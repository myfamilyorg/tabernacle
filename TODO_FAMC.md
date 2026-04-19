# TODO: famc

Consolidated list of proposed changes to the self-hosted fam compiler
(`src/famc.fam3`) based on what we've learned writing ~800 LOC of
`full_node.fam` / `tabernacle.fam3` on top of it.

Things that are **already done** and were removed from earlier drafts:
`li` handles full 32-bit immediates with correct sign-extension
(`famc.fam3:2948-3044`); string literals with escapes
(`.ci/testfamc:1346-1366`); structs, local arrays, macros, `rept`,
self-recursion, per-line error reporting, up to 8 fn args.

---

## P1 — Forward function declarations

**Gap.** `ct_fn_call` (`famc.fam3:11605-11633`) does a direct lookup;
callee must be defined **earlier in the source** than caller.
Self-recursion works because the fn name is bound before its body
compiles, but mutual recursion is impossible and file concatenation
order matters (the current `cat src/full_node.fam src/init.fam` rule
exists because `_bootstrap` in init.fam calls `main` in full_node.fam —
flip the order and the build breaks).

**Fix.** Two-pass compile:

1. First pass: collect all top-level `fn NAME(args)` signatures into the
   function symtab. No body codegen.
2. Second pass: emit fn bodies; calls resolve against the pre-populated
   table.

Alternatively a declaration-only syntax `fn name(args);` that forward-
declares — cheaper to implement, less clean to use.

**Effort:** medium. Needs source stream rewind or a buffered parse
front-end.

---

## ~~P2 — Constants visible in fn bodies~~ ✓ DONE

Implemented `const NAME = EXPR;` — compile-time constant definitions.
Values are substituted as literals at every use site (preprocessor model,
no runtime storage). Supports arithmetic expressions with `+ - * << >> & | ^ ~ ()`,
hex/decimal literals, and references to previously-defined consts. Both
`lookup` and `lookup_or_alloc` scan below `fn_scope_base` for `is_const=2`
entries so consts are visible inside fn bodies. 21 tests added.

---

## P3 — Array sizes should accept expressions, not just literals

**Gap.** `@arr[16384 + 4095]` silently parses as an array **access** of
an undefined variable rather than a declaration, because famc only
accepts integer literals for `LIT` in `@IDENT[LIT]`. Tested:
`.ci/testfamc:1153-1155`. Caused a miscompile ("full_node.fam:262:3
undefined variable" → captured as binary) that took a while to find,
because the error message doesn't hint at the real cause.

**Fix.** Accept constant expressions — anything evaluable at compile
time — for array sizes. With P3's `const` form in place, the natural
idiom becomes:

```
const SCRATCH_SIZE = 16384 + 4095;
fn f() { @scratch[SCRATCH_SIZE]; ... }
```

Basic arithmetic (`+ - * / << >> & | ~`) plus references to
previously-defined `const` names is enough; no variables, no function
calls. A small recursive-descent evaluator over the same token stream.

**Stretch:** runtime-sized arrays (`fn f(n) { @buf[n]; ... }`) would
also be useful (VLA-style), but they require dynamic frame adjustment
in the fn prologue and are a bigger change. Compile-time expressions
first; runtime later if the need becomes concrete.

**Effort:** small for compile-time expressions; medium for the VLA
stretch.

---

## P4 — Array alignment directive (nice-to-have)

**Gap.** Page-aligned regions for virtio `QUEUE_PFN` require the
over-allocate-and-mask pattern:

```
@region[49152 + 4095];
region = (region + 4095) & 0xFFFFF000;
```

Both approaches over-allocate identically to guarantee alignment, so
there's no space saving — but the manual mask is boilerplate that
readers have to pattern-match. A direct alignment declaration would be
cleaner:

```
@region[49152] align 4096;
```

**Fix.** Add an `align N` suffix to array declarations. Frame layout
bumps the offset to the next multiple of N before placing the array.

**Effort:** small. One parser extension, one frame-offset adjustment.


---

## P5 — Block-level variable scoping (currently fn-level)

**Gap.** Variable bindings are scoped to the **enclosing function**, not
to the nearest `{}`. Consequence: two sibling branches that each do
`sent = foo(...)` both refer to the same implicitly-promoted binding,
and the second one hits `Error: cannot reassign immutable` unless the
first was written with `:=`.

Confirmed empirically:
```
y > 0 ? { x = 65; @0x10000000 = x; }
      : { x = 66; @0x10000000 = x; };      // Error: cannot reassign immutable
y > 0 ? { x := 65; @0x10000000 = x; }
      : { x := 66; @0x10000000 = x; };     // OK — each branch gets its own local
```

In real code this surfaced when the RX-dispatch loop in `serve()` had
two ternary branches, one for ARP and one for IPv4, each wanting its
own `sent` count. With fn-scoped `=`, the IPv4 branch can't redeclare
`sent`; `:=` is required even though the two bindings are disjoint in
lifetime.

**Fix.** Make `=` (and `:=`) scope to the nearest enclosing `{}`. A
binding introduced inside a branch goes out of scope at `}`, so a
sibling branch is free to use the same name.

**Effort:** medium. Symbol-table changes plus care around the block /
fn-body boundary (fn params and the fn's outermost frame stay as they
are).

---

## P6 — Optional `;` after `loop` / `for` bodies

**Gap.** In some statement positions, a trailing `;` is required after
`loop { ... }` / `for ... { ... }` even though the braces are already
unambiguous block delimiters. Ends up looking like:

```
loop {
    @(UART + 5) & 0x20 ? break;
};                               // this ; shouldn't be required
scratch = (scratch + 4095) & 0xFFFFF000;
```

Fine when the rule is consistent, but fn bodies don't need the trailing
`;` after a final `}` (see fn-body tests in `.ci/testfamc`), so the
inconsistency catches you out when refactoring between the two
contexts.

**Fix.** Treat the closing `}` of `loop` / `for` as a statement
terminator in any statement position, same as a fn body. `;` stays
accepted for the cases where a chain of expressions really does want
it, but is not required to separate a braced block from the next
statement.

**Effort:** small. Statement-level parser tweak.

---

## P7 — Single-expression body for `loop` / `for` (no braces required)

**Gap.** `loop` and `for` always require a braced block even when the
body is a single expression. Minor papercut but it forces noise around
one-liner control flow:

```
loop { x > y ? break : { x++; y--; }; };
```

The outer `{ }` adds nothing — `loop` already terminates at the end of
its expression body.

**Fix.** Accept `loop <expr>;` and `for IDENT in RANGE <expr>;` as
valid single-statement forms, with braces still allowed for multi-line
bodies. Same rule Rust / Python / many modern languages use.

```
loop x > y ? break : { x++; y--; };
for i in 0..N @arr[i] = 0;
```

**Effort:** small. Parser tweak at the loop/for production.

---

## P8 — Comma operator

**Gap.** fam has no way to sequence side-effecting expressions inside a
place where a single expression is required (ternary branch, fn arg,
assignment RHS, etc.). Current workaround is a braced block:

```
x ? { a = 1; b = 2; c = 3; } : 0;
```

**Fix.** C-style comma operator: `e1, e2, e3` evaluates each in order
and yields the value of the last. Then:

```
x ? (a = 1, b = 2, c = 3) : 0;
```

Fits naturally alongside the existing ternary / block-expression idiom
and reduces `{ }` noise in one-liner branches.

**Effort:** small. New binary operator with the lowest precedence;
produces the RHS as its value.

---

## Not on the list

- **Stack-guard enforcement in allocators** — solved in
  `full_node.fam` `alloc` / `alloc_page` with a runtime s1-bump check
  that calls `heap_guard()` (emit OOM, shutdown). Not a famc concern.
- **Per-field width sigils in structs** (mixed u8/u16/u32 layouts).
  Considered but **rejected**: the only places that actually need
  bit-exact layouts are hardware-interop (virtio desc, eth/IP/UDP/ARP
  headers), a handful of self-contained sites. For those, the existing
  `*(ptr + N)` / `#(ptr + N)` byte-offset pattern reads 1:1 against the
  hardware spec and is easier to audit than a synthetic struct would
  be. Everywhere else, storing a "byte" or "bool" value in a u32 slot
  is semantically fine and costs nothing that matters.
- **Better asm-fn interop / "naked" fns** — deferred. The `asm { (var
  = reg) }` boundary is clunky but serviceable.
- **Structs / arrays / strings / `li` / recursion / error line:col** —
  already implemented. Removed from early drafts after reading
  `.ci/testfamc` properly.
