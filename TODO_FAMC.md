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

## ~~P5 — Block-level variable scoping (currently fn-level)~~ ✓ DONE

Implemented block-level scoping: `ct_lbrace` saves the symtab write
pointer (s8) as a byte offset on the stack; `ct_blk_end` restores it,
so all bindings introduced inside `{ }` go out of scope at `}`. Sibling
blocks can freely reuse the same name with plain `=`. Inner blocks can
still read/write outer-scope variables via `:=`. 11 tests added (5
block-scoping + 6 const-scoping). Also fixed deref-write context: `@`
prefix now forces read context at `pk_non_ws`, preventing `@UNDEF = v`
from silently creating a new variable.

---

## ~~P6 — Optional `;` after `loop` / `for` bodies~~ ✓ DONE

The top-level statement parser (`compile_stmt`) already checked
`last_was_brace` and made `;` optional. The bug was in the block-
expression separator (`sw_ct_blk_sep`), which required `;` or `}`
with no `last_was_brace` fallback. Added that check so `loop { }`,
`for { }`, `asm { }`, and plain `{ }` blocks inside fn bodies and
nested blocks no longer need a trailing `;` before the next statement.
4 tests added.

---

## ~~P7 — Single-expression body for `loop` / `for` (no braces required)~~ ✓ DONE

Removed the `{` requirement from both `sw_ct_loop_lbrace` and
`sw_ct_for_lbrace`. The body is now compiled via `compile_expr_p`
directly — if the next token is `{`, it enters `ct_lbrace` (block);
otherwise it parses a single expression. Braces still work for multi-
statement bodies. 6 tests added.

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
