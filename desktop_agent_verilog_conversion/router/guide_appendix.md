
# TL-Verilog Quick Reference (condensed)

- Every expression lives in a pipestage: `|pipe @N` (hierarchy scopes like
  `/core[2:0]` may wrap them). Code in a `\TLV` region is indented 3 spaces;
  whitespace and indentation are significant.
- Pipesignals are never declared; a `$sig` exists by being assigned exactly
  once. Single-bit assignments take no range on the left-hand side.
- References start from a common ancestor scope: `$sig` (same scope),
  `/child$sig`, `/common/scope$sig`, cross-pipeline `|pipe/scope>>N$sig`.
- Alignment: `>>N` reads a signal N stages ahead in the referencing context
  (as sampled now, this is the value from N cycles earlier); `<<N` the
  reverse; `<>0` is naturally aligned.
- State, two equivalent styles for a registered value; both express the same
  flop, do not mix them for one signal:
  1. next-value assignment: `<<1$cnt[15:0] = $reset ? '0 : $cnt + 1;`
  2. combinational producer + delayed consumer: `$rz = expr;` with the
     consumer reading `>>1$rz` for the previous-cycle value.
- When scope `?$valid` gates contained assignments (don't-care when
  deasserted); never functionally required.
- Lexical reentrance: statements are declarative, order-free; a scope can be
  reentered later in the file (`/scope[*]`) to add logic.
- `\SV_plus` embeds Verilog (always blocks, module/function instantiation)
  inside `\TLV`. Pipesignals may be read there; a pipesignal ASSIGNED there
  must be written `$$sig` with an explicit bit range in exactly one place.
  Escape `$` in Verilog system tasks as `\$display`.
- Memory arrays are unnatural as pipesignals; keep arrays and their
  read/write always blocks in Verilog (`\SV_plus`).
- Files starting `\m5_TLV_version` use M5 macro preprocessing; `\TLV name(...)`
  defines reusable macros; use `m5_calc(...)` for computed ranges.
- Assignments must be placed within the assigned signal's scope (references
  can cross scopes; assignments cannot).
