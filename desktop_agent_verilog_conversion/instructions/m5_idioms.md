# M5 Idioms Used by the Conversions

Read this for the tasks Define M5 Configurations, Configure Using M5, TLV Macro, Combine Repeated Logic, and Inline Child Macros. It covers the M5 constructs the converted files depend on, with the exact syntax, one real example each, and what goes wrong when the construct is misused. Several of these constructs appear in no official document; the last section lists which.

Examples are quoted verbatim from real files. `warp-v.tlv` is github.com/stevehoover/warp-v, `pipeflow_lib.tlv` is github.com/stevehoover/tlv_flow_lib, and `serv_immdec/wip.tlv`, `serv_rf_ram_if/wip.tlv` are completed SERV conversions produced by this flow. Line numbers refer to those files.

## `m5_if_eq_block(String1, String2, TrueBlock [, String1b, String2b, TrueBlockb ...] [, ElseBlock])`

Conditional inclusion of a multi-line block of TLV or Verilog text. This is the construct every M5 configuration in the SERV conversions uses. Compare `String1` to `String2` as text; emit `TrueBlock` when equal, otherwise test the next pair, otherwise emit `ElseBlock` if given.

Write each block as `['`, newline, body lines, newline, `'])` (or `'], ['` before an else block). Put the body lines at the same indentation as the `m5_if_eq_block(` line; the output lines land where the source lines were, so line numbers stay aligned between `wip.tlv` and the generated Verilog.

Two-branch form (`serv_rf_ram_if/wip.tlv:22`):

```
         m5_if_eq_block(m5_cond_ratio_2, 1, ['
         $wtrig1 = $wcnt[0];
         '], ['
         $wtrig1 = $wtrig0_r;
         '])
```

Empty true branch with an else (`serv_rf_ram_if/wip.tlv:41`):

```
         m5_if_eq_block(m5_cond_ratio_2, 1, [''], ['
         <<1$wtrig0_r = $wtrig0;
         '])
```

Chained pairs with a final else (`warp-v.tlv:5668`):

```
         m5_if_eq_block(m5_FORMAL, 1, [''], m5_IMEM_STYLE, EXTERN, [''], ['
```

Nesting is fine: `serv_immdec/wip.tlv:86` opens `m5_if_eq_block(m5_cond_w_1, 1, ['` and line 89 opens `m5_if_eq_block(m5_cond_shared, 1, ['` inside it, each closed by its own `'])`. Blocks may contain `m5+` macro calls and TLV scope lines. Two calls may be glued on one line so no blank line separates the arms of a ternary: `'])m5_if_eq_block(m5_EXT_F, 1, ['` (`warp-v.tlv:1931`).

Failure modes:

- Comparison is textual after elaboration. `m5_if_eq_block(m5_cond_w_1, 1 , ...)` never matches because the trailing space is part of the argument (see Quoting).
- A `']` inside the body ends the block early; the rest of the body is elaborated as M5 arguments and the error surfaces at the closing `'])`, or at the end of the file, not at the offending line.
- The condition variable must exist. An undefined `m5_cond_x` prints `Error: Getting value of undefined variable "cond_x"` and the block silently takes the else arm. Define every knob with `default_var` (below).
- Whether `m5_if_eq_block` sets `$status` is not documented. Do not follow it with `m5_else(...)`; write the else block as the last argument instead.

## `m5_if_eq(...)` and `m5_if(...)` within a line

Same argument pattern as `m5_if_eq_block`, but the bodies are single-line quoted text and the call stays inside one TLV line (`warp-v.tlv:4025`):

```
            m5_if_eq(m5_BRANCH_PRED, ['fallthrough'], [''], ['$pred_taken_branch = $pred_taken && $branch;'])
```

`m5_if(Cond, TrueBody [, FalseBody])` evaluates `Cond` as an arithmetic expression, non-zero is true (`warp-v.tlv:1211`):

```
   m5_if(m5_NUM_CORES > 1, ['m4_include_lib(['https://raw.githubusercontent.com/stevehoover/tlv_flow_lib/db17b2200d717b870a419613d2ab4445a1300152/pipeflow_lib.tlv'])'])
```

To put an `m5+` macro call under a condition, quote it inside `m5_if` or `m5_if_eq` (`warp-v.tlv:6581`):

```
   m5_if(m5_FORMAL, ['m5+formal()'])
```

Failure modes:

- A within-line body must produce no newline; a newline breaks the line tracking between source and generated code. Use `m5_if_eq_block` for anything multi-line.
- `m5_if(cond, m5+it())` without the quotes expands `m5+it()` while the arguments are elaborated, before the condition is tested. Always quote the body.

## `default_var` versus `var` versus `set`

Three ways to give a variable a value. Pick by who is allowed to override it.

- `default_var(Name, Value)`: define `Name` only if it is not already defined. An earlier definition wins, in particular one supplied on the command line with `--m5def Name=Value`. `warp-v.tlv:317` states the rule: `default_var(..) allows external definition to take precedence.` Example (`warp-v.tlv:321`):

  ```
     default_var(FORMAL, 0)  // Uncomment to test formal verification in Makerchip.
  ```

  Pairs may be listed together, with quoted `['# ...']` comment strings between them (`warp-v.tlv:334`). Inside a `\TLV` body write it with the prefix: `m5_default_var(IMEM_SIZE, 1024)` (`warp-v.tlv:1698`).
- `var(Name, Value)`: always declare, masking any outer or earlier definition (`warp-v.tlv:596`: `var(HAS_INDIRECT_JUMP, 0)`).
- `set(Name, Value)`: reassign a variable that already exists (M5 spec 4.3). Behavior on an undefined name is unspecified; declare first.

Use `default_var` for every configuration knob (`cond_*`) in a converted file. `fev.sh` supplies the knobs with `--m5def` from `config.json`; a file that says `var(cond_w_1, 1)` overrides that, every configuration elaborates to the same design, and FEV passes vacuously. A file with no default at all cannot be compiled standalone or included from a parent that does not define the knob. The completed macro files use exactly this (`serv_rf_ram_if_macro.tlv:6`):

```
   /Configuration knobs normally supplied by fev.sh (--m5def); defaults for
   /standalone compilation.
   default_var(cond_width_32, 0)
   default_var(cond_ratio_2, 0)
```

Failure mode to avoid: `m5_default` is not an M5 macro. A `\m5` region containing

```
   m5_default(SERV_CLEAR_RAM, 0)
   m5_var(cond_clear_ram, m5_SERV_CLEAR_RAM)
```

(`serv_rf_ram_rz/wip.tlv:6`) defines nothing. SandPiper prints `Error: Getting value of undefined variable "SERV_CLEAR_RAM".` on every run, still writes the `.sv`, and `fev.sh` still reports `All FEV runs successful`, so the error is easy to miss. `cond_clear_ram` is empty, and `m5_if_eq(m5_cond_clear_ram, 1, ...)` takes the else arm unless `--m5def SERV_CLEAR_RAM=1` happens to be given. The same run also warns `In M5 block, lines should not start with "m5_"`: inside a `\m5` region write `default_var(...)`, `var(...)`, without the `m5_` prefix.

## `m5+ifelse(...)` chaining with `\TLV` block arguments

A library macro that selects among `\TLV` code blocks passed as arguments. Argument pattern is the same as `m5_if_eq_block`: pairs of strings followed by a block, optionally a trailing else block. The blocks are written as `\TLV` lines indented exactly three spaces past the call, with the block body three more; the `, next, pair,` continuation line and the closing `)` also sit at the three-space indentation (`warp-v.tlv:1682`, abridged):

```
   m5+ifelse(m5_FORMAL, 1,
      \TLV
         // For formal
         ...
      , m5_IMEM_STYLE, SRAM,
      \TLV
         |fetch
            ...
      , m5_IMEM_STYLE, EXTERN,
      \TLV
         ...
      ,
      \TLV
         // Default to HARDCODED_ARRAY
         ...
      )
```

An empty block is `\TLV` followed directly by the `,` line (`warp-v.tlv:1797`):

```
      m5+ifelse(side_effects, RO,
         \TLV
         ,
         \TLV
            // Next value of the CSR.
```

`m5+ifelse` comes from a library; `warp-v.tlv:37` includes `fundamentals_lib.tlv` before using it. The SERV conversions use `m5_if_eq_block` instead, which needs no include. Prefer `m5_if_eq_block` unless the file already includes the library.

Failure modes: any continuation line not at exactly three spaces is parsed as a new TLV statement and the argument list is cut short; `\TLV` block arguments are implicitly quoted, so wrapping one in `['...']` puts literal quote characters into the code.

## `m5_makerchip_module`

Expands within a line, in an `\SV` region, to the Makerchip top-module header `module top(input wire clk, input wire reset, ...)` with `cyc_cnt`, `passed`, `failed`. Real use (`makerchip_examples/sin_cordic.tlv:21`):

```
   m5_makerchip_module
```

Older files use `m4_makerchip_module` (`makerchip_examples/serv.tlv:88`). A converted module declares its own `module <name>(...)` in `\SV`, so it must not use this macro: the result is a second module named `top` and a mismatched FEV top.

## `\TLV name(/_top, /_name, ...)` definition and `m5+name(...)` call

Define a multi-line macro as a region that begins a line, with the body indented three spaces (`serv_immdec/wip.tlv:8`):

```
\TLV serv_immdec(/_top)
   |default
      @0
```

Call it where a TLV statement could appear; the expansion is indented to the call (`serv_immdec/wip.tlv:209`):

```
   m5+serv_immdec(/top)
```

Parameter names keep the sigil of the thing they stand for and start with `_` after the sigil, so they can never collide with a real identifier (`pipeflow_lib.tlv:212`):

```
\TLV arb2(/_top, |_in1, @_in1, |_in2, @_in2, |_out, @_out, /_trans, $_reset1)
```

Conventions (Macro-Preprocessor User Guide, "TLV Macro Block Conventions"): `/_top` is the scope of the instantiation, so the body can reference signals there as `/_top$sig`; `/_name` is a unique hierarchy level the macro creates for its own declarations; `$_`, `|_`, `@_`, `#_` prefix pipesignals, pipelines, stages, and elaboration constants. Give every module macro at least `/_top` even when unused, and pass `/top` from the module wrapper. A macro that instantiates other macros passes its own `/_top` through: `m5+serv_rf_ram_if(/_top)` inside `\TLV serv_rf(/_top)`.

Substitution is textual and word-bounded. A parameter is replaced wherever its exact name appears not glued to another word character, comments included. A zero-argument call is written `m5+name()`. The macro must be defined earlier in the file (or in an included file) than its first call.

Failure modes: a parameter named `$in` rewrites every `$in` in the body; a body not indented under the `\TLV` line is dropped or attaches to the wrong region (check indentation after moving code into a macro); `m5+name(...)` before the definition leaves the call unexpanded.

## `m4_include_lib(['./file.tlv'])` and the `-f` upload for cloud SandPiper

Include another TLV file so its `\m5` definitions and `\TLV` macros become available. The included file is elaborated inline; its own main `\TLV`, `\SV`, and `\SV_plus` regions are discarded, so a child file's module wrapper does not leak into the parent. Put the include in an `\SV` region near the top, after `use(m5-1.0)`, and start a fresh region right after it:

```
\SV
   m4_include_lib(['./serv_rf_ram_if_macro.tlv'])
   m4_include_lib(['./serv_rf_ram_macro.tlv'])
```

(`serv_rf_step6_include.tlv:8`). The remote URL form is `m4_include_lib(['https://raw.githubusercontent.com/.../<commit>/fundamentals_lib.tlv'])` (`warp-v.tlv:37`); pin a commit, never a branch.

The flow compiles with `sandpiper-saas`, a cloud client. It uploads only the `-i` file unless every included file is also listed with `-f`. The client zips each `-f` file under its basename (`sandpiper-saas` 1.1.0, `sandpiper/__init__.py`: `zip_file.writestr(Path(f).name, ...)`), so on the server all files sit in one directory. Therefore the include path in the `.tlv` is always `./<basename>` regardless of where the file lives locally, and two includes with the same basename collide. The working invocation for the two-leaf SERV register file was:

```
sandpiper-saas -i wip.tlv -o wip_WIDTH_8.sv \
  -f ./serv_rf_ram_if_macro.tlv ./serv_rf_ram_macro.tlv \
  --m5def cond_width_32=0 --m5def cond_ratio_2=0 --inlineGen --noline --iArgs
```

`fev.sh` has no include-file option; it splices the `M5_configs` string from `config.json` verbatim into that command, so put the `-f ...` list in each configuration's string. Local SandPiper (`--m5inc`) resolves includes below the current directory instead and does not need `-f`.

Failure modes: a missing `-f` gives a "file not found" style error from the server for the include; an include placed inside a `\m5` region emits text into a region that discards it (wrap in `nullify(...)` there, as `warp-v.tlv:533` does); an include after the first `m5+` use of its macro leaves that call unexpanded.

## `['']` as a word delimiter

Substitution of a `\TLV` parameter or an `m5_` variable needs a word boundary on both sides. Insert the empty quote `['']` to create one (`warp-v.tlv:1788`, parameter `csr_name`):

```
            $csr_['']csr_name['']_hw_wr_en_mask[m5_THIS_CSR_RANGE] = ...
```

Without it, `$csr_csr_name_hw_wr_en_mask` contains no standalone `csr_name` (`_` is a word character) and nothing is substituted. The same trick lets a variable follow a word: `Index['']m5_Index`. The shorthand `\m5_Index` is equivalent (`warp-v.tlv:1943`: `m5_WORD_CNT'b0\m5_eval(...)`).

## The three-space continuation rule

An `m5+` call may span lines. Arguments may start on the first line; every following line is indented exactly three spaces past the `m5+` line; the closing `)` follows the last argument immediately on the same line. `\TLV` block arguments, their separating `,` lines, and the final `)` all sit at that three-space indentation, with the block body three spaces deeper. See the `m5+ifelse` example above.

Failure modes: a continuation line at any other indentation is read as a new TLV statement and the call sees a truncated argument list; a `)` on its own line puts the newline and its indentation into the last argument. Comments are not allowed inside an argument list.

## Six quoting rules

M5 quotes are `['` and `']`. Quoted text is passed through unchanged, minus the outer quotes; one level is removed per elaboration.

1. Trailing whitespace is part of an argument; leading whitespace is not (M5 spec 4.6). `m5_foo( A , B )` yields `A ` and `B `. Never put a space before a `,` or `)` in a comparison argument.
2. `//` is not an M5 comment (spec 5.1.2). `// m5_if_eq_block(...)` still runs. Disable M5 code with `///` (line comment anywhere) or a leading `/` on a statement line inside `\m5`.
3. `m5_foo()` passes one empty argument, not zero (spec 4.6). It is fine for `\TLV` block calls, `m5+foo()`, and for `fn`s with no parameters; a function with one required parameter receives an empty string instead of an error.
4. Commas need quoting. `m5_x(cond, {a, b})` passes three arguments. Quote any argument containing a comma or an unbalanced parenthesis: `['{a, b}']`. A list passed as one argument is quoted at the call, `m4+flow_interface(/_top, [' |_in_pipe, @_in_at'], ...)` (`pipeflow_lib.tlv:626`), and re-quoted when forwarded, `m4+flow_inputs(/_top, ['_ins'], $_reset1)` (`pipeflow_lib.tlv:116`).
5. Quotes must balance across the whole file after comment stripping (spec 5.7.2). One stray `['` or `']` shifts every later quote level, and the error is reported at the end of the region or file, far from the cause. Verilog `'` characters are safe inside quotes (`['1'b0']`); only the two-character sequences `['` and `']` matter. Keep each `['` and `']` on the same line except in a deliberate `m5_if_eq_block` body.
6. `$1`, `$2`, `$@` inside a macro body bind to the outermost definition being elaborated (spec 4.4, CAUTION). A `macro(...)` declared inside another macro's body has its `$1` replaced by the outer macro's argument at the outer call. Use numbered parameters only in top-level `macro(...)` bodies such as `macro(imm_reg, ['<<1$1 = ... $wb_rdt[$3] ...'])`; inside nested definitions use `fn` with named parameters. `$` followed by a letter is ordinary text, so `$wb_en` needs no escaping, and `\$` is wrong (the backslash reaches SandPiper and fails PARSE-IDENT).

## Not in the official PDFs

Checked against the text of the M5 Text Processing Language User's Guide (v2.0, 2024) and the TL-Verilog Macro-Preprocessor User Guide (draft, Nov 2022). Neither document contains:

- `m5_if_eq_block` (0 mentions in either), including its argument pattern, the body-at-call-indentation convention, and how it strips the leading and trailing newline.
- `default_var` and `m5_default_var` (0 mentions). The spec's library index lists `var`, `vars`, `set`, `push_var`, not `default_var`.
- `m5+ifelse` with `\TLV` block arguments (0 mentions; the guide's `simple_if` example is a hand-written stand-in for it).
- `m5_if_def_tlv(name, then, else)` and the block-call form `m5+call(m5_name)` (`warp-v.tlv:6573`, `:6575`).
- The local-file form `m4_include_lib(['./file.tlv'])`, the cloud `-f` upload requirement, and the basename flattening. The guide documents only the URL form.
- The `m5_default` trap: the name does not exist, SandPiper reports the missing variable but exits successfully, and the knob reads as empty.
- `m5_makerchip_module` is named once in the guide's file-structure example with the comment "Standard module interface for Makerchip" and is not described anywhere.
- `use(m5-1.0)`: the guide's example says `use(m5-0.1)`; every real file uses `use(m5-1.0)`.

The remaining items above are documented and cited here because workers get them wrong: `m5_if_eq` and `m5_if` (spec 7.3.2), `\TLV` blocks, `m5+` calls, `/_top` and `/_name` (guide, "Multiline TLV Macro Blocks" and "TLV Macro Block Conventions"), the `['']` delimiter (guide, "TLV Macro Block Declarations"), the three-space rule (guide, "m5+ Calls That Span Multiple Lines" and "\TLV Block Arguments and Parameters"), and the six quoting rules (spec 4.4, 4.6, 5.1.2, 5.7.2).
