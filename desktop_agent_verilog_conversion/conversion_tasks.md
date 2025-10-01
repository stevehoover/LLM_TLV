# Tasks for LLM-assisted Verilog to TL-Verilog Code Conversion

These tasks define a process for converting Verilog to TL-Verilog. An overview of the conversion process should have been provided in this Project/GPT's instructions.

## Task: Preparation

Summary: Prepare the initial code, tracker, status, and FEV configurations to begin conversion.

### Continuation

If asked to continue a conversion that has already been started, `cd` to the given working directory for the conversion, and assess the current progress in `status.md` and `tracker.md` as well as reviewing the current code. Skip ahead to the appropriate task using `./scripts/get_task.py '<task-title>'` to continue the work in progress.

### `prep.sh`

When starting fresh, a script `desktop_agent_verilog_conversion/prep.sh` assists you in initializing the conversion directory. The user should have provided you with a directory path and a Verilog file path to use for the conversion. Search the Verilog file to find its module name (perhaps `grep module <orig.sv>`), then run `.../prep.sh <directory> <verilog-file> <module_name>` to safely create and initialize `<directory>` with:

- `prepared.sv`, `wip.tlv`, and `feved.tlv`: as copies of <verilog-file>
- `tracker.md`: Some initial empty categories (which you may change as appropriate).
- `status.json`: to contain: `{"task": "Preparation", "fev.sh": "none", "llm": ""}
- `fev.eqy` and `fev_full.eqy`: based on the template `fev.eqy` in `desktop_agent_verilog_conversion/`.
- `scripts/`: as a link to the `desktop_agent_verilog_conversion/` directory containing all helper scripts (e.g. `fev.sh` and `get_task.py`).

Then `cd` to <directory>. Consider the remaining instructions for this task, and, as you do, update `prepared.sv`, `tracker.md`, and `status.json`.

### Single File

The MCP tools require the top-level module definition to be encapsulated in a single file. This includes any submodules, functions, and macro definitions that might be instantiated by the module. If any other files are needed, either find them and inline the needed content, or record the issue and stop to give the user a chance to assess the situation.

### Latch-based Design

It is expected that the original design is flip-flop-based, triggered by the rising edge of the clock. If logic is driven by the falling edge of the clock, it may be converted to transition a phase earlier or later as long as the output timing is preserved for FEV. Any changes like this that may impact the nature of the physical implementation should be noted in `tracker.md`.

### Clock Gating/Enabling

Clock gating logic can be difficult to convert. TL-Verilog logic infers flip-flops and does not have direct control over the application of clock to them. TL-Verilog supports fine-grained clock gating or enables using "when conditions", e.g., `?$valid`. This can be used to create clock gating that matches the original, but it may result in awkward code.

There is a distinction between functional and non-functional clock gating/enabling. In functional gating/enabling the gating is functionally required. In non-functional clock gating, the gating condition is functionally a DONT-CARE. If we know the gating to be non-functional, we have more flexibility in the conversion.

If the module has functional or non-functional clock gating/enable inputs, assume the input to be DONT-CARE (1'bX) if it is known to be non-functional. Comment on the use of clock gating or clock enabling in the original code and any modification to the code.

### Prepare the Code

Make sure you are in the established working directory for this conversion. Prepare `prepared.sv` as instructed above if needed. If any modifications are necessary from the given code or issues are found, report them in `tracker.md` and to the user. This establishes the baseline code that you will convert. Henceforth, all modifications MUST PASS FEV. If you made changes to `prepared.sv`, copy `prepared.sv` to `wip.tlv` and `feved.tlv`. Run `fev.sh` for this task as well. It should pass since there are no changes, but this will catch any script and setup errors before you begin refactoring.


## Task: Signal Matching

Add to the `[match ...]` section of `fev_full.eqy` a match line for every internal signal (not module interface signals) in the `wip.tlv` module. The section should look like:

```
[match <module>]
gold-match foo foo
gold-match bar bar
```

`fev.sh` will update this as you proceed.

Even though there is no update to `wip.tlv` for this step, run `fev.sh` anyway to checkpoint your work in `history/`.


## Task: Parameters

If the module has any parameters, additional FEV configurations can be established for alternate parameter sets. `fev.sh` will test each parameter set, each defined by a `fev_full_*.eqy` file.

Examine the use of parameters in `prepared.sv` to determine a set of parameter sets to adequately test future refactoring steps. Make sure key generate scenarios are covered. Parameters should be chosen impact generate `if` conditions. Generate `for`s should be tested with no iterations, one iteration, and multiple iterations if possible. Avoid large parameter values to avoid large FEV runs, and keep the set minimal, but sufficient.

Create a corresponding `fev_full_*.eqy`, e.g. `fev_full_WIDTH_4_BYPASS_1.eqy`, for each parameter set. Create each as a copy of `fev_full.eqy`, uncommenting the line `#chparam -set ...` and updating it with one `-set <PARAMETER_NAME> <VALUE>` for each overridden parameter.

Describe the parameter sets in `tracker.md`.

Even though there is no update to `wip.tlv` for this step, run `fev.sh` anyway to checkpoint your work in `history/`.


## Task: Reset and Clock

Summary: Ensure proper clock and reset signals (if needed).

TL-Verilog works with a global (free-running) clock, called `clk`. If the Verilog code uses a clock by a different name, assign it to a new `clk` signal, and update the code to use `clk` instead. A module that is purely combinational may not have a clock, and this is okay. Just be aware that if any sequential logic is defined using TL-Verilog, SandPiper will assume a `clk` exists.

TL-Verilog code conventionally uses a positively-asserted synchronous reset signal, called `reset`, and FEV configurations may assume this name (not currently true, but we'll prepare for this in any case). If the module has a reset input, analyze the logic to determine its assertion level and whether it is synchronous or asynchronous. It's name and/or code comments may also be revealing. If there is no reset signal, none is needed, and this task is complete.

If there are any asynchronous uses of reset, the following changes will be needed that impact functionality and cannot be FEVed. At this point, that's okay. `feved.tlv` and `wip.tlv` should be unchanged from `prepared.sv`. Double check to be sure. If the reset input is called `reset`, change its name in `prepared.sh` to `areset` (or `aresetn` if negatively asserted). Modify `prepared.sv` to synchronize the asynchronous reset using two flip-flops as a synchronizer, producing `reset` or `resetn`. Further update `prepared.sv` to use this new reset synchronously. Copy changes to `feved.tlv` and `wip.tlv`. Update `tracker.md` to highlight these unFEVed changes in `prepared.sv`.

If the input reset signal is negatively asserted, create a positively-asserted reset. This can be done in `wip.tlv` as it will not impact behavior. Call this positively-asserted reset `reset`. Update all uses of the old reset to use this new one.


## Task: TLV File Format

Summary: Format the file as a TL-Verilog file with module contents in an `SV_plus` block.

Convert the code to TLV file format. The code can all be in one big `\SV` region initially, so this can be as simple as prepending these two lines:

```tlv
\TLV_version 1d: tl-x.org
\SV
```

Next, put the top module body in `\SV_plus` context, where the use of TL-Verilog pipesignals is permitted. Move it into an `\SV_plus` block in stage 0 (`@0`) of a "default" pipeline (`|default`). So:

```tlv
\TLV_version 1d: tl-x.org
\SV
module(...);
<module-body>
endmodule
```

becomes:

```tlv
\TLV_version 1d: tl-x.org
\SV
module(...);
\TLV
   |default
      @0
         \SV_plus
            <module-body>
\SV
endmodule
```

Be sure to use three spaces of indentation for each scope and within the `\SV_plus` block. Indent `|default` 3 spaces, `@0` 6 spaces, `\SV_plus` 9 spaces, and the entire module body 12 spaces (plus its own internal indentation).

Code in an `\SV_plus` block is parsed for TLV identifiers. At this point, we should have no TLV identifiers, so we must avoid all syntax that could be mistaken as a TLV identifier. Identifiers begin with one or more symbol characters and are followed immediately by word characters.

The first change you can make to reduce the likelihood of false matches also establishes consistent coding conventions. Make sure all Verilog operators (unary, binary, and ternary) have whitespace separating them from any neighboring word characters. For `=` and `<=` assignment operators only, also ensure whitespace separation for neighboring non-word characters. Most Verilog coding guidelines would not suggest whitespace after unary operators like `!`, `~`, `|`, `&`, and `^`. Be sure to catch these.

Next, some valid Verilog syntax, such as `$display`, `%s`, and `@10` requires word characters immediately following symbol characters, and we need to ensure that these valid Verilog strings are not interpreted as TL-Verilog syntax. The `\` escape character can be used for this purpose within `\SV_plus` context. `\` ensures that the next character is treated as a literal Verilog character, so `$display`, `%s`, and `@10` must become `\$display`, `\%s`, and `\@10`. Symbols of concern are  `$`, `@`, `|`, `/`, `#`, `%`, and `\`. Only symbol characters that immediately precede word characters need escaping. This doesn't tend to occur often in practice and is most common in test bench and logging code. (Our module shouldn't contain test bench code.)

Note that these `\`s will carry over into `\TLV` assignment expressions, which also use Verilog syntax.

Before testing, double-check your indentation (3 spaces for each scope; no tabs). The whole <module-body> must be indented properly. This often trips you up.

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Signal Naming

Summary: Update the Verilog signals to conform to TL-Verilog naming convensions.

In preparation for converting Verilog signals to TL-Verilog pipesignals, rename Verilog signals to names that will be legal pipesignal names. (We will not use TLV state signals, only pipesignals.) Pipesignal names are limited to using lowercase ASCII letters, digits, and underscores. They are comprised of "tokens", that are separated by `_`. Each token is a string of 1 or more letters, followed by zero or more digits. The first token must begin with at least two letters. This is only a consideration for the first token, not the rest.

So:

- Rule 1: lower-case ASCII word characters only
- Rule 2: tokens (separated by `_`) must be one or more letters optionally followed by any number of digits
- Rule 3: the first token must begin with two or more letters

Example name mappings:

- `CSR` -> `csr`  # Rule 1
- `sig_1` -> `sig1`  # Rule 2
- `wide2narrow` -> `wide_to_narrow`  # Rule 2
- `a` -> `aa`  # Rule 3
- `x_y` -> `xx_y`  # Rule 3
- `product_1_NRE` -> `product1_nre`  # Rule 1 & Rule 2
- `Opcode_0b01011` -> `opcode01011`  # Rule 1 & Rule 2
- `is_VERSION_1_0` -> `is_version1_dot0`  # Rule 1 & Rule 2
- `regA_EXE_2` -> `reg_a_exe2`  # Rule 1 & Rule 2
- `no_change` -> `no_change`
- `this1_is_o_k` -> `this1_is_o_k`

First, convert internal signals (not module interface signals). Conveniently, these singals are listed in the `[match ...]` section of `fev_full.eqy`. Update this section with corrected "gate" names, then make the corresponding corrections in `wip.tlv`.

```
[match <module-name>]
x_len xx_len
```

Then convert interface signals as necessary. These require special consideration. The interface signals themselves must not be changed. So, in `wip.tlv`, create intermediate internal signals with the updated names. For inputs, declare and assign (using `assign`) the new signals toward the top of the module logic. Declare and assign new signals for outputs toward the bottom. Since these signals do not exist in the original code, there is no need to reflect them in `fev.eqy`.

Apply these conventions to `genvar`s as well.

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Signals to Pipesignals

Summary: Convert from using Verilog signals to using TL-Verilog pipesignals (boolean and bit-vector signals only).

In this task, you'll convert Verilog signals to TL-Verilog pipesignals. Convert only internal signals defined and assigned within the `\SV_plus` block. Do not convert module interface signals nor `clk`.

To SandPiper, the `\SV_plus` block is a giant assignment statement with a multitude of assigned pipesignals and a multitude of used pipesignals. SandPiper does not parse the Verilog syntax, and requires explicit syntax to identify which pipesignals are assigned by the block. One occurrence of each assigned pipesignal must identify the pipesignal as being assigned by the block by using a `$$` prefix. This occurrence also provides the bit range of the pipesignal.

To be clear, there is no need to use TL-Verilog's alignment operator, e.g., `<<1`, in this task. You will not rely on SandPiper to generate any flip-flops. Though TL-Verilog logic generally implies the flip-flops, for this task, the Verilog non-blocking assignments are still in place to provide them. So the conversion of register signals to pipesignals does not require any special consideration for timing.

Each signal can be converted independently of the others.

Begin by converting the Verilog signals defined at the top-level (not within a generate block), limiting yourself to those that are simple boolean and bit vector signals. These are converted as follows:

- Add a `$` prefix to the name everywhere.
- For the first assignment of the pipesignal, apply a `$$` prefix, and append the full bit range of the pipesignal after its name (unless it is boolean), e.g. `assign foo = ...` might become `assign $$foo[7:0] = ...`.
- Remove the Verilog signal declaration.

Note that non-blocking assignments are treated very similarly. `cnt <= reset ? 0 : cnt;` might become `$$cnt[31:0] <= reset ? 0 : $cnt;`. (This is actually a little goofy if you think about it. It's really `<<1$cnt`, the next value of count, that is assigned by a non-blocking assignment. But, SandPiper is unaware of the inherent delay in the non-blocking assignment. By NOT using `<<1` we compensate for this. To SandPiper, this looks like cyclic logic, and, fortunately, SandPiper doesn't currently complain about this.)

Constructs like `if` and `case` enclose multiple assignments of a signal. TL-Verilog uses single-assignment semantics, so these constructs are a bit awkward. In these cases, the first assignment should be used to indicate assignment (with `$$`) and define the signal's bit width. To SandPiper, other assignments can look like uses. This is weird, but it does no harm.

```tlv
   \SV_plus
      logic [WIDTH-1:0] cnt;
      always_ff @(posedge clk)
         if (reset)
            cnt <= 4'b0;
         else
            cnt <= cnt + 1;
```

becomes:

```tlv
   \SV_plus
      always_ff @(posedge clk)
      if (reset)
            $$cnt[WIDTH-1:0] <= 4'b0;
      else
            $cnt <= $cnt + 1;
```

A few things deserve clarification:

- Verilog expressions (elaboration-time constant) may be used for bit-range bounds, e.g. `$$foo[WIDTH-1:0] = ...;`.
- Concatenation on the left-hand side is fine, e.g. `assign {$$foo, $$bar[1:0]} = ...;`.

Signals with complex types (non-bit-vectors) or signed values require special consideration (in the next task). For this task, leave them as Verilog.

Replicated signals require special consideration and should be converted in a separate step. Most replicated signals are replicated by for loops with elaboration-time-constant bounds. Other scenarios are not considered here and may require user intervention.

A replicated signal may be assigned within a `generate for` loop or within a for loop within an `always` block. Those in generate for loops may be declared as arrays outside the loop and reference within the loop with an array index (often the loop index). Or signals may be declared within the loop and naturally replicated by the loop. Any of these scenarios is handled the same in TL-Verilog, and the corresponding pipesignal is referenced the same way. The pipesignal will exist in a replicated scope, e.g., `/loop[upper:lower]`. Upper and lower bounds must be elaboration-time constant and can be integers or Verilog expressions. The pipesignal reference within the loop will include the scope and its index, e.g. `/loop[ii]$foo`. For example:

```tlv
   |default
      @0
         \SV_plus
            logic [7:0] foo [4:0];
            logic [7:0] bar;
            genvar ii;
            for (ii = 0; ii < 4; ii++)
               assign foo[ii] = bar + ii;
```

when converting `foo`, becomes:

```tlv
\TLV
   |default
      @0
         /ii[3:0]
         \SV_plus
            logic [7:0] bar;
            genvar ii;
            for (ii = 0; ii < 4; ii++)
               assign /ii[ii]$$foo[7:0] = bar + ii;
```

Note that the scope (`/ii`) must be defined prior to the `/SV_plus` block.

Some (non-generate) loops might update the same signal in each iteration. These would generally, be termed "reduction" operations. One pattern for translating these is exemplified below:

```tlv
   |default
      @0
         \SV_plus
            logic [31:0] sum, addend[3:0];
            always_comb begin
               sum = 0;
               for (integer ii = 0; ii < 4; ii++)
                  sum = sum + addend[ii];
            end
```

Can be refactored to use explicit partial sums, as:
```tlv
   |default
      @0
         \SV_plus
            logic [31:0] sum, addend[3:0], partial[3:0];
            always_comb begin
               for (integer ii = 0; ii < 4; ii++)
                  partial[ii] = (ii == 0) ? 0 : partial[ii-1] + addend[ii];
               sum = partial[3];
            end
```

Some tools object to `partial[ii-1]` potentially indexing -1, which doesn't exist. In this case the value is unused, but, to make these tools happy, it may be necessary to use `partial[(ii+4-1)%4]` to keep the index in range.

From this, we can more easily refactor to pipesignals:

```tlv
\TLV
   |default
      @0
         /ii[3:0]
         \SV_plus
            always_comb begin
               for (integer ii = 0; ii < 4; ii++)
                  /ii[ii]$$partial[31:0] = (ii == 0) ? 0 : $partial[(ii+4-1)%4] + $addend[ii];
               $$sum[31:0] = $partial[3];
            end
```

[TODO: tackle this with Verilog signals earlier]
[TODO: split this task]

In Verilog, it is legal to assign different portions of a vector signal in separate assignments. This is not permitted in TL-Verilog. Likely, a combined assignment can be created by simply concatenating the expressions. If the individual assignments are complex, an intermediate signal can be introduced to hold the partial expression that is then concatenated. For example:

```tlv
   \SV_plus
      logic [31:0] addr;
      assign addr[31:12] = <complex_expression>;
      assign addr[11:0] = page_addr;
```

Is equivalent to:

```tlv
   \SV_plus
      logic [31:0] addr;
      logic [31:12] addr_b31_b12;
      assign addr_b31_b12 = <complex_expression>;
      assign addr = {addr_b31_b12, page_addr};
```

Which becomes:

```tlv
   \SV_plus
      assign $$addr_b31_b12[31:12] = <complex_expression>;
      assign $$addr[31:0] = {$addr_b31_b12, page_addr};
```

Update the `[match ...]` section of `fev.eqy` for these name changes, e.g:

```
[match <module-name>]
gold-match foo |default<>0$foo
```

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Non-vector Signals

Summary: Non-vector signal types are awkward in TL-Verilog; convert these to pipesignals.

Signals with complex types (non-bit-vectors) or signed values must use Verilog-defined types (or enums). A separate statement in a `\TLV` region is necessary to declare the pipesignal's type, using a `**` prefix on the type, as illustrated below.

For verilog `foo` in:

```tlv
\TLV
   |default
      @0
         \SV_plus
            typedef struct packed {
               logic [7:0] field1;
               logic [7:0] field2;
            } foo_t;
            ...
            foo_t foo;
            assign foo.field1 = $bar;
            assign foo.field2 = $baz;
```

the refactoring can be:

```tlv
\SV
   typedef struct packed {
      logic [7:0] field1;
      logic [7:0] field2;
   } foo_t;
...
\TLV
   |default
      @0
         **foo_t $foo;
         ...
         \SV_plus
            assign $$foo.field1 = $bar;
            assign $foo.field2 = $baz;
```

Verilog type `foo_t` would be defined in an `\SV` region or `\SV_plus` block.

Note that the multiple field assignments to `$foo` in this example will remain in an `\SV_plus` block throughout the conversions. These cannot be converted to native TLV assignments.

Here's another example using `foo_t`:

```tlv
\TLV
   **foo_t $blah;
   ...
   \SV_plus
      always_ff @(posedge clk)
         $blah <= reset ? '0 : $blah;
```

For signed signals, it is usually easier to convert them to normal pipesignals and use `\$signed(...)` where they are used instead of defining an unsigned type for them.

Update the `[match ...]` section of `fev.eqy` for these name changes, e.g:

After this task most if not all signals are probably converted to pipesignals. Other scenarios should be left as Verilog signals.

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: If/Else and Case to Ternary

Summary: `if`/`else`/`case` expressions are discouraged in TL-Verilog and are converted to ternary expressions.

This task should eliminate all signals with multiple assignments. These appear in `if`/`else` constructs and `case*` statements. These are assigned to different values under different conditions. TL-Verilog favors the use of ternary expressions for such assignments, because they follow single assignment semantics. (They also isolate the assignments of each signal, resulting in finer granularity assignments. Since assignments are the atomic unit of timing abstraction, this results in greater timing flexibility.)

`if`/`else`/`case` may not assign a signal in all cases. Ternary expressions do not allow this. These cases must retain the previous value explicitly in the ternary expression.

Let's look at some examples:

```tlv
   \SV_plus
      always_comb
         if ($cond)
            $yy = $bb;
         else
            $yy = $cc;
```

becomes:

```tlv
   \SV_plus
      always_comb
         $yy = $cond ? $bb : $cc;
```

Let's look at a more interesting example.

```tlv
   \SV_plus
      always_ff @(posedge clk) begin
         if ($valid) begin
            if ($cond1)
               $$yy <= $bb;
            else if ($cond2)
               $yy <= $cc;
            else begin
               $yy <= $dd;
               $$zz[7:0] <= $ee;
            end
         else
            $yy <= $ff;
         end
      end
```

Note that `$yy` is assigned under all conditions, but `$zz` is not and must be retained when not assigned.

This example can be transformed incrementally, first transforming the inner assignment of `$yy`:


```tlv
   \SV_plus
      always_ff @(posedge clk) begin
         if ($valid) begin
            $$yy <=
               $cond1 ? $bb :
               $cond2 ? $cc :
                        $dd;
            if ($cond1) begin
            end else ($cond2) begin
            end else
               $$zz[7:0] <= $ee;
         else
            $yy <= $ff;
         end
      end
```

Note that the empty conditions, above, are acceptable, but `begin`/`end` must be added.

Continuing to refactor `$yy` and `$zz`:

```tlv
   \SV_plus
      always_ff @(posedge clk) begin
         $$yy <=
            $valid ?
               $cond1 ? $bb :
               $cond2 ? $cc :
                        $dd :
            //default
               $ff;
      if ($valid && (! $cond1 && ! $cond2))
         $$zz[7:0] <= $ee;
      end
```

Then to refactor `$zz` to use a ternary expression, we must explicitly recirculate `$zz`.

```tlv
         $$zz[7:0] <= $valid && (! $cond1 && ! $cond2) ? $ee : $zz;
```

`case*` statements can be transformed similarly.

```tlv
   \SV_plus
      always_comb begin
         case ($sel)
            2'b00: $$yy[7:0] = 8'hAA;
            2'b11: $yy = 8'h55;
            default: $yy = 8'h00;
         endcase
      end
```

Results in:

```tlv
   \SV_plus
      assign $yy[7:0] =
           ($sel == 2'b00) ? 8'hAA :
           ($sel == 2'b11) ? 8'h55 :
                             8'h00;
```

Like `if`/`else` chains, `case` without `default` can infer latches and the resulting ternary expression must explicitly recirculate the value.

`unique case` implies exclusivity. The case conditions must be one-hot. They imply runtime checking and enable logic synthesis optimizations. To achieve this with ternary expressions, add assertions and runtime checking that exactly one of the conditions of the `unique case` is asserted.

For example:

```tlv
   \SV_plus
      always_comb begin
         unique case ($sel)
            2'b01: $$yy[7:0] = 8'hAA;
            2'b10: $yy = 8'h55;
         endcase
      end
```

```tlv
   \SV_plus
      $$yy[7:0] =
         ($sel === 2'b01) ? 8'hAA :
         ($sel === 2'b10) ? 8'h55 :
                              'x;  // impossible
      assert property (@(posedge clk) \$onehot($sel));
```

If you have trouble getting the assertion correct, make a note of the potential checking/synthesis implications in `tracker.md`.

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Migrate to TLV Expressions

Summary: Migrate Verilog-style expressions in `\SV_plus` block(s) to `\TLV`-style expressions.

### Entry Conditions

In this task, expressions from the `\SV_plus` block are pulled out as individual `\TLV` assignment expressions. All logic remain in `|default@0` for this task.

Unless you had difficulty in earlier tasks, all pipesignals should now have a single assignment, whether by an `assign` statements, in an `always_comb` block, or in an `always_ff` block. If earlier task seem incomplete, look back to ensure you are ready for this task.

### TLV Assignments

When refactored to `\TLV` context, all pipesignals will be assigned in `\TLV` context using a simple `=` assignment, and their `$$` will be dropped (for `$`). Verilog signals should be prefixed with `*`.

### Assigns

For `assign`s, in `\TLV` context, the `assign` keyword is dropped and the rest is unchanged. Note that concatenation is permitted on the left-hand side of a `\TLV` expression, e.g. `{$foo, $bar[1:0]} = ...;`.

Assignments within `always_comb` can be translated to `assign`s, then converted to `\TLV` syntax.

For example:

```tlv
   \SV_plus
      assign $$foo = $bar ^ i_data_in;
```

becomes:

```tlv
\TLV
   $foo = $bar ^ *i_data_in;
```

### Instantiations

Module, function, and macro instantiations may have signal parameters and may be pipesignals in `\SV_plus` context. These can be input or output signals (used or assigned). Those that are assigned, when converted to pipesignals, must use `$$` and an explicit bit range (for the first assignment in the `\SV_plus` block only).

### Non-Blocking Assignments

When migrating non-blocking assignments from `\SV_plus` to `\TLV`, the new assignment will use `=`, not `<=`. There is no longer an implicit flip-flop. To imply this flip-flop, prepend `<<1` to the assigned pipesignal, indicating that the assignment is to the pipesignal's *next* value (the value in the previous pipestage). Uses in the current stage will, thus, be after an implied staging flip-flop as desired.

For example:

```
   \SV_plus
      always_ff @(posedge clk)
         $$cnt[31:0] <= reset ? 0 : $cnt + 1;
```

```
\TLV
   <<1$cnt[31:0] = reset ? 0 : $cnt + 1;
```

Non-blocking assignments that use a conditioned clock (gated/enabled) can be converted using when conditions. A pipesignal must exist or be created for the condition. For example:

```
   \SV_plus
      wire gated_clk = clk & $en;
      always_ff @(posedge gated_clk)
         $$foo = $bar;
```

becomes:

```
   ?$en
      $foo = $bar;
```

### Replicated logic

Logic in `for` loops will need to be placed in the corresponding TLV scope. The loop's `genvar` is replaced with `#name`, where `name` is the name of the scope.

For example:

```tlv
\TLV
   /ii[3:0]
   \SV_plus
      always_comb begin
         for (integer ii = 0; ii < 4; ii++)
            /ii[ii]$$partial[31:0] = (ii == 0) ? 0 : $partial[(ii+4-1)%4] + $addend[ii];
         $$sum[31:0] = $partial[3];
      end
```

Becomes:

```tlv
\TLV
   /ii[3:0]
      $partial[31:0] = (ii == 0) ? 0 : $partial[(ii+4-1)%4] + $addend[ii];
   \SV_plus
      always_comb begin
         for (integer ii = 0; ii < 4; ii++)
            /ii[ii]$$partial[31:0] = (#ii == 0) ? 0 : $partial[(#ii + 4 - 1) % 4] + $addend[#ii];
         $$sum[31:0] = $partial[3];
      end
```

### Completion

Any uses of external components (other modules, functions, and Verilog macros) should remain in `\SV_plus` context. Also, `struct` and `union` types with separate field assignments will remain in `\SV_plus`. If anything else remains in `\SV_plus`, see if you can figure out how to migrate it to `\TLV` context. For anything that remains in `\SV_plus` context, add code comments to explain the difficulty.

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Consolidate the SV-TLV Interface

Summary: Isolate the transition from Verilog to (timing-abstract) TL-Verilog and back.

Module input and output signals as well as any other signals that you were unable to translate to pipesignals may currently be used throughout the logic. It would be cleanest to consolidate the connections of SV signals to and from TLV pipesignals. New pipesignals can be defined for this and assigned to/from the corresponding SV signals.

Assign new input pipesignals at the top of the first (and probably only) `\TLV` region. Assign Verilog output signals at the end of the last (and probably only) `\TLV` region. The input and output assignments should simply connect signals to/from pipesignals. They should not include logic. Replace all previous direct uses of the i/o signals with the pipesignals. Once fully refactored, all logic should be between the input and output assignment sections and should contain no Verilog signals.

Use a `*` prefix before Verilog signal names.

So, for example, this refactoring step should result in a structure like:

```tlv
\SV
   module foo(input wire clk, input wire reset, input wire in[7:0], output wire out[7:0]);
\TLV
   |default
      @0
         // Connect Verilog inputs:
         $reset = *reset;
         $in[7:0] = *in;

         ...
         
         // Connect Verilog outputs:
         *out = $out;
\SV
   endmodule
```

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Refactor TLV

Summary: The definition of this task is still work-in-progress, but general suggestions are provided that you may find helpful to further improve the TL-Verilog code.

Further refactoring tasks are not fully defined, but feel free to continue refactoring on your own. Signals that are simply unconditionally flopped versions of other signals can be eliminated. Pipelines can be established and logic moved into the pipelines.

The rough notes below might give you some ideas, but these need to be expanded to be more complete.



=======================================
TODO:




Remove/disable clock gating logic from both models if necessary. Verify.




Introduce pipelines into TL-Verilog structure. Place pipesignals into proper pipestages, and modify uses in \SV_plus to reference and align properly. Verify.
Move all logic into its own explicit pipeline/pipestage.
Identify any opportunities to avoid replicated logic statements with TL-Verilog behavioral hierarchy. Modify. Verify.
Identify any opportunities to utilize transactions ($ANY). Modify. Verify.
Add any parameterization desired, including pipeline parameterization. Convert Verilog parameters to M5 defines where desired. Incorporate m4_define_hier where appropriate.
Do any further cleanup you feel is necessary that can be done with the verification conversion infrastructure in place. Verify.
Compare the size of the original Verilog and resulting TL-Verilog. Be happy.

Beyond Conversion
With functional verification in place
Add any desired ‘when’ conditions to the code. Verify.
Apply parameterization to verification infrastructure. Try with other parameters.

Examples
...


#### Cycle Accuracy and Clock Gating/Enabling

Clock gating/enabling conditions inherited from the original design can limit our ability to clean up the code. TL-Verilog supports fine-grained clock gating naturally. Even if the original model has no conditional clocks, it might be nice to introduce when conditions. To gate logic in more cases than the original model would results in FEV mismatches and run the risk of introducing bugs.

If we are willing to rely on the project's existing verification infrastructure as a safety net, we can apply fine-grained clock gating using reasonable assumptions. With DONT-CARE injection enabled, the DONT-CAREs will propogate in simulation and any faulty assumptions will be caught. Note the verification checkers may be checking overly aggressively and could fail even if there was no real bug introduced.

To pass FEV with additional DONT-CARES, we have to swap the roles of gold and gate. With the WIP model with clock gating is taken as the golden model, its DONT-CAREs will be trusted, and we can pass FEV. Of course it must be highlighted in `tracker.md` that we have introduced unverified assumptions.




=======================================


Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: M5 Support

This'll be a quick one. You'll now add support for macro preprocessing using M5. Update your file structure to:

```
\m5_TLV_version 1d: tl-x.org
\m5
   use(m5-1.0)
\SV
...
```

Run  `./scripts/fev.sh`.

## Task: TLV Macro

Summary: Provide the module logic as a TLV Macro

The code currently provides a Verilog module. TL-Verilog is also able to use "TLV macros" to provide and instantiate reusable components. You will restructure the code such that the module's logic is defined in a TLV macro. The module body will connect interface signals to pipesignals and instantiate the module. This way, the same file serves to provide a module or a TLV macro to instantiate the same logic.

TLV macros are a simple M5-based mechanism for text substitution. Since they have no formality, there are several options as to how to structure this. Scope, such as `|default` and `@0` could be provided by the macro or by the module. You should include all scope within the macro, following the lead of the following example.

For this initial file structure:

```tlv
\SV
   // Implements...
   module foo(input wire clk, input wire reset, input wire in[7:0], output wire out[7:0]);
\TLV
   |default
      @0
         // Connect Verilog inputs:
         $reset = *reset;
         $in[7:0] = *in;

         // TL-Verilog logic (properly indented)
         // ...
         
         // Connect Verilog outputs:
         *out = $out;
\SV
   endmodule
```

First, note that this is equivalently (using lexical reentrance):

```tlv
\SV
   // Implements...
   module foo(input wire clk, input wire reset, input wire in[7:0], output wire out[7:0]);
\TLV
   |default
      @0
         // Connect Verilog inputs:
         $reset = *reset;
         $in[7:0] = *in;
   |default
      @0
         // TL-Verilog logic
         // ...
   |default
      @0
         // Connect Verilog outputs:
         *out = $out;
\SV
   endmodule
```

Separating the logic into a TLV macro, we get:

```tlv
// The guts of module foo.
\TLV foo(/_top)
   |default
      @0
         // TL-Verilog logic
         // ...

\SV
   // Implements...
   module foo(input wire clk, input wire reset, input wire in[7:0], output wire out[7:0]);
\TLV
   // Connect Verilog inputs:
   |default
      @0
         $reset = *reset;
         $in[7:0] = *in;
   m5+foo(/top)
   // Connect Verilog outputs:
   |default
      @0
         *out = $out;
\SV
   endmodule
```

A few things worth noting:

- The macro parameter `/_top` can be used in pipesignal references to reference the scope in which the macro is instantiated. It may not be needed, but should be provided regardless to abide by conventions.
- `m5+foo(/top)` instantiates the macro in `/top` (implicit top-level) scope.
- Check to be sure you didn't lose indentation. This tends to happen sometimes.

Be sure all changes for this task have been completed fully, and run  `./scripts/fev.sh`.


## Task: Final Testing and Debugging

Summary: Wrap up the work for a clean final handoff to the user.

To wrap up, compare your final code against the original, ensuring that:

- all comments are appropriately preserved
- the code is well organized and that its structure closely aligns with the original

Look for oppotunities to improve code quality. Ensure appropriate use of whitespace for best readability.

Give fev_full.eqy a final review, ensuring that the configuration that is used will result in adequate FEV coverage. Ensure that other fev_full_*.eqy also follow a sound approach.

If any changes are made, rerun `fev.sh`. Assess the impact that your conversion had. Did the code grow or shrink, and why? What about just the TLV macro versus the original module? Does TLV context provide more or less structure? Also assess obstacles to further optimizations. Suggest further optimizations the user might want to consider, if any, and explain why you were unable to make these optimizations yourself (likely that there would be functional change that couldn't be FEVed). Reflect these in `tracker.md`.

Ideally, you were able to run FEV for each refactoring step or task, proving that the prepared Verilog is functionally identical to your resulting TL-Verilog. To double-check your work, and to provide the user with clear evidence of equivalence, now FEV the final code versus the prepared Verilog (that resulted from the preparation step, ideally identical to the code given). If you are able to get this FEV to succeed, the user is assured of equivalence.

Now, prepare your work for a clean handoff to the user. Give `tracker.md` one final review. Ensure that it is succinct, complete, accurate, properly formatted as Markdown, and useful to the user to review your work and address remaining issues. Unless the prepared code and the final code were successfully FEVed, the conversion was, overall, unsuccessful. Bring every shortcoming to light. The worst possible outcome is that your efforts introduce a bug that goes undetected. Even an undetected functional difference or an implementation difference would be concerning. So, have the mindset of a verification engineer. If it can go wrong, it will. Sweep nothing under the rug. Raise all potential issues and concerns in `tracker.md` for handoff.


# EOF (End Of File)

The following are not yet part of the official sequence yet and should be ignored.


### TODO

Some refactoring steps will impact the ability to match state signals. These include changes to the reset network and timing. They could also include encoding and timing changes, but these are outside the scope of the code-conversion goals which aim to preserve the logic (for better or worse).

For such refactoring, set up an SBY bmc flow to verify the change. The alternative is to apply reset assumptions to EQY, but this has prover quite awkward. EQY uses induction, for which `sim` initialization does not apply. Using assertions is limited without Verific. It requires a wrapper module supposedly or other goofiness that I never got to work which must have elements that are DUT-specific. So SBY mbc seems to be the answer.


### Initializing States with Reset

We've changed course on this. It doesn't help because EQY treats states as cutpoints. However, if we enable FEV using SBY and a proper reset sequence, which can enable more substantial refactoring, this would make sense.

Uninitialized State:

For FEV to succeed, internal states must initialize to corresponding values in both designs. If both models use the same name for the signal, FEV will, by default, assume they match and will only explore matching initial values. However, we will be changing signal names, in which case, we must take measures to ensure consistent initialization.

One possible resolution is to provide a match statement in the FEV configuration, such as:

```
[match <module-name>]
gold-match verilog-name SandPiper-generated-name
```

This approach may work for us, but we will take an additional step to be sure, adding reset to the logic.

Most reset methodologies require internal states to be reset by a reset input signal to known values after a minimum number of reset cycles. You will identify any internal states that do not abide by this methodology and update the logic to apply reset.

Identifying uninitialized State:

States use non-blocking assignments, but not all non-blocking assignments are for state signals. Some are for staging flip-flops, which may naturally reach a known state from an upstream application of reset. States can retain, recirculate, or recirculate and update their value from one cycle to the next. Any non-blocking assignment to a signal that depends on itself (its registered value) is state. So, if the signal appears on the left- and right-hand sides of its non-blocking assignment, it is a state signal. Also, if the assignment is not complete, meaning there is not an assignment under all conditions, this also is a state since it can implicitly retain its value.

Pathologically, there could be a larger recirculation loop through multiple assignments that would require reset. This is atypical, but it you are uncertain, lean conservative, and apply reset.

Examine all non-blocking assignments, identifying those that are (or might be) state (those that recirculate). Any that are not forced into a known state by a reset signal are problematic.

Applying Reset:

If the module has uninitialized states and no reset input signal, you must add one. Add it as `reset`.

Update the logic for uninitialized state signals to incorporate reset initialization (to zero).

FEV must be configured to apply reset to the models. The `.eqy` files do not do this by default, but there are two commented line you can modify. Enable these lines if the module has a reset input (whether original or added by you), and update them to reflect the proper reset signal name and assertion level (`-reset` or `-resetn`).

List these issues and design changes in `tracker.md`.
