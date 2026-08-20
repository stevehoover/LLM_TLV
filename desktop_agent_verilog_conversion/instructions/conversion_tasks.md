# Tasks for LLM-assisted Verilog to TL-Verilog Code Conversion

These tasks define a process for converting Verilog to TL-Verilog. An overview of the conversion process should have been provided in this Project/GPT's instructions.

## Task: Preparation

Summary: Prepare the initial code, tracker, status, and FEV configurations to begin conversion.

### Continuation

If asked to continue a conversion that has already been started, `cd` to the given working directory for the conversion, and assess the current progress in `status.md` and `tracker.md` as well as reviewing the current code. Skip ahead to the appropriate task using `./scripts/get_task.py '<task-title>'` to continue the work in progress.

### `prep.sh`

When starting fresh, a script `desktop_agent_verilog_conversion/prep.sh` assists you in initializing the conversion directory. The user should have provided you with a directory path and a Verilog file path to use for the conversion. Search the Verilog file to find its module name (perhaps `grep module <orig.sv>`), then run `.../prep.sh <directory> <verilog-file> <module-name>` to safely create and initialize `<directory>` with:

- `prepared.sv`, `wip.tlv`, and `feved.tlv`: as copies of <verilog-file>
- `tracker.md`: Some initial empty categories (which you may change as appropriate).
- `status.json`: to contain: `{"task": "Preparation", "fev.sh": "none", "llm": ""}
- `fev.eqy` and `fev_full.eqy`: based on the template `fev.eqy` in `desktop_agent_verilog_conversion/fev/`.
- `scripts/`: as a link to the `desktop_agent_verilog_conversion/` directory containing all helper scripts (e.g. `fev.sh` and `get_task.py`).

<directory> and <verilog-file> must be given as absolute paths.

After running `prep.sh ...`, `cd` to <directory>. As you consider the remaining instructions for this task, update `prepared.sv`, `tracker.md`, and `status.json`.

### Libraries

`prepared.sv` may depend on external files via tick-include statements, or it might depend on the build environment to provide other files on the command line...
The MCP tools require the top-level module definition to be encapsulated in a single file. This includes any submodules, functions, and macro definitions that might be instantiated by the module. If any other files are needed, either find them and inline the needed content, or record the issue and stop to give the user a chance to assess the situation.

### Latch-based Design

It is expected that the original design is flip-flop-based, triggered by the rising edge of the clock. If logic is driven by the falling edge of the clock, it may be converted to transition a phase earlier or later as long as the output timing is preserved for FEV. This may require the use of grouping/partitioning statements in EQY configurations. Any changes like this that may impact the nature of the physical implementation should be noted in `tracker.md`.

### Clock Gating/Enabling

Clock gating logic can be difficult to convert. TL-Verilog logic infers flip-flops and does not have direct control over the application of clock to them. TL-Verilog supports fine-grained clock gating or enables using "when conditions", e.g., `?$valid`. This can be used to create clock gating that matches the original, but it may result in awkward code.

There is a distinction between functional and non-functional clock gating/enabling. In functional gating/enabling the gating is functionally required. In non-functional clock gating, the gating condition is functionally a DONT-CARE. If we know the gating to be non-functional, we have more flexibility in the conversion.

If the module has clock gating/enable inputs that can be determined to be non-functional, assume the input to be DONT-CARE (1'bX). Comment on the use of clock gating or clock enabling in the original code and any modification to the code.

### No Tri-States

This process does not support conversion of tri-states. You may continue, but note the issue in `tracker.md`.

### Prepare the Code

Make sure you are in the established working directory for this conversion. Prepare `prepared.sv` as instructed above if needed. If any modifications were necessary from the original code or issues are found, report them in `tracker.md` and to the user.

This establishes the baseline code that you will convert. Henceforth, all modifications will be made in `wip.tlv` and MUST PASS FEV using `fev.sh`. If you made changes to `prepared.sv`, copy `prepared.sv` to `wip.tlv` and `feved.tlv`.

Run `fev.sh` for this task as well. It should pass since there are no changes vs. `wip.tlv`, but this will catch any script and setup errors before you begin refactoring.


## Task: Signal Matching

Add to the `[match ...]` section of `fev_full.eqy` (not `fev.eqy`) a match line for every internal signal (not module interface signals) in the `wip.tlv` module (using default parameter values). The section should look like:

```
[match <module>]
gold-match foo foo
gold-match bar bar
```

`fev.sh` will update this as you proceed.

Even though there is no update to `wip.tlv` for this step, run `fev.sh` anyway to checkpoint your work in `history/`.


## Task: Parameters

If the module has any parameters or uses any tick-defines, additional FEV configurations can be established for alternate parameter sets. `fev.sh` will test each parameter set, each defined by a `fev_full_*.eqy` file.

Examine the use of module parameters and tick-define parameters in `prepared.sv` to determine a set of parameter sets to adequately test future refactoring steps. Make sure key generate scenarios are covered. Parameters should be chosen that impact elaboration and logic behavior. This includes generate `if` conditions, for example. Generate `for`s should be tested with no iterations, one iteration, and multiple iterations if possible. Avoid parameters that wouldn't be legal in the original code. It may be necessary to inspect project documentation or the broader code base to determine this. Avoid large parameter values to avoid large FEV runs. Keep the set (of sets) minimal, but sufficient.

Create a corresponding `fev_full_*.eqy`, e.g. `fev_full_WIDTH_4_BYPASS_1.eqy`, for each parameter set. Initialize each as a copy of `fev_full.eqy`. For module parameters, uncomment the line `#chparam -set ...` and update it with one `-set <PARAMETER_NAME> <VALUE>` for each overridden parameter. For tick-defines, use `-Dname=value` on both `read_verilog` lines. Modify the match list if the parameters affect which signals will be elaborated.

Describe the parameter sets in `tracker.md`.

If any modifications were made, run `fev.sh`. Since no changes were made to `wip.tlv`, failure points to an issue with `fev_full_*.eqy`. Compare thees versus `fev_full.eqy` to be sure you initialized them properly and also scrutinize the match lists. There could also be failures if you chose a configuration that is not supported in the original code.


## Task: No Tabs

Summary: Replace tabs with spaces.

Run `./scripts/no_tabs.py` to replace tabs with spaces in `wip.tlv`.

Run `./scripts/fev.sh` for good measure.


## Task: Reset and Clock

Summary: Ensure proper clock and reset signals (if needed).

TL-Verilog works with a global (free-running) clock, called `clk`. If the Verilog code uses a clock by a different name, assign it to a new `clk` signal, and update the code to use `clk` instead. A module that is purely combinational may not have a clock, and this is okay. Just be aware that if any sequential logic is defined using TL-Verilog, SandPiper will assume a `clk` exists.

TL-Verilog code conventionally uses a positively-asserted synchronous reset signal, called `reset`, and FEV configurations may assume this name (not currently true, but we'll prepare for this in any case). If the module has a reset input, analyze the logic to determine its assertion level and whether it is synchronous or asynchronous. It's name and/or code comments may also be revealing. If there is no reset signal, none is needed, and this task is complete.

If there are any asynchronous uses of reset, the following changes will be needed that impact functionality and cannot be FEVed. At this point, that's okay. `feved.tlv` and `wip.tlv` should be unchanged from `prepared.sv`. Double check to be sure. If you do need to make a change, note that `prepared.sv` should be read-only now. You'll have to make it writable, and restore it to read-only when you are done. If the reset input is called `reset`, change its name in `prepared.sh` to `areset` (or `aresetn` if negatively asserted). Modify `prepared.sv` to synchronize the asynchronous reset using two flip-flops as a synchronizer, producing `reset` or `resetn`. Further update `prepared.sv` to use this new reset synchronously. Copy changes to `feved.tlv` and `wip.tlv`. Update `tracker.md` to highlight these unFEVed changes in `prepared.sv`.

If the input reset signal is negatively asserted, create an internal positively-asserted reset. This can be done in `wip.tlv` as it will not impact behavior. Call this positively-asserted reset `reset`. Update all uses of the old reset to use this new one.

Unless you had to establish a new baseline `prepared.sv` model, there should be no interface changes for this (or any subsequent) task. `reset` can be created from the reset input as an internal signal, not by changing the interface.

**Timing: add this during initial setup:**
Add the clock bridge (`wire clk = <port_name>;`) in the `\SV` block
immediately during initial setup, even before any `\TLV` content is added.
Do NOT wait until SandPiper errors on a missing `clk` signal. The first
time any `>>1$signal` is written, SandPiper emits `always_ff @(posedge clk)`.
If `clk` is not yet declared, you will get an unresolved signal error
mid-conversion. Adding the bridge at setup time prevents this entirely.

## Task: Simplify Code Generation

Summary: Where possible, remove logic from generate `if`/`else` blocks.

Generate `if` blocks are particularly problematic to convert to TL-Verilog. TL-Verilog uses M5 for code construction/elaboration, and, at this point, we need to retain the module parameterization, which isn't possible if we convert to M5.

In this task, you will eliminate as many generate `if`/`else` blocks as we reasonably can. Note that in SystemVerilog, the use of `generate` and `endgenerate` keywords is optional.

Complete this task one generate `if` block at a time, together with its chained `else if`/`else` blocks.

We can eliminate a chain of blocks if all of its assignment expressions would be valid under all conditions--if they can be moved outside of the blocks without introducing compilation errors. The downside is that, under certain parameters, logic will be included in the design that isn't needed. This logic is necessarily unused (dead) logic, and, in most cases, logic synthesis tools will easily remove it from the design.

Identify assignments or groups of assignments that can be safely move out from conditioning ('if', tick-ifdef, etc.). The right-hand-side expression(s) must depend only on signals/pipesignals that are similarly unconditioned. Bit ranges must remain valid when unconditioned.

Blocks that contains an instantiation of a non-trivial module, function, or macro should not be refactored.

Consider multiple blocks of logic under the same condition together. The goal is to reduce the number of configurations that construct different code. Remaining configurations will be dealt with in a subsequent task. Capture in `status.json`'s `llm` field a list of the blocks/conditions you intend to eliminate.

For each generate `if` chain or tick-ifdef/ifndef that is to be refactored, incrementally transition logic declarations and assignment statements/blocks outside the condition. It may be necessary to uniquify the signal names as you do. Signals originally assigned under different conditions can be converted to ternary expressions as they are pulled out. Provide comments, like `// relevant if BYPASS` as statements are removed from `if (BYPASS)`.

You'll need to update match sections accordingly. Dead signals have nothing to map to. Hopefully, they don't create FEV issues. Inform the user if they do.

Let's talk through an example. Let's consider the following `if` block. (It performs a cyclic find-first, assigning `o_next_mask` (`logic [N-1:0]`), based on a valid mask `logic [N:0] i_valid_mask` and an encoded current index `logic [$clog2(N)-1:0] i_current`). The `if`/`else` block treats the degenerate `N=1` case specially.

```
if (N <= 1) begin: nn_eq1
   assign o_next_mask = {N{1'b0}};
end else begin: nn_gt1
   logic [N-1:0] valid_hi;
   assign valid_hi = i_valid_mask & ~( (1 << i_current) - 1);
   assign o_next_mask = | valid_hi ? find_first(valid_hi) : find_first(i_valid_mask);
end
```

According to the guidance above, we might not refactor this block because it calls a function (`find_first`). But, let's look at the refactoring anyhow.

This block might ultimately become:

```
// relevant if (N > 1)
logic [N-1:0] valid_hi_n_gt1, next_mask_n_gt1;
assign valid_hi_n_gt1 = i_valid_mask & ~( (1 << i_current) - 1);
assign next_mask_n_gt1 = | valid_hi_n_gt1 ? find_first(valid_hi_n_gt1) : find_first(i_valid_mask);
// end if (N > 1)
assign o_next_mask = (N <= 1) ? {N{1'b0}} : next_mask_n_gt1;
```

The expression for`valid_hi` has been pulled out as `valid_hi_n_gt1`. The expression for `o_next_mask` has been pulled out as `next_mask_n_gt1`. And `o_next_mask` is now assigned with a ternary expression. While the new intermediate signal, `next_mask_n_gt1`, wasn't necessary, introducing it helps to isolate logic that is specific to N > 1.

Completion: This task is complete only once all `if`/`else` chains and tick-ifdef/ifndef sections have been refactored or determined to be poor candidates for refactoring.

Update `tracker.md`, capturing a list of remaining `if` chains conditions and tick-ifdef/ifndef conditions that will need to be parameterized using M5.

**Stage alignment in EQY match lines:**

When adding a `[match]` entry for a newly converted TL-Verilog
pipesignal, explicitly check the stage/transaction alignment of the
pipesignal reference.

For pipesignals referenced through a pipeline scope such as
`|default`, the match may require an explicit `<>0` alignment suffix.
For example:

```text
gold-match is_uncore_aperture |default<>0$is_uncore_aperture
```

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Eliminate Split Assignments

Summary: Avoid separate assignments for different portions of a vector signal.

In Verilog, it is legal to assign different portions of a vector signal in separate assignments. This is not permitted in TL-Verilog. Likely, a combined assignment can be created by simply concatenating the expressions. If the individual assignments are complex, an intermediate signal can be introduced to hold the partial expression that is then concatenated. For example:

```tlv
logic [31:0] addr;
assign addr[31:12] = <complex_expression>;
assign addr[11:0] = page_addr;
```

Might become:

```tlv
logic [31:0] addr;
logic [31:12] addr_b31_b12;
assign addr_b31_b12 = <complex_expression>;
assign addr = {addr_b31_b12, page_addr};
```

New intermediate signals do not need to be matched in `fev*.eqy`.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: If/Else and Case to Ternary

Summary: Procedural `if`/`else`/`case` expressions are converted to ternary expressions.

Procedural `if`/`else` constructs and `case*` statements assign signals to different expressions under different conditions. TL-Verilog favors the use of ternary expressions for such assignments because ternary expressions follow single assignment semantics. (They also isolate the assignments of each signal, resulting in finer granularity assignments. Since assignments are the atomic unit of timing abstraction, this results in greater timing flexibility.)

`if`/`else`/`case` may not assign a signal in all cases. Ternary expressions are explicit in all cases. Unassigned cases must explicitly retain the previous value in the ternary expression.

Let's look at some examples (declarations not shown):

```verilog
always_comb
   if (cond)
      y = b;
   else
      y = c;
```

becomes:

```verilog
always_comb
   y = cond ? b : c;
```

Let's look at a more interesting example.

```verilog
always_ff @(posedge clk) begin
   if (valid) begin
      if (cond1)
         y <= b;
      else if ($cond2)
         y <= c;
      else begin
         y <= d;
         z[7:0] <= e;
      end
   else
      y <= f;
   end
end
```

Note that `y` is assigned under all conditions, but `z` is not and must be retained when not assigned.

This example can be transformed incrementally, first transforming the inner assignment of `y`:

```verilog
always_ff @(posedge clk) begin
   if (valid) begin
      y <=
         cond1 ? b :
         cond2 ? c :
                 d;
      if (cond1) begin
      end else (cond2) begin
      end else
         z[7:0] <= e;
   else
      y <= f;
   end
end
```

Note that the empty conditions, above, are acceptable, but `begin`/`end` must be added.

Continuing to refactor `y` and `z`:

```verilog
always_ff @(posedge clk) begin
   y <=
      $valid ?
         cond1 ? b :
         cond2 ? c :
                  d :
      //default
         f;
   if (valid && (! cond1 && ! cond2))
      z[7:0] <= e;
end
```

Then to refactor `z` to use a ternary expression, we must explicitly recirculate `z`.

```verilog
always_ff @(posedge clk) begin
   z[7:0] <= valid && (! cond1 && ! cond2) ? e : z;
```

Since `always` blocks have sequential semantics, signals may be assigned and reassigned. This can get tricky to map to ternary semantics for several reasons. In an `if`/`else` chain, the final assignment takes priority, whereas, in a ternary chain, the first case takes priority, so the order of cases must be reversed. Also, for blocking assignments, subsequent assignments can depend on earlier ones. It can help to create intermediate signals in these cases. Take complex cases one signal at a time (and even an incremental step toward one signal at a time). The code for a given signal can get distributed over a long `if`/`else` chain. It can help to first consolidate the logic for a signal by constructing its own `if`/`else` chain. Then convert that. You can convert an inner `if`/`else` chain before converting an outer chain. Break the control flow down into cases (conditions). Define new intermediate signals for these conditions if they will be reused by other signals. Then, with the cases mapped out, introduce the ternary expression. Generally, favor a flat organization of cases over a nested structure of ternary expressions for readability.

`case*` statements can be transformed similarly.

```verilog
always_comb begin
   case (sel)
      2'b00: y[7:0] = 8'hAA;
      2'b11: y = 8'h55;
      default: y = 8'h00;
   endcase
end
```

Results in:

```verilog
assign y[7:0] =
      (sel == 2'b00) ? 8'hAA :
      (sel == 2'b11) ? 8'h55 :
                       8'h00;
```

Like `if`/`else` chains, `case` without `default` can infer latches and the resulting ternary expression must explicitly recirculate the value.

`unique case` implies exclusivity. The case conditions must be one-hot. They imply runtime checking and enable logic synthesis optimizations. To achieve this with ternary expressions, add assertions and runtime checking that exactly one of the conditions of the `unique case` is asserted.

For example:

```verilog
always_comb begin
   unique case (sel)
      2'b01: y = 8'hAA;
      2'b10: y = 8'h55;
   endcase
end
```

```verilog
always_comb begin
   y[7:0] =
      (sel === 2'b01) ? 8'hAA :
      (sel === 2'b10) ? 8'h55 :
                        'x;  // impossible
end
assert property (@(posedge clk) $onehot(sel));
```

If you have trouble getting the assertion correct, make a note of the potential checking/synthesis implications in `tracker.md`.

Refactor in a manner that minimizes common subexpressions. Create intermediate signals for subexpressions, such as condition expressions affecting multiple signals. New intermediate signals do not need to be matched in `fev*.eqy`.

The conversion to ternary expressions organizes the logic differently. Often, we have a matrix of conditions and signals, and we have a value to assign (or retain) in each cell of that matrix. The `if`/`else` chain or `case` breaks this matrix first by condition, then by signal. Using ternaries, organizes code first by signal, then by condition. There are pros and cons either way. When signals are tightly associated, the `if`/`else` organization can be more readable/maintainable. This can be mimicked using ternaries by assigning concatenations of signals to concatenations of expressions within the ternary. Consider building up concatenations versus replicating ternary structure, although, do not overuse this. It is easy to introduce bugs with this structure with mis-aligned bits in the concatenations, so it can be a maintenance issue. Find a reasonable balance based on the scenario.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Procedural For Loops

Summary: Transform procedural `for` loops with inter-iteration dependencies to avoid reassignments.

Some procedural loops might update the same signal in each iteration, based on its value in the previous iteration. (These are often "reduction" operations.) TL-Verilog discourages procedural assignments. The pattern we'll follow for translating these is to create an array signal to hold the intermediate results of each iteration, assigning a unique entry in each iteration. For example:

```verilog
logic [31:0] sum, addend[3:0];
always_comb begin
   sum = 0;
   for (integer i = 0; i < 4; i++): ii
      sum = sum + addend[i];
end
```

can be refactored to use explicit partial sums, as:

```verilog
logic [31:0] sum, addend[3:0], partial[3:0];
always_comb begin
   for (integer i = 0; i < 4; i++): ii
      partial[i] = (i == 0) ? 0 : partial[i-1] + addend[i];
   sum = partial[3];
end
```

Some tools object to `partial[i-1]`, which can index `partial[-1]`, which doesn't exist. The value is unused, but, to make these tools happy, it may be necessary to use `partial[(i+4-1)%4]` to keep the index in range.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Eliminate Always Comb

Summary: Transform `always_comb` to `assign`.

Transform all assignments in `always_comb` and non-edge-triggered `always` blocks to `assign` statements. All `always_comb` blocks should be eliminated.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: TLV File Format

Summary: Format the file as a TL-Verilog file with M5 support with module contents in an `\SV_plus` block.

Convert the code to TLV file format with M5 support. As a first step, the code can all be in one big `\SV` region. This simply requires prepending these lines to the beginning of the file:

```tlv
\m5_TLV_version 1d: tl-x.org
\m5
   use(m5-1.0)
\SV
```

Next, put the top module body (excluding the `clk` declaration and assignment, if there is one) in `\SV_plus` context, where the use of TL-Verilog pipesignals is permitted. Move it into an `\SV_plus` block in stage 0 (`@0`) of a "default" pipeline (`|default`). So:

```tlv
\m5_TLV_version 1d: tl-x.org
\m5
   use(m5-1.0)
\SV
module(...);
   wire clk = ...;
<module-body>
endmodule
```

becomes:

```tlv
\m5_TLV_version 1d: tl-x.org
\m5
   use(m5-1.0)
\SV
module(...);
   wire clk = ...;
\TLV
   |default
      @0
         \SV_plus
            <module-body>
\SV
endmodule
```

Be sure to use three spaces of indentation for each TLV scope and within the `\SV_plus` block. Indent `|default` 3 spaces, `@0` 6 spaces, `\SV_plus` 9 spaces, and the entire module body 12 spaces. This is a good opportunity to apply consistent indentation within the module body as well. (This body need not use specifically three spaces for indentation.)

Code in an `\SV_plus` block is parsed for TLV identifiers. At this point, we should have no TLV identifiers, so we must avoid all syntax that could be mistaken as a TLV identifier. Identifiers begin with one or more symbol characters and are followed immediately by word characters.

The first change you can make to reduce the likelihood of false matches also establishes consistent coding conventions. Make sure all Verilog operators (unary, binary, arithmetic, ternary, and range specifiers like (`:`)) have whitespace separating them from any neighboring word characters. `=` and `<=` must always have whitespace on either side. Most Verilog coding guidelines would not suggest whitespace after unary operators like `!`, `~`, `|`, `&`, and `^` and in ranges, but, for TL-Verilog, it is best practice to have whitespace separation. This distinguishes, for example, `| foo` as a unary operator versus `|foo`, a pipeline called `foo`. Be sure to catch these common unary opeartor scenarios.

Next, some valid Verilog syntax, such as `$clog2`, `$display`, `%s`, and `@10` requires word characters immediately following symbol characters, and whitespace separation cannot be introduced. We need to ensure that these valid Verilog strings are not interpreted as TL-Verilog syntax. The `\` escape character can be used for this purpose within `\SV_plus` context. `\` ensures that the next character is treated as a literal Verilog character, so `$clog2`, `$display`, `%s`, and `@10` must become `\$clog2`, `\$display`, `\%s`, and `\@10`. Symbols of concern are  `$`, `@`, `|`, `/`, `#`, `%`, `*`, and `\`. Only symbol characters that immediately precede word characters need escaping. For example `!foo && bar && |baz` would need escaping as `!foo && bar && \|baz`--`!` is not a symbol of concern, and `|` is. `! foo && bar && | baz`, however, needs no escaping because of the whitespace separation. In practice, it should be fairly rare that escaping is required. Conflicting syntax occurs most commonly in test bench and logging code, and our module shouldn't contain test bench code.

Note that these `\`s will carry over into `\TLV` assignment expressions, which also use Verilog syntax.

Before testing, double-check your indentation (3 spaces for each scope; no tabs). The whole <module-body> must be indented properly. This often trips you up.

In case you have difficulty with this task, the `\SV` region can be converted to an `\SV_plus` block incrementally, moving a subset of lines from the `\SV` block to the `\SV_plus` block in each step (keeping the overall order of the lines consistent).

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Define M5 Configurations

Summary: Define M5 parameters to affect TL-Verilog code generation.

If the module has no generate `if` blocks (noting that the `generate` keyword is optional in SystemVerilog) and no tick-ifdef/ifndef, you may skip this task and the next.

Verilog module parameterization and tick-defines are elaborated prior to processing other Verilog constructs. This enables conditional elaboration within the model. While TL-Verilog code can contain module parameters and tick-defines, these are simply passed along to be processed by Verilog tools. SandPiper cannot use them to conditionally generate TL-Verilog code. For this purpose, SandPiper uses M5 macro preprocessing. Thus, to prepare for conditioned assignments to be converted to TL-Verilog, we must convert the conditioning from generate `if`/`else` and tick-ifdef/ifndef to M5.

This refactoring step will introduce sufficient M5 parameterization to construct the TL-Verilog code correctly for different parameter scenarios. M5 parameters will correspond to the elaboration conditions in the current `wip.tlv` code. A set of configurations will be defined covering all legal parameter scenarios. SandPiper will be run for each of these configurations, producing a unique Verilog module for each.

A prior task should have captured a list of remaining conditions in `tracker.md`. Also analyze `wip.tlv`, to definitively identify the conditions to parameterize with M5 and a complete flat list of legal code configurations. If more than eight configurations are necessary, wrap up your efforts, and seek user guidance.

Update `config.json` to include a flat list of legal configurations and corresponding M5 boolean (0/1) condition parameters. (If none are needed, skip this task.) For example, Verilog containing:

```verilog
if (WIDTH=32) begin
   ...
end
...
if (WIDTH=64) begin
   ...
end
```

Might be parameterized as:

```json
{
  "top": "my_dut",
  "M5_configs": {
    "WIDTH_32": "--m5def cond_width_32=1 --m5def cond_width_64=0",
    "WIDTH_64": "--m5def cond_width_32=0 --m5def cond_width_64=1",
    "WIDTH_OTHER": "--m5def cond_width_32=0 --m5def cond_width_64=0"
  }
}
```

No case is needed for `--m5def cond_width_32=1 --m5def cond_width_64=1` since both conditions are determined from `WIDTH` and are inherently mutually exclusive. If it can be determined that 32 and 64 are the only legal values for `WIDTH`, the `WIDTH_OTHER` case can be dropped and `width_32` can be used in place of `width_64` (with opposite polarity), so `width_64` can also be dropped.

Here's an example with nested conditions:

```verilog
`ifdef ASIC
...
`ifndef GATING
...
`else
...
`endif
`endif
```

```json
{
  "top": "my_dut",
  "M5_configs": {
    "NOT_ASIC": "--m5def cond_asic=0",
    "ASIC_GATING": "--m5def cond_asic=1 --m5def cond_gating=1",
    "ASIC_NO_GATING": "--m5def cond_asic=1 --m5def cond_gating=0"
  }
}
```

If both of these examples appeared together, the set of configurations would be the crossproduct. Assuming `WIDTH` can only be 32 or 64, we'd have:

```json
{
  "top": "my_dut",
  "M5_configs": {
    "WIDTH_32_NOT_ASIC": "--m5def cond_width_32=1 --m5def cond_asic=0",
    "WIDTH_32_ASIC_GATING": "--m5def cond_width_32=1 --m5def cond_asic=1 --m5def cond_gating=1",
    "WIDTH_32_ASIC_NO_GATING": "--m5def cond_width_32=1 --m5def cond_asic=1 --m5def cond_gating=0",
    "WIDTH_64_NOT_ASIC": "--m5def cond_width_32=1 --m5def cond_asic=0",
    "WIDTH_64_ASIC_GATING": "--m5def cond_width_32=1 --m5def cond_asic=1 --m5def cond_gating=1",
    "WIDTH_64_ASIC_NO_GATING": "--m5def cond_width_32=1 --m5def cond_asic=1 --m5def cond_gating=0"
  }
}
```

Also, identify in `config.json` which is the default configuration, corresponding to default module parameters and no tick-defines, e.g.:
```json
{
   ...
   "default_config": "WIDTH_32_NOT_ASIC"
}
```

With `configs` added, SandPiper will run for each configuration, producing, e.g., `wip_WIDTH_32_NOT_ASIC.sv`.

Update the `read_verilog` commands of all `fev_full_*.eqy` to read the correct `wip_*.sv`, corresponding to the `-D<NAME>=<VALUE>` and `chparam -set <NAME> <VALUE>` parameters. Do not update `fev.eqy` and `fev_full.eqy`. These should continue to use `wip.sv`, which will be linked to the `wip_*.sv` corresponding to `default_config`. Use `grep read_verilog fev_full_*.eqy` to be sure you didn't miss any updates.

At this point, each `wip*.sv` should contain the same Verilog output as `wip.sv` did previously, but run `fev.sh` to test the flow with your configuration changes.


## Task: Configure Using M5

Summary: Replace generate `if` and tick-ifdef/ifndef with M5-based conditioning.

There should now be the necessary M5 condition variables defined to use M5-based code construction in place of generate `if` and tick-ifdef/ifndef conditioning.

```tlv
   m5_if_eq_block(m5_cond_xxx, 0, ['
   // cond true
   '], ['
   // cond false
   '])
```

Will result in:

```tlv
   
   // cond true
   
   
   
```

or:

```tlv
   
   
   
   // cond false
   
```

Lines are kept aligned between source TLV and generated Verilog files.

A Verilog generate `if` might be converted as follows:

```verilog
   reg foo;
   if (RESET == "INIT") begin : foo_reset
      initial foo = 1'b0;
      always_ff @(posedge clk) foo <= bar;
   end else begin : foo_init
      always_ff @(posedge clk) foo <= reset ? 1'b0 : bar;
   end
```

Can be converted to:

```tlv
   logic foo;
   m5_if_eq_block(m5_cond_reset, 0, ['
   initial foo = 1'b0;
   always_ff @(posedge clk) foo <= bar;
   '], ['
   always_ff @(posedge clk) foo <= reset ? 1'b0 : bar;
   '])
```

This impacts the Verilog hierarchy, and may require other code updates. A more incremental approach is recommended, by first updating to:

```tlv
   logic foo;
   m5_if_eq_block(m5_cond_reset, 0, ['
   if (1) begin : foo_init
      initial foo = 1'b0;
      always_ff @(posedge clk) foo <= bar;
   end
   '], ['
   if (1) begin : foo_reset
      always_ff @(posedge clk) foo <= reset ? 1'b0 : bar;
   end
   '])
```

This preserves the hierarchy, and allows testing with `./scripts/fev.sh` before flattening the hierarchy by removing the `if (1)` conditions.

Convert all conditions to M5. This task is successfully complete when all generate `if` chains (including `if (1)`) and all use of tick-ifdef/ifndef have been eliminated.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Eliminate Multiple Assignments

Summary: If any constructs remain containing multiple statements assigning the same signal, try to eliminate them.

Look over `wip.tlv` to see if there are any constructs containing multiple statements assigning the same signal. These require special consideration in TL-Verilog and should have already been eliminated by prior tasks. If you find any, report the oversight in `tracker.md` if not already reported, and see if you can find a way to eliminate them. Look back at prior task instructions that may relate to the situation.

Specifically, multiple assignments of concern could occur in the following constructs:

- `case*` and procedural `if`/`else` (under different conditions)
- `always` blocks (that reassign a signal)
- generate `if` (under mutually exclusive conditions)
- different tick-ifdef/ifndef sections (under mutually exclusive conditions)

Yosys will report a fatal error for multiple concurrent assignments in different `case`, `if`/`else`, and `always` blocks, unless they are mutually exclusive based on code elaboration (generate `if`/`else` chains and tick-ifdef/ifndef), so you don't need to detect these concurrent situations.

Some scenarios are okay and may remain:

- Assignments under mutually exclusive M5 conditions are fine. For complex M5 configurations, it might be easier to analyze the generated Verilog (being sure it is current), though this may require analyzing numerous files.
- Initial assignments (e.g., `initial foo = 1'b0;` or `logic foo = 1'b0;`) are not considered assignments for this task.

If you made any code changes (even just comments), ensure that `./scripts/fev.sh` passes.


## Task: Name Generate Blocks

Summary: Name each generate `for` loop.

Give each generate `for` loop a short name, and add `begin`/`end` if absent. The name may be based on the name of a `for` loop's `genvar`, or on the meaning of the block. Use lower-case.

If any changes were made, pass `./scripts/fev.sh` before continuing.


## Task: Naming Conventions

Summary: Update the Verilog signals to conform to TL-Verilog naming convensions.

In preparation for converting Verilog signals to TL-Verilog pipesignals, rename Verilog signals to names that will be legal pipesignal names. (We will not use TLV state signals, only pipesignals.) Pipesignal names are limited to using lowercase ASCII letters, digits, and underscores. They are comprised of "tokens", separated by `_`. Each token is a string of 1 or more letters, followed by zero or more digits. The name must begin with at least two letters.

So:

- Rule 1: lower-case ASCII word characters only
- Rule 2: tokens (separated by `_`) must be one or more letters optionally followed by any number of digits
- Rule 3: the first two characters in the name must be letters

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

First, convert internal signals (not module interface signals). Conveniently, these signals are listed in the `[match ...]` section of `fev_full.eqy` (with one-to-one mappings).

A script, `./scripts/rename_sigs.py` is provided to assist in determining violations and in applying name changes from `fev_full.eqy` to `wip.tlv`. First, run `./scripts/rename_sigs.py -n -a`. This reports all non-compliant gate signal names in `fev_full.eqy`, and other potential issues.

Update `fev_full.eqy` to correct all issues, e.g.:

```
[match <module-name>]
x_len xx_len
```

Then run `rename_sigs.py` to apply the new names. If issues are reported, correct and repeat. Run `rename_sigs.py -h` for full usage.

Apply these same naming conventions to generate `if`/`else` and `for` loop names as well. You can use `rename_sigs.py -t name1 name2 ...` to test these names. Do not change `clk`. This name is required by SandPiper for the global clock.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Signal Assignments to TLV Pipesignal Assignments

Summary: Convert internal boolean and bit-vector Verilog signal assignments to TL-Verilog pipesignal assignments.

In this task, you'll convert signal assignments to TL-Verilog and their assigned signals to pipesignals. Exclude:

- anything outside the `\TLV` region
- the declaration and assignment of `clk` (which should be in the `\SV` region, not `\TLV`, anyway)
- anything assigned within a generate block (noting that in SystemVerilog the `generate` keyword is optional)
- anything assigned within a procedural `for` loop
- signals with signed or user-defined types (non-bit vector)
- signals assigned by a module, function, or macro instantiation.

All logic remains in `|default@0` for this task.

Each assignment can be converted independently of the others. To preserve file structure, convert from top to bottom, essentially migrating the `\SV_plus` line downward as you go. You can use this `\SV_plus` line as your progress indicator. Label it with `\SV_plus   // YOU ARE HERE` to distinguish it from other `\SV_plus` lines you might introduce. Remove the indicator comment (or the whole line, as appropriate) when done with the task.

As you convert lines, any that must remain in `\SV_plus` context can be kept as such by creating a new `\SV_plus` block for them, maintaining the order of statements. For example:

```
\SV_plus   // YOU ARE HERE
   localparam max = 10;
   reg foo;
   ...
```

becomes:

```
\SV_plus
   localparam max = 10;
   reg foo;
\SV_plus   // YOU ARE HERE
   ...
```

As above, Verilog signal declarations can remain in `\SV_plus` until their corresponding assignments are converted, at which point, they can be deleted. `localparam` declarations, Verilog type declarations, and anything else not involved in this task can remain in `\SV_plus` throughout this task.

M5-conditioned sections beginning with, e.g., `m5_if_eq_block(m5_cond_w_1, 1, ['`, do not affect your ability to refactor the code. Use similar M5 conditioning context for the converted code.

Assignments of module output signals can be pulled out of `\SV_plus`. Add a `*` prefix to Verilog signals (assigned and used), if not already present. E.g. `*o_foo = *o_bar + $baz;`.

Convert `assign` assignments as follows:

- Add a `$` prefix to the assigned name(s) everywhere in `wip.tlv`. (Optionally, you can use, e.g., `./scripts/rename_sigs.py foo $foo`.)
- Move the assignment out from its `\SV_plus` block as a TLV assignment. TLV assignments combine declaration and assignment, e.g. `$foo[3:0] = ...;`.
- Remove the Verilog signal declaration.

TL-Verilog assignments use Verilog `assign` syntax except:

- The `assign` keyword is dropped.
- For vectors (non-booleans) the bit range is added immediately after the pipesignal identifier and uses Verilog syntax, e.g. `$foo[WIDTH-1:0] = ...;`.
- Verilog signals in TLV assignments should be prefixed by `*` (though it's not actually necessary).
- Concatenations on the left-hand side are permitted, e.g. `{*foo, <<1$bar[1:0]} = ...;`. Preserve the concatenation structure from the original assignments.

The rest should be non-blocking assignments. These convert similarly, except the value being assign is the next value of the signal--taking effect after the clock edge. In TL-Verilog we express the next value by prepending `<<1`. Thus, the most direct conversion of:

```
always @(posedge clk)
   foo <= bar;
```

is:

```
<<1$foo = bar;
```

Non-blocking assignments that use a conditioned clock (gated/enabled) can be converted using recirculation. The value must be held--explicitly recirculated when the clock is conditioned off. For example:

```
   \TLV
      \SV_plus
         wire gated_clk = clk & $en;
         always_ff @(posedge gated_clk)
            $$foo = $bar;
```

becomes:

```
   \TLV
      <<1$foo = $en ? $bar : $foo;
```

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: For Loop Assignments to TLV Scoped Assignments

Summary: Convert assignments in loops to TL-Verilog.

For this (very complex) task, it is important to also be familiar with the instructions already completed for the prior task, "Simple Signal Assignments to TLV Pipesignal Assignments". It would be good to read or reread them now, then reread this task.

In this task, you will translate `for` loops to TLV scopes and convert the assignments within the for loop to TLV assignments within the new scopes.

Verilog has generate `for` loops and procedural `for` loops (within an `always` block). They assign signals that may be declared as arrays outside the loop and reference within the loop with an array index (often the loop index). Or signals may be declared within a generate loop and naturally replicated by that loop. Any of these scenarios is coded the same in TL-Verilog. The pipesignal will be assigned in (and scoped to) a replicated scope, e.g., `/loop[upper:lower]`. Upper and lower bounds must be Verilog expressions that are constant at Verilog elaboration time.

For this code:

```tlv
   |default
      @0
         \SV_plus
            logic [7:0] foo [3:0], bar;
            genvar i;
            for (i = 0; i < 4; i++) begin: ii
               assign foo[i] = bar + i;
            end
```

the `for` loop and it's assignment become:

```tlv
\TLV
   |default
      @0
         /ii[3:0]
            $foo[7:0] = bar + i;
         \SV_plus
            logic [7:0] bar;
```

After converting the assignment, all references to the new pipesignal must be updated. This includes ones in the `\SV_plus` block as well as ones in TLV-style assignments.

All pipesignal references within the `\SV_plus` block are relative to the scope of the `\SV_plus` block (so `|default@0`). An updated reference might need to be, e.g. `/loop[i]$foo`, referencing into the new replicated TLV scope, indexed by a Verilog expression. Continuing with the above example, a reference to `foo` in:

```
         \SV_plus
            assign last = foo[3];
```

would become:

```
         \SV_plus
            assign last = /ii[3]$foo;
```

References to `foo` from TLV assignments would similarly reference through this scope. TLV assignments might be in a scope of their own. In this case, the new TLV reference must begin with `|default`, a common ancestor scope, so, e.g., `|default/ii[x]$foo`. So,

The right-hand side of the new assignment needs consideration as well. The new assignment has different scope in TLV as well as in Verilog. Right-hand-side references to other signals and pipesignals must be updated to reference through proper TLV or Verilog scope. For example, the refactored `valid`/`$valid` assignment below references a pipesignal and a Verilog signal:

```
\TLV
   |default
      @0
         /elsewhere
            $valid = ...;
         /core[NUM_CORES-1:0]
            // NEW:
            $valid = |default/elsewhere$valid || | core[#core].disabled;
         \SV_plus
            for (x = 0; x < 8; x++) begin: core
               logic disabled;
               // OLD:
               //valid = /elsewhere$valid || | disabled;
               assign disabled = ...;
            end
```

`|default/elsewhere$valid` begins with the common ancestor scope `|default`, and `core[#core].disabled` references into the Verilog scope. `#core` is a TL-Verilog mechanism to access the scope index of `/core` (within `/core`).

Note a current limitation of SandPiper. The scope (`/core`) must be defined prior to any references to the scope, thus, something like the following might be necessary:

```
\TLV
   |default
      @0
         /core[NUM_CORES-1:0]   // define
         /elsewhere
            $valid = /core[0]$something;
         /core[*]    // "[*]" uses range defined above
            // NEW:
            $valid = |default/elsewhere$valid || | core.disabled;
```

You are likely to see ternary expressions in the loop bounds. Note that, when using these in the scope range, the `:` from the ternary expression must not be interpreted as a range separator and must be escaped as `\:`. For example:

```
   |default
      @0
         \SV_plus
            genvar gen_n_gt1;
            logic foo;
            for (gen_n_gt1 = N <= 1 ? 1 : 0; gen_n_gt1 < 1; gen_n_gt1++) begin: nn_gt1
               foo = $bar;
            end
```

Becomes:

```
   |default
      @0
         /nn_gt1[0 : N <= 1 ? 1 \: 0]  // <-- escaped ":"
            $foo = |default$bar;
```

Update match statements in `fev.eqy` accordingly, e.g.:

```
gold-match ii[*].foo |default/ii[*]<>0$foo
```

Whether originally blocking or non-blocking, the match statements will use `<>0`.

You may notice generate `for` loops that evaluate 0 or 1 times (converted in a prior task from generate `if` blocks). These are to be included for refactoring in this task. Zero-replica scopes in TL-Verilog aren't really supported, but they will work, and we'll eliminate them soon. They may result in unused Verilog declarations, but these shouldn't cause any harm.

This is a complex task, so tackle each signal independently until successful patterns are clear.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Non-vector Signals

Summary: Non-vector signal types are awkward in TL-Verilog; convert these to pipesignals within `\SV_plus`.

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
            assign $$foo.field1 = $bar;   // First assignment requires "$$", no range.
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
         $blah <= reset ? '0 : choice ? $foo : $blah;
```

For signed signals, it is usually easier to convert them to normal pipesignals and use `\$signed(...)` where they are used instead of defining an unsigned type for them.

Update the `[match ...]` section of `fev.eqy` for these name changes. The proper syntax for this has not been worked out, so see if you can do so, and report your findings to the user.

After this task most if not all signals are probably converted to pipesignals. Other scenarios should be reported to the user before continuing.

There should be little, if anything, remaining in `\SV_plus` context when this task is complete. Exceptions include:

- instantiations of external components (other modules, functions, and Verilog macros)
- `struct` and `union` types with separate field assignments
- small generate `if`/`else` blocks (where each case assigns the same set of signals to values assigned by different scopes, each replicated 0 or 1 times).
- initialization, such as `initial foo = 1'b0;` or `logic foo = 1'b0;`.

If anything else remains in `\SV_plus`, see if you can figure out how to migrate it to `\TLV` context. Review task instructions to find clues. For anything you cannot migrate, describe the difficulty in `tracker.md`.

For Verilog declarations contained within an M5 conditional, e.g., within a block beginning `m5_if_eq_block(m5_cond_w_1, 1, ['`, apply similar M5 conditioning to the declaration in `\TLV` context.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Convert Remaining Signals to Pipesignals

Summary: Convert remaining signals to pipesignals.

In this task you will convert all remaining internal (non-module-interface) Verilog signals to pipesignals. If all signals (except `clk`) have already been converted, you may skip this step.

To SandPiper, an `\SV_plus` block is a single statement with zero or more assigned pipesignals and zero or more used pipesignals. SandPiper does not parse the Verilog syntax, and requires explicit syntax to identify which pipesignals are assigned by the block. One occurrence of each assigned pipesignal must identify the pipesignal as being assigned by the block by using a `$$` prefix. This occurrence must also provide the bit range of the pipesignal (unless boolean). Do not use `$$` for an initial assignment (whether using the `initial` keyword, e.g., `initial $foo = 1'b0;` or inline, e.g., `logic $foo = 1'b0;`). Other pipesignal references are interpreted as uses (including non-first assignments, and that's okay).

For example:

```tlv
   \SV_plus
      logic [WIDTH-1:0] cnt;
      if (WIDTH > 1)
         always_ff @(posedge clk)
            cnt <= 0;
      else
         always_ff @(posedge clk)
            cnt <= reset ? 0 : cnt + 1;
```

becomes:

```tlv
   \SV_plus
      if (WIDTH > 1)
         always_ff @(posedge clk)
            $$cnt[WIDTH-1:0] <= 0;
      else
         always_ff @(posedge clk)
            $cnt <= reset ? 0 : $cnt + 1;
```

Signals assigned by an instantiated module, function, or macro are handle the same. (They are given a `$$` prefix and a range expression if non-boolean.) It may not be syntactically clear which signal arguments are inputs vs. outputs, so further investigation may be necessary for these.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Review Commenting and Structure

Summary: Ensure that the current code is organized and commented consistently with the prepared code.

Compare the structure and commenting of `prepared.sv` with that of `wip.tlv`. Make any adjustments necessary to reasonably align the structure and commenting of `wip.tlv` with that of `prepared.sv`. The code may have been substantially reordered during conversion, and the order should be reestablished. Preserve comments like `// if (cond)` above replicated scopes, as these are used by subsequent tasks. Balance the alignment goal with the goal of quality, favoring alignment where there is not a significant quality concern. A slight increase in commenting may be reasonable, where there is a particular need. No comments should be lost or modified without a very clear reason.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Consolidate the SV-TLV Interface

Summary: Isolate the transition from Verilog to (timing-abstract) TL-Verilog and back.

Module input and output signals (as well as any other signals that you were unable to translate to pipesignals) may currently be used throughout the logic. Consolidate the connections of SV signals to and from TLV pipesignals, and eliminate the use of Verilog signals from logic expressions. New intermediate pipesignals can be defined and assigned to/from the corresponding SV signals.

Assign new input pipesignals at the top of the first (and probably only) `\TLV` region (part 1). Assign Verilog output signals at the end of the last (and probably only) `\TLV` region (part 2). Add an appropriate comment line above each of these sections. The input and output assignments should simply connect signals to/from pipesignals. They should not include logic. Replace all previous direct uses of the i/o signals with the pipesignals.

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

Do not create `$clk`. `clk` remains a Verilog signal, used implicitly.

Once fully refactored, all logic should be between the input and output assignment sections and should contain no Verilog signals. Highlight any deviations in `tracker.md`.

Before introducing new pipesignals, verify that they are compliant with naming methodology by using the script `rename_sigs.py`. For example, to test the names `$i_foo` and `$o_bar`, run `./scripts/rename_sigs.py -t i_foo o_bar`. (For full usage, run `./scripts/rename_sigs.py -h`.) (For these, `$foo` and `$bar` are recommended, instead.)

FEV may present difficulties when replacing the use of output signals in expressions with the new intermediate pipesignals. Outputs are cut points for EQY, and the fanin cone of an expression is cut by its use of the output signal, but the gate model will not be cut by the intermediate TL-Verilog signal.

Take a very incremental approach with such cases. Replace internal uses of output signals one-by-one. Merge output partitions using commands in the `[collect *]` and/or `[partition *]` sections, such as:

```
[collect *]
# A very heavy-handed group-everything.
group *
```

or

```
[partition *]
# Merge partitions selectively.
merge /^(out1|out2|...)$/
```

or

```
[partition *]
# Merge all outputs (for a design with a o_* naming convention).
name outputs /^o_/
```

Be sure to include in the unified partition the gold output signal that is replaced and any other output signals whose fanins include the modified expression.

This task is successful only if there is no longer any use of Verilog signals in logic expressions (only in the input/outuput connections sections).

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


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
         // TL-Verilog logic (including any logic you were unable to migrate out of \SV_plus)
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

- The macro parameter `/_top` can be used in pipesignal references to reference the scope in which the macro is instantiated. It may not be needed, but should be provided regardless to abide by conventions. `/top` is passed into `/_top`, identifying the implicit top-level `/TLV` scope.
- `m5+foo(/top)` is instantiated at the top level within the `\TLV` region. The macro argument references the scope of the instantiation, which, in this case, is the implicit `/top` scope.
- Check to be sure you didn't lose indentation. This tends to happen sometimes. The macro body should be indented (3-spaces) beneath `/TLV ...`.

It is probably easiest to tackle this in one shot, but, if you have difficulty, you can approach this incrementally, by first putting an empty macro in place, then, incrementally moving content from the `\TLV` body into the new macro. If there are M5 `m5_if_else` sections or TLV scopes, you'll have to be careful about preserving proper context. You can first split scopes in `\TLV` context, then migrate.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Review and Prepare Code for Handoff

Summary: Review the code and improve its quality for final handoff to the user.

To wrap up, compare your final code against `prepared.sv`. Compare the organization and commenting of you code versus `prepared.sv`.

Refactor your code such that:

- logic is expressed in optimal ways for readability and minimal redundancy
- all comments are appropriately preserved from `prepared.sv`, including the license header if present
- a note, such as "Converted to TL-Verilog by Claude.", is added (after the license, if present)
- the code is well organized and its structure closely aligns with the original
- the code follows best practices and has high quality
- whitespace is used appropriately for best readability

Give `fev_full.eqy` a final review, ensuring that the configuration that is used will result in adequate FEV coverage. Ensure that other fev_full_*.eqy also follow a sound approach.

If any changes are made, rerun `fev.sh`.


## Task: Prepare Tracker for Handoff

Summary: Prepare `tracker.md` for handoff to the user

Give `tracker.md` one final review and cleanup. Ensure that it is succinct, complete, accurate, properly formatted as Markdown, and useful to the user to review your work and address remaining issues.

Declare success only if:

- `fev.sh` passed for all FEV runs
- `fev*.eqy` are sound in their methodology
- all conversion steps substantially met their goals

Bring every shortcoming or concern to light. Have the mindset of a verification engineer. `tracker.md` should not recount the successes, only highlight areas of concern. Mere progress tracking can be removed. It is understood that all tasks were completed unless otherwise noted.

Assess the impact that your conversion had and incorporate this into `tracker.md`. Did the code grow or shrink, and why? What about just the TLV macro versus the original module? Does TLV context provide more or less structure? Also assess obstacles to further optimizations. Suggest further optimizations the user might want to consider, if any, and explain why you were unable to make these optimizations yourself, such as functional change that couldn't be FEVed. Reflect these in `tracker.md`.

Run `fev.sh` again, unless you are certain it was already run successfully, and CONGRATULATIONS ON COMPLETING YOUR ASSIGNMENT!!!


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


## Task: Refactor TLV

Summary: The definition of this task is still work-in-progress, but general suggestions are provided that you may find helpful to further improve the TL-Verilog code.

Mmmm.... just skip this step. There are several more.

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


Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: When Conditions

Non-blocking assignments that use a conditioned clock (gated/enabled) can be converted using when conditions. A pipesignal must exist or be created for the condition. For example:

```
   \TLV
      \SV_plus
         wire gated_clk = clk & $en;
         always_ff @(posedge gated_clk)
            $$foo = $bar;
```

becomes:

```
   \TLV
      ?$en
         <<1$foo = $bar;
```


# ARCHIVE


## Task: Generate If to For

Summary: Prepare generate if blocks for conversion.

THIS TASK IS BEING ELIMINATED. STOP WORKING.

If no generate `if` blocks remain in the design, you may skip this step. (Note that the `generate` keyword is optional in SystemVerilog.)

Let's consider the following generate `if` block. (This example was used in the previous task as well, though the previous task may not have converted it.) It performs a cyclic find-first, assigning `o_next_mask` (`logic [N-1:0]`), based on a valid mask `logic [N:0] i_valid_mask` and an encoded current index `logic [$clog2(N)-1:0] i_current`. The `if`/`else` block treats the degenerate `N=1` case specially.

```
if (N <= 1) begin: nn_eq1
   assign o_next_mask = {N{1'b0}};
end else begin: nn_gt1
   logic [N-1:0] valid_hi;
   assign valid_hi = i_valid_mask & ~( (1 << i_current) - 1);
   assign o_next_mask = | valid_hi ? find_first(valid_hi) : find_first(i_valid_mask);
end
```

Note that in SystemVerilog, `generate` and `endgenerate` are optional.

Generally, for code construction like this in TL-Verilog, we would employ M5. For now, though, we want to preserve the module functionality, configured by its parameters, so we'll use some awkward tricks.

Generate `if` blocks do not have a direct analogy in TL-Verilog. `for` loops do. And we can express `if` blocks using `for` loops that evaluate 0 or 1 times.

### Part: Use Separate If Blocks for Outputs

Generate `if` and `else` blocks will assign signals that are declared outside the blocks as well as inside. These are essentially the outputs of the conditional blocks, while the internal assignments feed into these output assignments. Block outputs will be assigned by different blocks under different configurations--in clean code, by exactly one block for any legal configurations.

We want our new `for` loops to only assign locals, so first pull block output assignments into their own `if`/`else` blocks (if there are any). Keep as much local as possible, so create local intermediate signals (e.g., `next_mask_n_gt1`, below) where reasonable. For example:

```
// (from original else block)
if (N > 1) begin: nn_gt1
   logic [N-1:0] valid_hi, next_mask_n_gt1;
   assign valid_hi = i_valid_mask & ~( (1 << i_current) - 1);
   assign next_mask_n_gt1 = | valid_hi ? find_first(valid_hi) : find_first(i_valid_mask);
end
if (N <= 1) begin: nn_eq1_out
   assign o_next_mask = {N{1'b0}};
end else begin: nn_gt1_out
   assign o_next_mask = nn_gt1.next_mask_n_gt1;
end
```

Note that reaching across the blocks requires the addition of the scope (e.g., `nn_gt1.`) to references. Since these references are to signals that only exist for certain configurations, it is not possible to convert the lower `if` block to a ternary expression (that would exist for all configurations).

Since we kept the name of the `nn_gt1` block, and the new `nn_eq1_out` block contains no signal declarations, there is no need for any match updates above.

### Part: If to For

Now the local-only `if`/`else` blocks can be converted to `for`:

```
// if (N > 1)
genvar gen_n_gt1;
for (gen_n_gt1 = N <= 1; gen_n_gt1 < 1; gen_n_gt1++) begin: nn_gt1
   logic [N-1:0] valid_hi, next_mask_n_gt1;
   assign valid_hi = i_valid_mask & ~( (1 << i_current) - 1);
   assign next_mask_n_gt1 = | valid_hi ? find_first(valid_hi) : find_first(i_valid_mask);
end
// (This cannot become a ternary expression)
if (N <= 1) begin: nn_eq1_out
   assign o_next_mask = {N{1'b0}};
end else begin: nn_gt1_out
   assign o_next_mask = nn_gt1[0].next_mask_n_gt1;
end
```

This for loop defines `nn_gt1[0]` if `N` > 1 and nothing otherwise. References that were `nn_gt1.` become `nn_gt1[0].`. Signals declared within the loop change scope, so this must be reflected correctly in `fev.eqy` and any differently-configured `fev_full_*.eqy`.

The comment, `// if (N > 1)`, above, will be helpful to future tasks, so provide such comments.

Be sure all changes for this task have been completed fully and that `./scripts/fev.sh` passes before reviewing `instructions/desktop_agent_instructions.md` and running `./scripts/get_task.py next`. If the task was not fully successful, wrap-up, update the user, and stop working, awaiting user guidance.


## Task: Pass Module Parameters to TLV Macro

Summary: Introduce parameters to the TLV Macro for module parameters.

If the module has no parameters, you may skip this task.

Pass the names of module parameters into the TLV macro, adding parameters to the TLV macro, and arguments to its instantiation. For example:

```
\TLV dut(/_top, #_width, _target)
   ...
\SV
module dut
  #(parameter WIDTH = 1,
    parameter TARGET = "FPGA")
  ...
\TLV
   ...
   m5+dut(/top, WIDTH, TARGET)
   ...
```

For numeric parameters...

## Task: Pass M5 Configuration as TLV Macro Arguments

Summary: Introduce parameters to the TLV Macro for M5 configuration variables.

...

## Task: Create TLV Macro for TLV Use

Summary: Create a TLV macro wrapper around the existing TLV macro that requires parameters to be elaborated by M5, not given as module parameter names.

...

## Strategy Notes for Integration Modules

- Convert to TLV
- Include TLV code as local libraries
- For each submodule:
  - update the submodule's conversion work to incorporate any 
  - convert to TLV macros, incorporating 

## Appendix: Known Failure Patterns (from serv_immdec analysis)

**Scope condition polarity (Class A):** When creating a TLV hierarchy
scope for a parameter-conditional generate block, the scope condition
must match the block's actual if-condition, not the compiled
for-generate loop's start value, which often uses inverted polarity.
Example: `if (W == 1) begin : gen_w_eq1` must produce
`/gen_w_eq1[W == 1 ? 0 \: -1 : 0]`, even though the compiled loop
reads `for (gen_w1 = (W != 1); ...)`. Double-check against the
original if-condition before running FEV.

**Shift-register chains (Class C):** Before converting an if/else
block to ternary, check whether any signal in the block is read by
another signal's assignment in the same always block (a dependency
chain). If so, do not convert those specific signals to standalone
ternary — leave them as if/else and note this as an intentional
exception, not a failure to retry.

**Duplicate assignment after refactor (Class B):** After adding any
new assignment for a signal, verify the old assignment for that same
signal was removed from the same always block. A signal name should
appear as an assignment target exactly once per block.
