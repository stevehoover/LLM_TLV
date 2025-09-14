# Tasks for LLM-assisted Verilog to TL-Verilog Code Conversion

These tasks define a process for converting Verilog to TL-Verilog. An overview of the conversion process should have been provided in this Project/GPT's instructions.

## Task: Preparation

If asked to continue a conversion that has already been started, assess the current progress in the status and tracker artifacts as well as reviewing the current code, and skip ahead to the appropriate task.

When starting fresh, prior to the first refactoring task, assess the job. Determine any necessary assumptions, issues, and limitations, if any. Potential considerations are described here. Capture these in a new tracker artifact, titled "Conversion Tracking for <module-name>".

### Single File

The MCP tools require the top-level module definition to be encapsulated in a single file. This includes any submodules, functions, and macro definitions that might be instantiated by the module.

### Parameters

FEV must be run on a specific configuration of the module. It is generally recommended to preserve the parameterization through the conversion, but typically FEV only the default configuration at each refactoring step. Other parameter values can be tested and debugged after the conversion.

Other parameter values can also be verified as desired along the way, especially when a refactoring step involves parameterized code. Test alternate configurations before and after such refactoring. Make a separate artifact file for each configuration, containing a wrapper module defining the same interface, but calling the main module with specific parameter values. Incorporate the parameter values in the wrapper module name. Run FEV on the wrapper, providing combined code to the FEV tool.

### Latch-based Design

It is expected that the original design is flip-flop-based, triggered by the rising edge of the clock. If logic is driven by the falling edge of the clock, it may be converted to transition a phase earlier or later as long as the output timing is preserved for FEV. Any changes like this that may impact the nature of the physical implementation should be noted in the tracking artifact.

### Prepare the Code

Prepare the initial module artifact from the code you are given. Report any missing subcomponents and definitions to the user. If any modifications are necessary from the given code, report them in the tracking artifact and to the user. This establishes the baseline code that you will convert. Henceforth, all modifications MUST PASS FEV.


## Task: Reset and Clock

TL-Verilog works with a global (free-running) clock, called `clk`. If the Verilog code uses a clock by a different name, assign it to a new `clk` signal, and update the code to use `clk` instead.

TL-Verilog code conventionally uses a positively-asserted synchronous reset signal, called `reset`, and FEV configurations may assume this name. If the module has a reset by a different name, negatively-asserted, or asynchronous, create the necessary `reset` signal (internally), and update the code to use it. If the module reset is asynchronous, note this in the tracking artifact, as FEV will assume it to be synchronous.


## Task: TLV File Format

Convert the code to TLV file format. The code can all be in one big `\SV` region initially, so this can be as simple as prepending these two lines:

```tlv
\TLV_version 1d: tl-x.org
\SV
```

Next, convert the top module body to an `\SV_plus` region. Remember, region identifiers are not indented.

In an `\SV_plus` region, `/` is an escape character, forcing the next character to be interpreted literally. Symbols used in TLV identifiers will require `\` to avoid special interpretation only if followed immediately by word characters. This includes `$`, `@`, `|`, `/`, `#`, `%`, and `\`. These doesn't tend to occur often in practice and are most common in test bench and logging code. Test bench code should not be included. Common scenarios to look out for include `$display`, `%s`, and `@10`. These must be translated to `\$display`, `\%s`, and `\@10` to transition `\SV` to `\SV_plus`.

All changes must be FEVed before proceeding.


## Task: Signal Naming

Rename Verilog signals to names that are legal pipesignal names. (We will not use TLV state signals, only pipesignals.) Pipesignal names are limited to using lowercase ASCII letters, digits, and underscores. They are comprised of tokens, that are separated by `_`. Each token is a string of 1 or more letters, followed by 0 or more digits. The first token must begin with at least two letters. Example name mappings:

- `no_change` -> `$no_change`
- `a` -> `$aa`
- `o_result` -> `$oo_result` (or, if `o_` indicates output, it's not important; so `$result`)
- `product_1_NRE` -> `$product1_nre`
- `Opcode_0b01011` -> `$opcode_01011`
- `is_VERSION_1_0` -> `$is_version1_dot0`
- `regA_EXE_2` -> `$reg_a_exe2`

Apply these conventions to `genvar`s as well.

All changes must be FEVed before proceeding.


## Task: Signals to Pipesignals

In this task, you'll convert Verilog signals to TL-Verilog pipesignals. Begin with signals defined at the top-level (not within a generate block), limiting yourself to those that are simple bit vector signals. These are converted as follows:

- Add a `$` prefix to the name everywhere.
- Identify the first assignment of the signal/pipesignal. (Often there is only one, but there might be multiple in an `if` chain or `case` statement.) This occurence defines the type and that the signal is assigned by the `\SV_plus` block. Use a `$$` prefix instead of `$` to denote assignment, and add the vector bounds to declare the type. Verilog expressions (elaboration-time constant) may be used for bounds.
- Non-blocking assignments (`<=`) (which should be in `always_ff` or `always @(posedge clk)` blocks) are assigning the next value of the pipesignal, thus prepend `<<1` to the pipesignal name to indicate this timing.
- Remove the Verilog signal declaration.

Note that the `\SV_plus` region is not explicitly part of a pipeline, and is therefore in stage 0 of a default pipeline. So, the pipesignal references you are creating are relative to stage 0 of a default pipeline. For now, this is best. We'll introduce explicit pipelines later.

For example:

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
         <<1$$cnt[WIDTH-1:0] <= 4'b0;
     else
         <<1$cnt <= $cnt + 1;
```

Signals with complex types (non-bit-vectors) or signed values require special consideration (in the next task). For this tast, leave them as Verilog.

Replicated signals require special consideration and should probably be converted in a separate step. Most replicated signals are replicated by for loops with elaboration-time-constant bounds. Other scenarios are not considered here and may require user intervention.

A replicated signal may be assigned within a `generate for` loop or within a for loop within an `always` block. Those in generate for loops may be declared as arrays outside the loop and reference within the loop with an array index (often the loop index). Or signals may be declared within the loop and naturally replicated by the loop. Any of these scenarios is handled the same in TL-Verilog, and the corresponding pipesignal is referenced the same way. The pipesignal will exist in a replicated scope, e.g., `/loop[upper:lower]`. Upper and lower bounds must be elaboration-time constant and can be integers or Verilog expressions. The pipesignal reference within the loop will include the scope and its index, e.g. `/loop[ii]$foo`. For example:

```tlv
\SV_plus
   logic [7:0] foo [4:0];
   logic [7:0] bar;
   genvar ii;
   for (ii = 0; ii < 4; ii++)
      assign foo[ii] = bar + ii;
```

becomes:

```tlv
\TLV
   /ii[3:0]
\SV_plus
   logic [7:0] bar;
   genvar ii;
   for (ii = 0; ii < 4; ii++)
      assign /ii[ii]$$foo[7:0] = bar + ii;
```

Note that the scope (`/ii`) must be defined in a preceding `/TLV` region. If the assignment were non-blocking, the reference would use `<<1`, as `/ii[ii]<<1$$foo[7:0]`. And, of course, right-hand-side uses would not need double-`$` nor the bit range (`/ii[ii]$foo`) (unless extracting a subrange of bits).

Some (non-generate) loops might update the same signal in each iteration. These would generally, be termed "reduction" operations. One pattern for translating these is exemplified below:

```tlv
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
   /ii[3:0]
\SV_plus
   always_comb begin
      for (integer ii = 0; ii < 4; ii++)
         /ii[ii]$$partial[31:0] = (ii == 0) ? 0 : $partial[(ii+4-1)%4] + $addend[ii];
      $$sum[31:0] = $partial[3];
   end
```

In Verilog, it is legal to assign different portions of a vector signal in separate assignments. This is not permitted in TL-Verilog. Likely, a combined assignment can be created by simply concatinating the expressions. If the individual assignments are complex, an intermediate signal can be introduced to hold the partial expression that is then concatenated. For example:

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
   assign $addr_b31_b12[31:12] = <complex_expression>;
   assign $addr[31:0] = {$addr_b31_b12, page_addr};
```

All changes must be FEVed before proceeding.


## Task: Non-vector Signals

Signals with complex types (non-bit-vectors) or signed values must use Verilog-defined types (or enums). A separate statement in a `\TLV` region is necessary to declare the pipesignal's type, using a `**` prefix on the type, as illustrated below.

For verilog `foo` in:

```tlv
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
\tlv
   **foo_t $foo;
...
\SV_plus
   assign $$foo.field1 = $bar;
   assign $foo.field2 = $baz;
```

Verilog type `foo_t` would be defined in an `\SV` or `\SV_plus` region.

Note that the multiple field assignments to `$foo` will remain in an `\SV_plus` block throughout the conversions. These cannot be converted to native TLV assignments.

For signed signals, it is usually easier to convert them to normal pipesignals and use `\$signed(...)` where they are used instead of defining an unsigned type for them.

After this task most if not all signals are probably converted to pipesignals. Other scenarios should be left as Verilog signals.

All changes must be FEVed before proceeding.


## Task: If/Else and Case to Ternary

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
            <<1$$yy <= $bb;
         else if ($cond2)
            <<1$yy <= $cc;
         else begin
            <<1$yy <= $dd;
            <<1$$zz[7:0] <= $ee;
         end
      else
         <<1$yy <= $ff;
      end
   end
```

Note that `<<1$yy` is assigned under all conditions, but `<<1$zz` is not and must be retained when not assigned.

This example can be transformed incrementally, first transforming the inner assignment of `<<1$yy`:


```tlv
\SV_plus
   always_ff @(posedge clk) begin
      if ($valid) begin
         <<1$yy <=
              $cond1 ? $bb :
              $cond2 ? $cc :
                       $dd;
         if ($cond1) begin
         end else ($cond2) begin
         end else
            <<1$$zz[7:0] <= $ee;
      else
         <<1$yy <= $ff;
      end
   end
```

Note that the empty conditions, above, are acceptable, but `begin`/`end` must be added.

Continuing to refactor `<<1$yy` and `<<1$zz`:

```tlv
\SV_plus
   always_ff @(posedge clk) begin
      <<1$yy <=
           $valid ?
              $cond1 ? $bb :
              $cond2 ? $cc :
                       $dd :
           //default
              $ff;
     if ($valid && (! $cond1 && ! $cond2))
        <<1$$zz[7:0] <= $ee;
   end
```

Then to refactor `<<1$zz` to use a ternary expression, we must explicitly recirculate the previous value of `<<1$zz`, aka `$zz`.

```tlv
      <<1$zz[7:0] <= $valid && (! $cond1 && ! $cond2) ? $ee : $zz;
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

If you have trouble getting the assertion correct, make a note of the potential checking/synthesis implications in the tracking artifact.

All changes must be FEVed before proceeding.


## Task: Migrate from `\SV_plus` to `\TLV`

In this task, expressions are transitioned from `\SV_plus` context to `\TLV` context. Pipesignals will remain in the default (implicit) pipeline for this task. There should not currently be, and will not be after this task, any use of the TLV pipeline construct (e.g. `|pipe`) nor the pipestage construct (e.g. `@3`) yet. Just like the `\SV_plus` region, `\TLV` expressions will be in stage 0 of the default pipeline implicitly.

Unless you had difficulty, all pipesignals should now have a single assignment, whether by an `assign` statements, in an `always_comb` block, or in an `always_ff` block. When refactored to `\TLV` context, all pipesignals will be assigned in `\TLV` context using a simple `=` assignment, and their `$$` will be dropped (for `$`).

For `assign`s, in `\TLV` context, the `assign` keyword is dropped and the rest is unchanged.

Assignments within `always_comb` can be translated to `assign`s, then converted to `\TLV` syntax.

`always_ff` assignments, should be using `<<1` and non-blocking `<=`. They will retain the `<<1` (because they still assign the next value), but use `=` assignment in `\TLV` context. They become individual assignments like the others, with no `always_ff`.

For example:

```
\SV_plus
   $$foo = $bar ^ $blah;
   always_ff @(posedge clk)
      <<1$$cnt[31:0] <= reset ? 0 : $cnt + 1;
```

```
\TLV
   $foo = $bar ^ $blah;
   <<1$cnt[31:0] = reset ? 0 : $cnt + 1;
```

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

Any uses of external components (other modules, functions, and Verilog macros) should remain in `\SV_plus` context. Also, `struct` and `union` types with separate field assignments will remain in `\SV_plus`. If anything else remains in `\SV_plus`, see if you can figure out how to migrate it to `\TLV` context. For anything that remains in `\SV_plus` context, add code comments to explain the difficulty.

All changes must be FEVed before proceeding.


## Task: Consolidate the SV-TLV Interface

Module input and output signals as well as any other signals that you were unable to translate to pipesignals may be used throughout the logic. It would be cleanest to consolidate the connections of SV signals to and from TLV pipesignals. New pipesignals can be defined for this and assigned to/from the corresponding SV signals.

Assign new input pipesignals at the top of the first (and probably only) `\TLV` region. Assign Verilog output signals at the end of the last (and probably only) `\TLV` region. Replace all previous direct uses of the i/o signals with the pipesignals. Once fully refactored, the internals of the `\TLV` region(s) ideally contain no Verilog signals, and are safely retimeable (aka timing abstract).

Though not required, using a `*` prefix before Verilog signal names is suggested, so tools (SandPiper) can recognize them as Veriog signal references.

So, for example, this refactoring step should result in a structure like:

```tlv
\SV
   module foo(input wire clk, input wire reset, input wire in[7:0], output wire out[7:0]);
\TLV
   // Connect Verilog inputs:
   $reset = *reset;
   $in[7:0] = *in;

   ...
   
   // Connect Verilog outputs:
   *out = $out;
\SV
   endmodule
```

All changes must be FEVed before proceeding.


# Task: Refactor TLV

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

=======================================


All changes must be FEVed before proceeding.


### Task: Final Testing and Debugging

Review your translated code for quality and correctness and make improvements where possible. FEV should ensure correctness, but it never hurts to double check. Compare your final code against the original. Ensure that all comments are appropriately preserved. Ensure that the code is well organized and that its structure closely matches the original. If any changes are made, FEV them. Assess the impact that your conversion had. Did the code grow or shrink? Does TLV context provide more or less structure? Also assess obstacles to further optimizations. Suggest further optimizations the user might want to consider, if any and explain why you were unable to make these optimizations yourself (likely that there would be functional change that couldn't be FEVed). Reflect these in the tracker artifact.

Ideally, you were able to run FEV for each refactoring step or task, proving that the prepared Verilog is functionally identical to your resulting TL-Verilog. To double-check your work, and to provide the user with clear evidence of equivalence, now FEV the final code versus the prepared Verilog (that resulted from the preparation step, ideally identical to the code given). If you are able to get this FEV to succeed, the user is assured of equivalence.

If the code is parameterized, it would be valuable to FEV the conversion for different parameter values as well (as described in the preparation step). This will further boost the user's confidence in the conversion. Update the tracker artifact to indicate all successfully FEVed parameter configurations.

Now, prepare your work for a clean handoff to the user. Give the tracker artifact one final review. Ensure that it is succinct, complete, accurate, and useful to the user to review your work and address remaining issues. Unless the prepared code and the final code were successfully FEVed, the conversion was, overall, unsuccessful. Bring every shortcoming to light. The worst possible outcome is that your efforts introduce a bug that goes undetected. Even an undetected functional difference or an implementation difference would be concerning. So, have the mindset of a verification engineer. If it can go wrong, it will. Sweep nothing under the rug. Raise all potential issues and concerns in the tracker artifact for handoff.
