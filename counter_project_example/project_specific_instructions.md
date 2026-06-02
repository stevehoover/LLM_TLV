# Project-Specific Conversion Instructions: counter

## Overview
Single-module, single-file design: an 8-bit synchronous counter with synchronous,
active-high reset. This is the simplest possible conversion case — no libraries, no
generated CSRs, no parameters, no clock gating, no tri-states.

## Module
- File: `counter.v` (project root, `/workspace/proj/counter.v`)
- Module: `counter`
- Ports: `clk` (input), `reset` (input), `count[7:0]` (output reg)
- Behavior: `always @(posedge clk)` — on reset `count <= 0`, else `count <= count + 1`

## Analysis
- **Include/library paths:** None. The module is fully self-contained; no `include`
  paths are needed for Yosys/SandPiper to read it.
- **Generated code:** None in the source. (SandPiper *output* files are listed below.)
- **Parameterization:** None. No tick-defines or module parameters. The 8-bit width
  is hard-coded; nothing to choose at test time.
- **One module per file:** Satisfied — `counter.v` defines exactly one module.
- **Latches:** None. Pure flip-flop logic on the rising edge of `clk`.
- **Clock gating/enabling:** None. Single ungated clock; no `when`/`?$valid` needed.
- **Tri-states:** None.

## TL-Verilog Notes
- The `always @(posedge clk)` register maps directly to the `>>1$count` staging pattern.
- Reset (active high) is the project's `*reset` input: it is a Verilog signal, not a TLV
  `$reset`, so reference it as `*reset` in the TLV.
- Conversion body (see `counter.tlv`):
  ```
  |count_pipe
     @1
        $count[7:0] = *reset ? 8'b0 : >>1$count + 8'b1;
        *count = >>1$count;
  ```
- Single pipeline stage `@1`; no additional stages required.
- **IMPORTANT — registered vs combinational output:** the original `count` is a
  *registered* port (`count <= count + 1`). Drive the output from the **staged** value
  `>>1$count`, not the live `$count`. Using `*count = $count` makes the output
  combinational (`registered_value + 1`), which leads the original by one cycle and is
  an FEV/sim mismatch (observed count=11 vs 10). With `*count = >>1$count`, SandPiper
  emits `assign count = COUNT_PIPE_count_a2;` (the flop) — cycle-accurate with the
  original (verified: identical `$monitor` traces, t=115 count=10).

## SandPiper Output (already generated — verified present)
Regenerate from `tlv/counter.tlv` with (output lands next to `-o`, plus a `_gen` companion):
```bash
cd /workspace/proj/tlv && sandpiper-saas -i counter.tlv -o counter_gen.sv --bestsv
```
This produces, in `tlv/`:
- `counter_gen.sv` — the translated SystemVerilog (the file that replaces `counter.v`).
  **Verified present** (`tlv/counter_gen.sv`), header confirms SandPiper 1.14 provenance.
- `counter_gen_gen.sv` — companion file with top-level signal declarations and the
  `always_ff` staging for `>>1$count`; it is `` `include ``-d by `counter_gen.sv`.
  Keep it alongside `counter_gen.sv`.

## Preparation (for conversion agent)
The design is self-contained — no special read/library setup. To validate the converted
design, the regression must compile the SandPiper output instead of the original
`counter.v`. Override the original by linking it to the generated SV (and keep the
companion include reachable from the project root):

```bash
cd /workspace/proj
ln -sf tlv/counter_gen.sv counter.v            # override original with converted RTL
ln -sf tlv/counter_gen_gen.sv counter_gen_gen.sv  # SandPiper `include companion
```

To restore the original RTL: `cd /workspace/proj && git checkout counter.v && rm -f counter_gen_gen.sv`.

## Regression
- **Command:** `tlv/regress/regress.sh`
- **What it does:** runs `verilator --binary --top counter_tb` over `counter.v` +
  `counter_tb.v` from `/workspace/proj`, builds `sim_counter`, runs it, and prints the
  last lines plus `REGRESSION PASSED`/`REGRESSION FAILED`.
- **Pass criterion:** simulation reaches `$finish` and `count` increments correctly
  (e.g. `t=115 reset=0 count=10`); script prints `REGRESSION PASSED` and exits 0.
- **Fail criterion:** Verilator compile error or wrong count → `REGRESSION FAILED`,
  non-zero exit.
- **Verification collateral to keep in sync:** `counter_tb.v` connects by port name
  (`.clk`, `.reset`, `.count`). The conversion preserves the module's port list, so the
  testbench needs no changes; only the internal RTL of `counter` changes.
- **Status:** Verilator regression confirmed working on the original RTL.
- **Debugging tip:** for full logs, run Verilator manually from `/workspace/proj`:
  `verilator --binary -j 0 --top counter_tb counter.v counter_tb.v -o sim_counter`,
  then inspect `obj_dir/`.
