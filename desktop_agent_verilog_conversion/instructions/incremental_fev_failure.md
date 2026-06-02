# Incremental FEV Failure Guidance

Covers FEV failures during incremental steps (current TLV vs previous step).
See full_fev_failed.md for full FEV failures vs original.

## Most Common: NO-ALIGN

**Tag:** `NO-ALIGN`

**Cause:** Signal path in fev.eqy missing `<>0` transaction shift.

**Wrong:**

**Correct:**

**Best — use [collect *] when possible:**

## Python Version Error (rename_sigs.py)

**Symptom:** `SyntaxError: f-string expressions nested too deeply`
**Cause:** Requires Python 3.12+, container ships 3.11.
**Fix:** Use node:22-trixie-slim base image (Python 3.13) or rename manually.

## Pipeline Timing Offset (Registered vs Combinational Output)

**Symptom:** Regression passes but output value is off by one cycle.
Original shows count=10, converted shows count=11 at same timestamp.

**Root cause:** Using `*port = $signal` makes the output combinational
(next-value before the flop). Using `*port = >>1$signal` outputs the
registered value — cycle-accurate with the original.

**Wrong:**
```tlv
$count[7:0] = *reset ? 8'b0 : >>1$count + 8'b1;
*count = $count;        // combinational — leads original by 1 cycle
```

**Correct:**
```tlv
$count[7:0] = *reset ? 8'b0 : >>1$count + 8'b1;
*count = >>1$count;     // registered — matches original exactly
```

SandPiper output difference:
- Wrong:   `assign count = COUNT_PIPE_count_a1;`  (combinational)
- Correct: `assign count = COUNT_PIPE_count_a2;`  (the flop)

**Why simulation alone misses this:** If regress.sh only checks that
simulation reaches $finish without comparing output values, it will
report PASS even when the output is wrong. Always add golden checks.

## Debugging Strategy

1. Add `<>0` to match section signal paths
2. Try `[collect *]` with explicit bind
3. Check SandPiper output: `grep "assign" counter_gen.sv` — verify
   ports connect to `_a2` (registered) not `_a1` (combinational)
4. Run trace diff: compare $monitor output between original and converted
5. Search sandpiper_messages.md for error tag
6. Document all findings in tracker.md

## Error Tag Reference

| Tag | Meaning | Fix |
|-----|---------|-----|
| `NO-ALIGN` | Missing `<>0` | Add to match entries |
| `UNDRIVEN` | Signal not in TLV output | Check SandPiper names |
| `NO-MATCH` | Name mismatch | Check rename output |
| `MULTI-DRIVEN` | Duplicate assignments | Fix double assignments |
