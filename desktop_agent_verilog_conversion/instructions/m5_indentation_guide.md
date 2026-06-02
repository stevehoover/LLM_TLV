# M5 Macro Indentation Guide

## Critical: m5_if_eq_block Column Alignment

Assignments inside m5_if_eq_block MUST be at the SAME column as the macro.
Deeper indentation causes "signal never assigned" SandPiper errors.

**Wrong:**

**Correct:**

**Post-expansion (what SandPiper sees):**

The macro argument is inserted verbatim. The result must be valid TL-Verilog.

## Verification After M5 Changes

```bash
sandpiper-saas -i module.tlv -o out.sv --bestsv
```

"Signal never assigned" = indentation mismatch in macro argument.
