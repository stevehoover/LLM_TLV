# FEV Failure Recovery Guide

This file documents common FEV failure patterns and their fixes.
Consult this file when `fev.sh` fails.

---

## Pattern 1: Missing Stage Alignment in EQY Match Lines

**When it happens:** During Signal Assignments task, when adding
a match line for a newly converted pipesignal.

**Error message from fev.sh:**
    "Cross-pipeline signal references require explicit alignment."
    SandPiper exits before EQY runs.

**Cause:** A match line written as `gold-match reset |default$reset`
is missing the required `<>0` stage alignment.

**Fix:** Change to `gold-match reset |default<>0$reset`

No TL-Verilog change is needed — this is a pure fev.eqy syntax fix.

---

## Pattern 2: Registered Output Used Internally — EQY Partition Conflict

**When it happens:** During Consolidate the SV-TLV Interface task,
when converting a signal that is both a module output port AND a
flip-flop register.

**Error message:**
    partition: ERROR: conflicting matches for gold bit \o_signal_name:
               \DEFAULT_signal_name_a0 vs \o_signal_name

**Cause:** In the original Verilog, the output port and the register
are one net. After conversion, the gate has two nets: the internal
flop (renamed by SandPiper, e.g. DEFAULT_ctrl_jump_a0) and the
output port buffer (o_ctrl_jump). EQY's automatic port-name matching
plus your explicit match line both try to map to the single gold net,
creating a conflict.

**Fix — keep the flop gold-named in \SV_plus:**

1. Compute the next value as a pipesignal:
   `$ctrl_jump_next = ($reset & ...) ? 1'b0 : ...;`

2. Keep the register in \SV_plus:
   `always @(posedge clk) o_ctrl_jump <= $ctrl_jump_next;`

3. For readback in logic:
   `$ctrl_jump = *o_ctrl_jump;`

4. Remove the explicit match line for this signal. EQY will
   auto-match `o_ctrl_jump` by name — no explicit match needed.

**Why this works:** Gold has one net (flop == port). Gate also has
one net (you kept the original name). EQY auto-matches by name,
no conflict.

**Known examples:** `o_ctrl_jump` in serv_state, `o_ibus_adr` in serv_ctrl.

**Last resort — if the above doesn't resolve it:**
Add `[collect *]\ngroup .*` to all fev_full*.eqy files. This collapses
the entire design into one partition. The proof still holds but
failure localization is lost — the whole module fails as one unit
rather than one signal. Prefer the named-output approach above.

---

## Pattern 3: fev.sh Silently Ignoring Malformed config.json

**When it happens:** Any time the agent generates config.json.

**Symptom:** FEV appears to pass, but only the default configuration
was actually verified. Non-default parameter configurations were
silently skipped.

**Root cause:** fev.sh passes config.json arguments to SandPiper via
`-iargs`. This flag downgrades unknown arguments from fatal errors
to non-fatal warnings, so malformed config.json causes SandPiper to
ignore the extra configurations without failing.

**How to detect:** After a conversion completes, manually check:
    cat config.json
Valid format:
    {
      "top": "module_name",
      "M5_configs": {
        "config_name": "-m5arg value"
      },
      "default_config": "config_name"
    }

If M5_configs is missing, wrong type, or incorrectly nested, the
non-default configurations were never verified.

**Fix:** fev.sh needs to validate config.json format before building
the command line. SandPiper "unrecognized argument" warnings should
be treated as fatal errors.

---

## Pattern 4: Output Signal Used Internally — Cut Point Asymmetry

**When it happens:** After Consolidate the SV-TLV Interface task,
when several outputs are also used in internal logic.

**Symptom:** EQY's automatic partitioning fails or produces
unexpectedly large partitions.

**Cause:** EQY uses output signals as natural partition cut points.
When the gold model cuts at an output but the gate model uses a
different internal pipesignal for the same logical point, the
partitions don't align.

**Fix — selective merge:**
Rather than `group .*` (which merges everything), selectively merge
only the affected output partitions:
    [partition *]
    merge /^(o_signal1|o_signal2)$/

This preserves granularity for unaffected partitions.

**Identifying affected signals:** Look for outputs that appear both
in the Connect Verilog outputs section AND in internal logic
expressions. Those are the ones causing the asymmetry.
