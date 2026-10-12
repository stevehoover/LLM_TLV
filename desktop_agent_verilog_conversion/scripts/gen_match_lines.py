#!/usr/bin/env python3

# Mechanical enumeration and cross-check of fev*.eqy match lines.
#
# Usage: ./gen_match_lines.py --emit <fev*.eqy>
#        ./gen_match_lines.py --check <fev*.eqy>
# Run from the module work directory (alongside wip.tlv, prepared.sv, config.json).
#
# Both modes replay the .eqy file's [gold]/[gate] read commands and [script]
# transforms through yosys (the same view eqy matches on) and enumerate the
# named wires and registers on each side. Name-identical pairs need no match
# line.
#
# --emit prints a proposed [match] section: gold-only names are paired to
#   gate-only names by a conservative base-name heuristic where the pairing
#   is unambiguous, and listed as UNRESOLVED otherwise.
#
# --check compares the match lines present in the .eqy file against the
#   enumeration and exits 1 listing every disagreement:
#   - match lines whose gold name does not exist in the gold enumeration
#   - gate references (TL-Verilog or Verilog syntax) that map to no signal
#     in the gate enumeration
#   - gold registers with no name-identical gate partner and no match line
#     (state that would make FEV fail or pass vacuously)
#   - a wip.tlv that SandPiper refuses to compile; the compiler's own
#     diagnostic (e.g. the BAD-SCOPE line and the offending source line) is
#     the report, since a compile error in the edited source is a verdict on
#     the edit and needs no FEV run to discover
#   Exit 2 means the check itself could not run (missing tool, compile
#   service unreachable, elaboration failure); callers should treat that as
#   "no verdict", not as disagreement.
#
# The gate side is regenerated from wip.tlv with sandpiper-saas (mirroring
# fev.sh) into a temporary directory so the check reflects the current
# source. When sandpiper-saas is unavailable, the on-disk generated Verilog
# is used as-is. sandpiper-saas is a client for a network service, so its
# failures come in two shapes that are told apart by its output: a compile
# error carries SandPiper's banner and an `ERROR(n)`/`FATAL_ERROR(n)`
# diagnostic (exit 1 here), while a service failure ("Error while accessing
# the compile service.", "Error while extracting response.", a timeout)
# carries no SandPiper diagnostic at all (retried once, then exit 2).
#
# Gate-side names
# ---------------
# A gate reference in TL-Verilog syntax is mapped to the Verilog name
# SandPiper generates for it:
#   - each scope token of the path is CamelCased, dropping its underscores
#     (`/rf_ram_if` -> `RfRamIf`, `/inner_thing` -> `InnerThing`)
#   - each pipeline token is upper-cased (`|default` -> `DEFAULT`)
#   - the pipesignal name keeps its own case (`$o_wdata` -> `o_wdata`)
#   - the tokens are joined with `_` in path order, and a stage suffix
#     `_a<n>` or `_n<n>` may be appended
#     (`/rf_ram_if|default<>0$rgnt` -> `RfRamIf_DEFAULT_rgnt_n1`)
# The rule is applied exactly. A gate name that differs from the expected
# name only in case or underscores is not accepted: eqy sees the name
# SandPiper itself generates for the reference (map_match_pipesignals.py),
# and SandPiper resolves a reference to one signal or rejects it, never to a
# look-alike. Accepting a look-alike here would pass a match line that eqy
# then leaves unmatched, or that names a different signal ($rdata_0 for
# $rdata0, /rf_ramif for either of /rf_ram_if and /rfram_if). Such near
# misses are listed in the failure instead, so a wrong reference, or a
# drift in SandPiper's rule, is visible at once.
#
# A replicated scope gives the same signal a second name shape. By default
# the loop body is a named generate block `L<n>_<Path>` and the declaration
# inside it carries an `L<n>_` uniquifying prefix, so the hierarchical name
# reads `L1_Sort_Level[level].L2_PIPE_Pair[pair].L2_a_num_a1` rather than
# one joined path. Under `--fmtFlatSignals` the same signal is instead
# `Sort_Level_PIPE_Pair_a_num_a1[level][pair]`, one joined path with
# unpacked array dimensions. Both shapes are recognized, and reduce to the
# same joined path for comparison. The `L<n>` numbers derive from where the
# logic was declared in the source and are not stable across code motion,
# so they are stripped before comparison and an `L`-number change is never
# a mismatch by itself.
#
# When the gate Verilog was generated with one of the debug-signal flags
# (--debugSigs, --debugSigsGtkwave, --debugSigsYosys), it carries a
# DEBUG_SIGS generate block that states SandPiper's own pipesignal-to-
# Verilog mapping. The check reads that block when it is there and resolves
# gate references through it instead of the name rule. The flow does not
# pass those flags today, so this is an optional tightening, never a
# requirement: with no DEBUG_SIGS block the name rule above is used alone.

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

DFF_TYPES = re.compile(r'^\$(dff|dffe|adff|adffe|aldff|aldffe|sdff|sdffe|sdffce|dffsr|dffsre|dlatch|adlatch|dlatchsr|ff)$')
STAGE_SUFFIX_RE = re.compile(r'_[an]\d+$')
GEN_PREFIX_RE = re.compile(r'^L\d+_')
INDEX_RE = re.compile(r'\[[^\]]*\]')
TLV_TOKEN_RE = re.compile(r'([|/$])([A-Za-z_][A-Za-z0-9_]*)')
DBG_START_RE = re.compile(r'\bbegin\s*:\s*(DEBUG_SIGS\w*)')
DBG_BLOCK_RE = re.compile(r'\bbegin\s*:\s*(\\\S+|\w+)')
DBG_DECL_RE = re.compile(r'^\s*(?:\(\*\s*keep\s*\*\)\s*)?logic\b.*?(\\[^\s;]+)\s*;\s*$')
DBG_ASSIGN_RE = re.compile(r'^\s*assign\s+(\\[^\s=]+)\s*=\s*(.+?)\s*;\s*$')
DBG_LEAF_RE = re.compile(r'@(-?\d+)\$(\w+)$')


# Read an .eqy file into its [gold], [gate], [script] and [match] section bodies.
def parse_eqy(path):
    # Args:
    #    path: Path to the .eqy file to read
    #
    # Returns:
    #    Dict mapping each of "gold", "gate", "script" and "match" to the
    #    list of its stripped, non-comment, non-blank lines
    sections = {"gold": [], "gate": [], "script": [], "match": []}
    cur = None
    for raw in open(path):
        s = raw.strip()
        if s.startswith('['):
            cur = re.match(r'\[(\w+)', s).group(1)
            continue
        if not s or s.startswith('#'):
            continue
        if cur in sections:
            sections[cur].append(s)
    return sections


# Find the top module name that the [script] section elaborates.
def top_module(script):
    # Args:
    #    script: List of [script] section lines
    #
    # Returns:
    #    The module name given to `hierarchy -top`; exits 2 if there is none
    for s in script:
        m = re.search(r'hierarchy\s.*-top\s+(\S+)', s)
        if m:
            return m.group(1)
    print("ERROR: no 'hierarchy -top <top>' command in the [script] section.")
    sys.exit(2)


# Look up the sandpiper-saas arguments for an M5 configuration in config.json.
def m5_config_args(suffix):
    # Args:
    #    suffix: M5 configuration name from the generated .sv file name, or
    #            "" to use config.json's default_config
    #
    # Returns:
    #    The configuration's argument string, or "" when there is no
    #    config.json or no configuration to apply; exits 2 if the named
    #    configuration is absent from M5_configs
    try:
        with open('config.json') as f:
            config_json = json.load(f)
    except Exception:
        return ""
    M5_configs = config_json.get('M5_configs', {})
    if not suffix:
        suffix = config_json.get('default_config', "")
    if suffix == "":
        return ""
    args = M5_configs.get(suffix)
    if args is None:
        print(f"ERROR: M5 configuration '{suffix}' not found in config.json's M5_configs.")
        sys.exit(2)
    return args


# Regenerate the gate side's Verilog from wip.tlv so the check reflects current source.
def regen_gate(gate_lines, tmpdir):
    # Args:
    #    gate_lines: List of [gate] section lines
    #    tmpdir: Temporary directory to write the generated Verilog into
    #
    # Returns:
    #    The [gate] lines with the wip .sv read command repointed at the
    #    freshly generated file, or the lines unchanged when sandpiper-saas
    #    is unavailable and the on-disk .sv is used instead
    for i, s in enumerate(gate_lines):
        m = re.search(r'read_verilog.*\s(wip_?(\S*)\.sv)\b', s)
        if not m:
            continue
        sv_name, suffix = m.group(1), m.group(2)
        if shutil.which("sandpiper-saas") is None:
            if os.path.exists(sv_name):
                print(f"NOTE: sandpiper-saas not available; using on-disk {sv_name}.")
                return gate_lines
            print(f"ERROR: sandpiper-saas not available and {sv_name} does not exist.")
            sys.exit(2)
        out_path = os.path.join(tmpdir, sv_name)
        cmd = ["sandpiper-saas", "-i", "wip.tlv", "-o", sv_name, "--outdir", tmpdir,
               "--inlineGen", "--noline", "--iArgs"] + m5_config_args(suffix).split()
        r = run_sandpiper(cmd)
        if r.returncode != 0 and not os.path.exists(out_path) and not compile_diagnostic(r):
            # No SandPiper diagnostic: a service-side failure, possibly
            # transient, so try once more after a pause (as fev.sh does).
            time.sleep(15)
            r = run_sandpiper(cmd)
        if not os.path.exists(out_path):
            if r.returncode == 0:
                shutil.copy("wip.tlv", out_path)
            elif compile_diagnostic(r):
                print(f"SANDPIPER COMPILE ERROR: wip.tlv does not compile for {sv_name}, "
                      f"so the match lines cannot be checked and FEV would fail at the same step. "
                      f"Fix the source; SandPiper reports:")
                print(compile_diagnostic(r))
                sys.exit(1)
            else:
                print(f"ERROR: SandPiper failed regenerating {sv_name} from wip.tlv "
                      f"(no compiler diagnostic; the compile service was not reachable or "
                      f"returned nothing):")
                print(r.stdout + r.stderr)
                sys.exit(2)
        return gate_lines[:i] + [s.replace(sv_name, out_path)] + gate_lines[i + 1:]
    return gate_lines


# Run one sandpiper-saas command, treating a hang as a service failure.
def run_sandpiper(cmd):
    # Args:
    #    cmd: The sandpiper-saas argument list
    #
    # Returns:
    #    A CompletedProcess; on timeout, one with returncode 124 and whatever
    #    output had been produced, so callers see a service failure rather
    #    than an exception
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired as e:
        def text(b):
            return b.decode("utf-8", "replace") if isinstance(b, bytes) else (b or "")
        return subprocess.CompletedProcess(cmd, 124, text(e.stdout), text(e.stderr))


# Extract SandPiper's own compile diagnostic from a failed sandpiper-saas run.
def compile_diagnostic(r):
    # Args:
    #    r: The CompletedProcess of a sandpiper-saas invocation
    #
    # Returns:
    #    The diagnostic text (every ERROR/FATAL_ERROR block, with the source
    #    excerpt and explanation SandPiper prints under it) when the output
    #    carries a compiler diagnostic, or "" when it does not, which is how
    #    a service failure looks: the client's own message or nothing at all,
    #    with no ERROR block and no "SandPiper returning status" line
    out = r.stdout + r.stderr
    lines = out.splitlines()
    kept = []
    keep = False
    for line in lines:
        if re.match(r"^(FATAL_)?ERROR\(\d+\)", line):
            keep = True
        elif re.match(r"^[A-Z_]+\(\d+\)", line) or "SandPiper returning status" in line:
            keep = False
        if keep:
            kept.append(line)
    if not kept:
        return ""
    status = [l for l in lines if "SandPiper returning status" in l]
    return "\n".join(kept + [re.sub(r"\x1b\[[0-9;]*m", "", s) for s in status])


# Find the generated Verilog file the gate side reads.
def gate_sv_path(gate_lines):
    # Args:
    #    gate_lines: List of [gate] section lines, after regen_gate
    #
    # Returns:
    #    The path of the wip .sv file read there, or None if there is none
    for s in gate_lines:
        m = re.search(r'read_verilog.*\s(\S*wip_?\S*\.sv)\b', s)
        if m:
            return m.group(1)
    return None


# Elaborate one side of the comparison through yosys and return its design JSON.
def enumerate_side(read_lines, script, tag, tmpdir):
    # Args:
    #    read_lines: The side's read commands ([gold] or [gate] section)
    #    script: The [script] section's transform commands
    #    tag: "gold" or "gate", used to name the intermediate files
    #    tmpdir: Temporary directory for the script and JSON output
    #
    # Returns:
    #    The parsed yosys `write_json` design; exits 2 if yosys is missing
    #    or elaboration fails
    if shutil.which("yosys") is None:
        print("ERROR: yosys not found in PATH.")
        sys.exit(2)
    json_path = os.path.join(tmpdir, tag + ".json")
    ys_path = os.path.join(tmpdir, tag + ".ys")
    with open(ys_path, "w") as f:
        f.write("\n".join(read_lines + script + ["write_json " + json_path]) + "\n")
    r = subprocess.run(["yosys", "-q", "-s", ys_path], capture_output=True, text=True)
    if r.returncode != 0:
        print(f"ERROR: yosys failed elaborating the {tag} side:")
        print(r.stdout + r.stderr)
        sys.exit(2)
    with open(json_path) as f:
        return json.load(f)


# Collect the named signals of the top module, noting which are ports and which hold state.
def side_signals(design, top, tag):
    # Args:
    #    design: Parsed yosys design JSON
    #    top: Name of the module to enumerate
    #    tag: "gold" or "gate", used in the error message
    #
    # Returns:
    #    Dict mapping signal name to {"bits", "regbits", "reg", "port"};
    #    exits 2 if the module is absent after elaboration
    mod = design.get("modules", {}).get(top)
    if mod is None:
        print(f"ERROR: module '{top}' not found on the {tag} side after elaboration.")
        sys.exit(2)
    reg_bits = set()
    for cell in mod.get("cells", {}).values():
        if DFF_TYPES.match(cell.get("type", "")):
            for b in cell.get("connections", {}).get("Q", []):
                if isinstance(b, int):
                    reg_bits.add(b)
    ports = set(mod.get("ports", {}))
    sigs = {}
    for name, net in mod.get("netnames", {}).items():
        if net.get("hide_name") or name.startswith("$"):
            continue
        bits = [b for b in net.get("bits", []) if isinstance(b, int)]
        sigs[name] = {"bits": bits,
                      "regbits": [b for b in bits if b in reg_bits],
                      "reg": any(b in reg_bits for b in bits),
                      "port": name in ports}
    return sigs


# Split a TL-Verilog reference into its (sigil, token) pairs.
def tlv_tokens(ref):
    # Args:
    #    ref: A match line's gate reference, e.g. /rf_ram_if|default<>0$rgnt
    #
    # Returns:
    #    The list of (sigil, token) pairs in path order, or None when ref is
    #    not a pipesignal reference (plain Verilog syntax)
    if not re.search(r'[|$]', ref):
        return None
    toks = TLV_TOKEN_RE.findall(ref)
    if not toks or toks[-1][0] != '$':
        return None
    return toks


# Build the canonical scope-and-signal path of a TL-Verilog reference, without its stage.
def tlv_key(toks):
    # Args:
    #    toks: The (sigil, token) pairs from tlv_tokens
    #
    # Returns:
    #    The path with its sigils and without any stage or alignment
    #    qualifiers, e.g. /rf_ram_if|default$rgnt
    return "".join(sigil + tok for sigil, tok in toks)


# Map a TL-Verilog gate reference to the Verilog name SandPiper generates for it.
def tlv_stem(ref):
    # Args:
    #    ref: A match line's gate reference, e.g. /rf_ram_if|default<>0$rgnt
    #
    # Returns:
    #    The joined Verilog name without its stage suffix, e.g.
    #    RfRamIf_DEFAULT_rgnt, or None when ref is not a pipesignal
    #    reference
    toks = tlv_tokens(ref)
    if toks is None:
        return None
    parts = []
    for kind, tok in toks:
        if kind == '/':
            parts.append("".join(w[:1].upper() + w[1:] for w in tok.split('_')))
        elif kind == '|':
            parts.append(tok.upper())
        else:
            parts.append(tok)
    return "_".join(parts)


# Reduce a generated Verilog name to one joined path, independent of generate-block numbering.
def normalize_gate_name(name):
    # Args:
    #    name: A name from the gate enumeration, flat
    #          (RfRamIf_DEFAULT_rgnt_n1), inside a generate block
    #          (L1_Sort_Level[level].L2_a_num_a1), or with unpacked array
    #          dimensions (Sort_Level_a_num_a1[level])
    #
    # Returns:
    #    The name with indices removed, every L<n>_ uniquifying prefix
    #    stripped, and the hierarchy components joined with `_`
    parts = []
    for comp in name.split('.'):
        comp = GEN_PREFIX_RE.sub('', INDEX_RE.sub('', comp))
        if comp:
            parts.append(comp)
    return "_".join(parts)


# Collapse a name to its case- and underscore-insensitive form, for near-miss reporting only.
def squash(name):
    # Args:
    #    name: A normalized signal name
    #
    # Returns:
    #    The name lower-cased with its underscores removed. Distinct signals
    #    can share this form ($a_b and $ab, /rf_ram_if and /rfram_if), so it
    #    is never used to resolve a reference, only to name the look-alikes
    #    in a failure report
    return name.replace('_', '').lower()


# Turn a DEBUG_SIGS generate block label into the TLV scope token it stands for.
def dbg_block_scope(name):
    # Args:
    #    name: A generate block label, e.g. \/sort, \|pipe or P_pipe
    #
    # Returns:
    #    The scope or pipeline token with its sigil, or None if the label is
    #    not a scope (--debugSigsYosys renames \|pipe to P_pipe)
    if name.startswith('\\'):
        name = name[1:]
    if name.startswith('/') or name.startswith('|'):
        return name
    if name.startswith('P_'):
        return '|' + name[2:]
    return None


# Split a DEBUG_SIGS leaf name into the path it carries, its stage and its signal.
def dbg_split_leaf(esc):
    # Args:
    #    esc: The escaped leaf identifier, e.g. \@1$a_num or \//|pipe@1$a_num
    #
    # Returns:
    #    (path_segments, leading_slash_depth, stage, signal), or None if the
    #    name is not a debug-sig leaf. This build emits the bare
    #    \@<stage>$<sig> form and carries the path in the enclosing block
    #    names, so path_segments is normally empty; the leading-slash form is
    #    accepted but not relied on
    if esc.startswith('\\'):
        esc = esc[1:]
    m = DBG_LEAF_RE.search(esc)
    if not m:
        return None
    prefix = esc[:m.start()]
    depth = len(prefix) - len(prefix.lstrip('/'))
    segs = [s for s in prefix.split('/') if s and not s.startswith('?$')]
    return segs, depth, m.group(1), m.group(2)


# Read SandPiper's own pipesignal-to-Verilog mapping out of a DEBUG_SIGS block.
def debug_sig_map(sv_path):
    # Args:
    #    sv_path: Path to the generated Verilog to scan, or None
    #
    # Returns:
    #    (mapping, complete), where mapping takes a canonical TLV path (as
    #    built by tlv_key) to the set of Verilog names assigned to it, and
    #    complete says every declared debug signal was mapped. An absent or
    #    unreadable file, or one with no DEBUG_SIGS block, gives ({}, False)
    if not sv_path or not os.path.isfile(sv_path):
        return {}, False
    try:
        lines = open(sv_path).readlines()
    except OSError:
        return {}, False
    mapping = {}
    pending = set()
    stack = []
    in_dbg = False
    depth = 0
    for line in lines:
        if not in_dbg:
            if DBG_START_RE.search(line):
                in_dbg, depth, stack = True, 1, []
            continue
        m = DBG_BLOCK_RE.search(line)
        if m:
            stack.append((depth, dbg_block_scope(m.group(1))))
            depth += 1
            continue
        d = DBG_DECL_RE.match(line)
        if d:
            pending.add(d.group(1))
            continue
        a = DBG_ASSIGN_RE.match(line)
        if a:
            esc, vname = a.group(1), a.group(2)
            parsed = dbg_split_leaf(esc)
            if parsed is None:
                continue
            segs, _slash_depth, _stage, sig = parsed
            if segs:
                path = "".join(s if s.startswith('|') else '/' + s for s in segs)
            else:
                path = "".join(s for _d, s in stack if s)
            mapping.setdefault(path + '$' + sig, set()).add(vname)
            pending.discard(esc)
            continue
        if re.match(r'^\s*end\b', line):
            depth -= 1
            while stack and stack[-1][0] >= depth:
                stack.pop()
            if depth <= 0:
                break
    return mapping, bool(mapping) and not pending


# Index the gate enumeration by the two forms a gate reference is compared against.
def gate_name_index(gate_sigs):
    # Args:
    #    gate_sigs: The gate side's signal dict, as returned by side_signals
    #
    # Returns:
    #    Dict with "exact", a set of normalized names with and without their
    #    stage suffixes, and "near", a dict from squashed stage-less name to
    #    the set of normalized stage-less names that produced it, used only
    #    to report look-alikes when a reference fails to resolve
    exact = set()
    near = {}
    for n in gate_sigs:
        norm = normalize_gate_name(n)
        base = STAGE_SUFFIX_RE.sub('', norm)
        exact.add(norm)
        exact.add(base)
        near.setdefault(squash(base), set()).add(base)
    return {"exact": exact, "near": near}


# Test whether a match line's gate reference names a signal that exists on the gate side.
def gate_ref_exists(ref, gate_sigs, index, dbg):
    # Args:
    #    ref: The gate reference, in TL-Verilog or Verilog syntax
    #    gate_sigs: The gate side's signal dict
    #    index: The gate name index from gate_name_index
    #    dbg: The (mapping, complete) pair from debug_sig_map
    #
    # Returns:
    #    True if the reference resolves to a gate signal by the exact name
    #    rule (or the DEBUG_SIGS mapping when one is present); False
    #    otherwise. A gate name that matches only ignoring case and
    #    underscores does not count; see near_misses
    toks = tlv_tokens(ref)
    if toks is None:
        plain = ref.lstrip('*')
        return plain in gate_sigs or normalize_gate_name(plain) in index["exact"]
    dbg_map, dbg_complete = dbg
    if dbg_map:
        names = dbg_map.get(tlv_key(toks))
        if names:
            return any(normalize_gate_name(v) in index["exact"] for v in names)
        if dbg_complete:
            return False
    return tlv_stem(ref) in index["exact"]


# List the gate names that differ from a reference's expected name only in case or underscores.
def near_misses(ref, index):
    # Args:
    #    ref: The gate reference, in TL-Verilog syntax
    #    index: The gate name index from gate_name_index
    #
    # Returns:
    #    The sorted list of normalized stage-less gate names whose squashed
    #    form equals that of the name expected from ref, for reporting
    #    alongside a failed resolution; empty when ref is not a pipesignal
    #    reference or nothing comes close
    stem = tlv_stem(ref)
    if stem is None:
        return []
    return sorted(index["near"].get(squash(stem), ()))


# Reduce a gate name to the pipesignal name it was generated from.
def gate_base(name):
    # Args:
    #    name: A name from the gate enumeration
    #
    # Returns:
    #    The name with its stage suffix, generate-block hierarchy and
    #    leading scope and pipeline tokens removed, leaving the lower-case
    #    pipesignal name
    parts = STAGE_SUFFIX_RE.sub('', normalize_gate_name(name)).split('_')
    while len(parts) > 1 and parts[0][:1].isupper():
        parts.pop(0)
    return "_".join(parts)


# Extract the (gold name, gate reference) pairs from a [match] section.
def match_pairs(match_lines):
    # Args:
    #    match_lines: List of [match] section lines
    #
    # Returns:
    #    List of (gold_name, gate_ref) tuples, one per gold-match line
    pairs = []
    for s in match_lines:
        parts = s.split(None, 2)
        if len(parts) == 3 and parts[0] == "gold-match":
            pairs.append((parts[1], parts[2].strip()))
    return pairs


# Print a proposed [match] section pairing gold-only names to gate-only names.
def emit(top, gold_sigs, gate_sigs):
    # Args:
    #    top: Top module name, used for the section header
    #    gold_sigs: The gold side's signal dict
    #    gate_sigs: The gate side's signal dict
    #
    # Returns:
    #    None; writes the section to stdout, listing names with no unique
    #    gate candidate under an UNRESOLVED comment
    gold_only = sorted(n for n, v in gold_sigs.items() if not v["port"] and n not in gate_sigs)
    gate_only = sorted(n for n, v in gate_sigs.items() if not v["port"] and n not in gold_sigs)
    by_base = {}
    for n in gate_only:
        by_base.setdefault(gate_base(n), []).append(n)
    gold_base_count = {}
    for n in gold_only:
        b = n.rsplit(".", 1)[-1]
        gold_base_count[b] = gold_base_count.get(b, 0) + 1
    print(f"[match {top}]")
    unresolved = []
    for n in gold_only:
        b = n.rsplit(".", 1)[-1]
        cands = by_base.get(b, [])
        if len(cands) > 1:
            aligned = [c for c in cands if re.search(r'_a\d+$', c)]
            if len(aligned) == 1:
                cands = aligned
        if len(cands) == 1 and gold_base_count[b] == 1:
            print(f"gold-match {n} {cands[0]}")
        else:
            unresolved.append(n)
    if unresolved:
        print()
        print("# UNRESOLVED (no unique gate candidate; resolve by hand):")
        for n in unresolved:
            print(f"#   {n}")


# Cross-check an .eqy file's match section against the enumeration of the two designs.
def check(eqy_file, gold_sigs, gate_sigs, match_lines, dbg):
    # Args:
    #    eqy_file: Name of the .eqy file being checked, for the report
    #    gold_sigs: The gold side's signal dict
    #    gate_sigs: The gate side's signal dict
    #    match_lines: List of [match] section lines
    #    dbg: The (mapping, complete) pair from debug_sig_map
    #
    # Returns:
    #    None on agreement, after printing a PASS line; exits 1 listing
    #    every disagreement otherwise
    index = gate_name_index(gate_sigs)
    pairs = match_pairs(match_lines)
    matched_gold = {g for g, _ in pairs}
    problems = []
    for g, gate_ref in pairs:
        if g not in gold_sigs:
            problems.append(f"gold name not in the gold design: 'gold-match {g} {gate_ref}'")
        if not gate_ref_exists(gate_ref, gate_sigs, index, dbg):
            stem = tlv_stem(gate_ref)
            hint = f" (no gate signal matches '{stem}[_a<n>]')" if stem else ""
            near = near_misses(gate_ref, index)
            if near:
                hint += (f"; not accepted: {near} differ from it only in case or underscores, "
                         f"and eqy will not resolve the reference to them either")
            problems.append(f"gate reference maps to no gate signal: 'gold-match {g} {gate_ref}'{hint}")
    covered = set()
    for n, v in gold_sigs.items():
        if v["port"] or n in gate_sigs or n in matched_gold:
            covered.update(v["bits"])
    for n, v in sorted(gold_sigs.items()):
        if v["port"] or n in gate_sigs or n in matched_gold:
            continue
        if v["reg"] and any(b not in covered for b in v["regbits"]):
            problems.append(f"gold register '{n}' has no name-identical gate partner and no match line")
    if problems:
        print(f"MATCH CROSS-CHECK FAILED for {eqy_file} ({len(problems)} problem(s)):")
        for p in problems:
            print(f"  - {p}")
        print("The match section disagrees with the mechanical enumeration of the two designs.")
        print("Fix the match lines (or the design) before FEV is run.")
        sys.exit(1)
    source = "SandPiper debug signals" if dbg[0] else "generated name rule"
    print(f"match cross-check PASS: {eqy_file} "
          f"({len(pairs)} match lines, {len(gold_sigs)} gold signals, {len(gate_sigs)} gate signals, "
          f"gate names resolved by the {source})")


# Parse the command line, elaborate both sides, and run the requested mode.
def main():
    # Args:
    #    None; reads sys.argv for the mode (--emit or --check) and the .eqy file
    #
    # Returns:
    #    None; exits 1 on bad usage or a failed check, 2 when the check could
    #    not be run
    if len(sys.argv) != 3 or sys.argv[1] not in ("--emit", "--check"):
        print("Usage: ./gen_match_lines.py (--emit|--check) <fev*.eqy>")
        sys.exit(1)
    mode, eqy_file = sys.argv[1], sys.argv[2]
    if not os.path.isfile(eqy_file):
        print(f"ERROR: {eqy_file} not found.")
        sys.exit(2)
    sections = parse_eqy(eqy_file)
    top = top_module(sections["script"])
    with tempfile.TemporaryDirectory() as tmpdir:
        gate_lines = regen_gate(sections["gate"], tmpdir)
        dbg = debug_sig_map(gate_sv_path(gate_lines))
        gold_sigs = side_signals(enumerate_side(sections["gold"], sections["script"], "gold", tmpdir), top, "gold")
        gate_sigs = side_signals(enumerate_side(gate_lines, sections["script"], "gate", tmpdir), top, "gate")
    if mode == "--emit":
        emit(top, gold_sigs, gate_sigs)
    else:
        check(eqy_file, gold_sigs, gate_sigs, sections["match"], dbg)


if __name__ == "__main__":
    main()
