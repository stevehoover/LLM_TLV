"""Source correlation from SandPiper-generated Verilog back to the TL-Verilog
it came from, so tool messages that name a generated line can also show the
line the worker actually wrote.

SandPiper 1.14 under fev.sh's flags (--inlineGen --noline --iArgs) emits
"//_\\source <file> <N>" markers (the marker line itself is TLV line N),
"//_\\end_source" at the end of an expanded macro body, and banner comments
around the inlined generated declarations, which carry only "// For <sig>."
comments. Without --noline it emits "`line N \"file\" L" directives instead
(the line after the directive is TLV line N). Both forms are handled."""

import os
import re
from collections import namedtuple

Loc = namedtuple("Loc", "file line inst via")

LINE_RE = re.compile(r'^\s*`line\s+(\d+)\s+"([^"]+)"\s+\d')
SOURCE_RE = re.compile(r"^\s*//_\\source\s+(\S+)\s+(\d+)")
END_SOURCE_RE = re.compile(r"^\s*//_\\end_source\b")
INST_RE = re.compile(r"//\s*Instantiated from\s+\S+,\s*(\d+)")
FOR_RE = re.compile(r"^\s*// For (\S+?)\.\s*$")
GEN_BEGIN = "// ---------- Generated Code Inlined Here"
GEN_END = "// ---------- Generated Code Ends"

SV_REF_RE = re.compile(r"(?<![\w/.-])((?:[\w.-]+/)*(?:wip|feved)[\w.-]*\.sv):(\d+)\b")
TLV_REF_RE = re.compile(r"File '([^']+\.tlv)' Line (\d+)")


def _inst(text):
    m = INST_RE.search(text)
    return int(m.group(1)) if m else None


# The TLV file to quote for a generated .sv: the .sv's own stem (wip_*.sv ->
# wip.tlv, feved.sv -> feved.tlv) when it exists, since the markers say
# wip.tlv even inside the copied feved.sv; else the marker's file beside it.
def tlv_path(sv_path, marker_file):
    d = os.path.dirname(sv_path)
    stem = os.path.basename(sv_path).split("_")[0].removesuffix(".sv")
    own = os.path.join(d, stem + ".tlv")
    if os.path.exists(own):
        return own
    return os.path.join(d, marker_file) if marker_file else None


# First TLV line assigning the pipesignal named by a "// For <path>$sig."
# comment (the generated declarations carry no other correlation).
def _signal_line(tlv_file, sig):
    name = sig.rsplit("$", 1)[-1]
    pat = re.compile(r"(?<![A-Za-z_$])\$\$?" + re.escape(name) + r"\b\s*(?:\[[^\]]*\])?\s*=(?!=)")
    try:
        lines = open(tlv_file).read().splitlines()
    except OSError:
        return None
    for i, l in enumerate(lines, 1):
        if pat.search(l):
            return i
    return None


# TLV origin of line n of a generated .sv, or None when the line has no
# correlation (marker lines, generated declarations without a "// For" hint,
# files without markers). Walks the markers preceding n and counts.
def map_line(sv_path, n):
    try:
        lines = open(sv_path).read().splitlines()
    except OSError:
        return None
    if not 1 <= n <= len(lines):
        return None
    file = tlv = inst = None
    stack = []
    in_gen = False
    last_for = None
    marker_file = None
    for i, text in enumerate(lines, 1):
        m = LINE_RE.match(text)
        if m:
            file, tlv, inst = m.group(2), int(m.group(1)) - 1, _inst(text)
            if not file.endswith(".tlv"):
                file = None
            else:
                marker_file = marker_file or file
            if i == n:
                return None
            continue
        m = SOURCE_RE.match(text)
        if m:
            stack.append((file, tlv, inst))
            file, tlv, inst = m.group(1), int(m.group(2)), _inst(text)
            marker_file = marker_file or file
            if i == n:
                return Loc(tlv_path(sv_path, file), tlv, inst, "marker")
            continue
        if END_SOURCE_RE.match(text):
            if stack:
                file, tlv, inst = stack.pop()
                if tlv is not None:
                    tlv += 1
            if i == n:
                return None
            continue
        if text.startswith(GEN_BEGIN):
            in_gen = True
            if i == n:
                return None
            continue
        if text.startswith(GEN_END):
            in_gen = False
            if i == n:
                return None
            continue
        if in_gen or file is None:
            fm = FOR_RE.match(text)
            if fm:
                last_for = fm.group(1)
            if i == n:
                if last_for and "$" in last_for:
                    tf = tlv_path(sv_path, marker_file)
                    ln = _signal_line(tf, last_for) if tf else None
                    if ln:
                        return Loc(tf, ln, None, last_for)
                return None
            continue
        tlv += 1
        if i == n:
            return Loc(tlv_path(sv_path, file), tlv, inst, "marker")
    return None


# Numbered TLV lines around line, the target marked with '>'.
def quote(tlv_file, line, context=1):
    try:
        lines = open(tlv_file).read().splitlines()
    except OSError:
        return ""
    lo, hi = max(1, line - context), min(len(lines), line + context)
    return "\n".join(f"    {'>' if i == line else ' '}{i:5}: {lines[i-1]}" for i in range(lo, hi + 1))


# Short tag for a mapped location: names the macro instantiation site when the
# line lies inside an expanded macro body, or the pipesignal whose generated
# declaration was hit.
def describe(loc):
    where = f"{os.path.basename(loc.file)}:{loc.line}"
    if loc.via != "marker":
        return f"{where} (assignment of {loc.via}, whose generated declaration this is)"
    if loc.inst:
        return f"{where} (macro body; instantiated at line {loc.inst})"
    return where


# Append the TLV origin to every "file.sv:N" (yosys/EQY) reference to a
# generated file and quote the TLV source once per location; quote the source
# for SandPiper's own "File 'x.tlv' Line N" as well. Unmappable references are
# left untouched.
def annotate(text, mdir):
    out = []
    quoted = set()
    for line in text.splitlines():
        blocks = []
        tags = []

        def sv_sub(m):
            p = os.path.join(mdir, m.group(1))
            if not os.path.exists(p):
                p = os.path.join(mdir, os.path.basename(m.group(1)))
            loc = map_line(p, int(m.group(2)))
            if not loc or not os.path.exists(loc.file):
                return m.group(0)
            key = (loc.file, loc.line)
            if key not in quoted:
                quoted.add(key)
                blocks.append(f"  TLV source at {os.path.basename(loc.file)}:{loc.line}:\n"
                              + quote(loc.file, loc.line))
            tags.append(f"[{m.group(1)}:{m.group(2)} is from TLV {describe(loc)}]")
            return m.group(0)

        def tlv_sub(m):
            p = os.path.join(mdir, m.group(1))
            key = (p, int(m.group(2)))
            if os.path.exists(p) and key not in quoted:
                quoted.add(key)
                blocks.append(f"  TLV source at {m.group(1)}:{m.group(2)}:\n" + quote(p, int(m.group(2))))
            return m.group(0)

        line = SV_REF_RE.sub(sv_sub, line)
        line = TLV_REF_RE.sub(tlv_sub, line)
        out.append(line + ("  " + " ".join(tags) if tags else ""))
        out.extend(blocks)
    return "\n".join(out) + ("\n" if text.endswith("\n") else "")
