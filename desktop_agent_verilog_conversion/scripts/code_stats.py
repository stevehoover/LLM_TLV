#!/usr/bin/env python3

# Character-level code-size comparison of a hand-written Verilog module against its
# TL-Verilog conversion, using the methodology of Hoover, "Timing-Abstract Circuit
# Design in Transaction-Level Verilog", ICCD 2017, Fig. 11 / Table I:
#   * the unit is characters, not lines (line counts are reported alongside);
#   * comments and whitespace are separated out and excluded from the headline ratio;
#   * remaining characters are attributed to Validity, Structure, Staging,
#     Declarations, or Logic. The paper's "Clock Gating" bucket only occurs in
#     SandPiper-generated code and is folded into Validity here (it is derived from
#     the same ?$valid information). Two buckets from the Makerchip "Code Comparison"
#     chart are added: Instrumentation and Untouched.
#
# SandPiper itself was not used for the TLV-side categories: its --help text (all flags)
# lists no stats option and no *_stats output was found in any local run, so both sides
# are classified by the rules below. The rules are written to be applied identically to
# both sides wherever the construct exists in both languages; where a construct exists
# in only one language the paper's Table I example decides.
#
# Categories and rules (character granularity; every character lands in exactly one):
#
#   whitespace      space, tab, CR, LF, form feed anywhere outside a comment.
#   comments        // to end of line, /* ... */, and in a TL-Verilog \m5 region lines
#                   whose first non-blank character is "/" (M5 comment syntax).
#                   Comment delimiters count as comment characters.
#   instrumentation lines containing $display/$monitor/$finish/$dump*/$error/$fatal/
#                   $info/$warning/assert, and TL-Verilog \viz_* regions.
#   validity        TL-Verilog "?$cond" / "?*cond" when-condition lines.
#                   Verilog: `WHEN(...) and clock-gate cells in SandPiper output
#                   (hand-written Verilog has no validity construct, so 0).
#   structure       Verilog: module/endmodule and the header punctuation ( #( ( ); ),
#                   generate/endgenerate and generate-context if/else/for/case, begin/end
#                   and block labels, always_comb / always @* headers, initial and for
#                   headers, compiler directives (`default_nettype, `ifdef...), and
#                   module instantiations in their entirety (hierarchy plumbing).
#                   TL-Verilog: region headers (\TLV, \SV, \SV_plus, \m5, \m5_TLV_version),
#                   the whole \m5 region (preprocessor setup), |pipeline and /scope lines,
#                   |pipe and /scope prefixes inside expressions, and every M5/M4 macro
#                   line (m5+..., m5_if_eq_block(..., m4_include_lib(..., and the
#                   '], / ']) bracket lines that close them).
#   staging         Verilog: the "always @(posedge clk)" / always_ff header, and inside a
#                   clocked block the target and "<=" of every nonblocking assignment.
#                   When the right-hand side is a plain identifier (optionally with one
#                   select), the whole statement is staging (a pure flop, Table I).
#                   Any other right-hand side, and every if/else/case condition inside
#                   the clocked block (reset muxes, enables, holds), is logic, because
#                   the TL-Verilog side expresses exactly the same mux as logic.
#                   TL-Verilog: @N stage lines, and the <<N / >>N / <>N alignment
#                   operators wherever they occur.
#   declarations    Verilog: input/output/inout/wire/reg/logic/parameter/localparam/
#                   integer/genvar/bit/int statements from the keyword through the
#                   identifier list (types, ranges, names, commas, and the terminating
#                   ; or ,). A parameter's default value is part of the declaration.
#                   For "wire x = expr;" the "= expr;" is logic.
#                   TL-Verilog: bit ranges on the left-hand side of an assignment
#                   (the first assignment of a pipesignal is its declaration; any
#                   later width on a LHS is counted the same way, consistently).
#   logic           everything else: assign statements, expressions, operators,
#                   signal references (including *verilog_sig references from TLV),
#                   the "=" of an assignment, procedural if/else/case, blocking
#                   assignments, and the interface plumbing "$x = *i_x;" lines.
#   untouched       TL-Verilog only: every code character in a \SV or \SV_plus region,
#                   i.e. Verilog that the conversion left as Verilog (module interface,
#                   localparams, clock wires, RAM arrays). On the Verilog side this is 0.
#
# Side metrics (not categories, do not sum into the total):
#   port_plumbing   TLV: code characters of "$x = *i_x;" and "*o_x = $x;" lines, so the
#                   cost of the SandPiper interface convention can be quoted separately.
#
# Ratios are Verilog / TL-Verilog, so a value above 1 means the TL-Verilog is smaller.
#
# Usage:
#   ./code_stats.py [MODULE_DIR ...] [--manifest sets.json] [--csv out.csv]
#                   [--png out.png] [--summary out.txt] [--no-gensv]
#
#   MODULE_DIR      a conversion directory: orig.sv is the Verilog side, wip.tlv the
#                   TL-Verilog side (fully_feved.tlv with --feved), and wip.sv or
#                   wip_gen.sv the SandPiper-generated SV ("SV Total" bar) if present.
#   --manifest      JSON list of {"name", "verilog": [files], "tlv": [files],
#                   "gensv": [files]} for sets that are not a single module dir
#                   (for example a flattened hierarchy against several Verilog files).
#
# Requires Python 3.8+. matplotlib is needed only for --png.

import argparse
import csv
import json
import os
import re
import sys

CATEGORIES = ["logic", "declarations", "structure", "staging", "validity",
              "instrumentation", "untouched", "comments", "whitespace"]
CODE_CATEGORIES = CATEGORIES[:7]

WS = " \t\r\n\f\v"

VERILOG_DECL_KW = {"input", "output", "inout", "wire", "reg", "logic", "parameter",
                   "localparam", "integer", "genvar", "bit", "int", "real", "time"}
VERILOG_STRUCT_KW = {"module", "endmodule", "generate", "endgenerate", "begin", "end",
                     "initial", "function", "endfunction", "task", "endtask", "endcase"}
VERILOG_PROC_KW = {"if", "else", "case", "casez", "casex", "default", "for", "while"}
INSTR_RE = re.compile(r"\$(display|monitor|finish|dump\w*|error|fatal|info|warning|write|strobe)\b|\bassert\b")

TOKEN_RE = re.compile(r"`?[A-Za-z_][A-Za-z_0-9$]*|\d+'[bBhHdDoO][0-9a-fA-FxXzZ_?]+|\d[\d_]*\.?\d*|\"[^\"]*\"|<=|>=|==|!=|&&|\|\||<<|>>|::|[^\sA-Za-z_0-9]")


# Mark comment and whitespace characters. Returns a list with one category per
# character ("comments", "whitespace", or None for code) and the text with comments
# blanked to spaces so later passes see code only at the original offsets.
def mask_comments(text, m5_regions=()):
    cats = [None] * len(text)
    masked = list(text)
    i = 0
    n = len(text)
    in_string = False
    while i < n:
        c = text[i]
        if in_string:
            if c == "\\" and i + 1 < n:
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
            i += 1
            continue
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                cats[k] = "comments"
                masked[k] = " "
            i = j
            continue
        if text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if text[k] in WS:
                    cats[k] = "whitespace"
                else:
                    cats[k] = "comments"
                masked[k] = " " if text[k] != "\n" else "\n"
            i = j
            continue
        if c in WS:
            cats[i] = "whitespace"
        i += 1
    for start, end in m5_regions:
        for ls, le in line_spans("".join(masked), start, end):
            line = "".join(masked[ls:le])
            stripped = line.lstrip()
            if stripped.startswith("/") and not stripped.startswith("//"):
                for k in range(ls, le):
                    if cats[k] is None:
                        cats[k] = "comments"
                        masked[k] = " "
    return cats, "".join(masked)


# Yield (start, end) offsets of each line in text[start:end], end excluding the newline.
def line_spans(text, start=0, end=None):
    end = len(text) if end is None else end
    i = start
    while i < end:
        j = text.find("\n", i, end)
        j = end if j < 0 else j
        yield i, j
        i = j + 1


def fill(cats, start, end, cat):
    for k in range(start, end):
        if cats[k] not in ("comments", "whitespace"):
            cats[k] = cat


# Tokenize masked code in [start, end) into (text, start, end) triples.
def tokens_in(masked, start, end):
    return [(m.group(0), m.start(), m.end()) for m in TOKEN_RE.finditer(masked, start, end)]


# Classify a Verilog / SystemVerilog code span. The default for every code character is
# logic; the rules in the header override spans. `is_gensv` enables the SandPiper
# output constructs (`WHEN, clock gates) which never occur in hand-written serv code.
def classify_verilog(cats, masked, start, end):
    fill(cats, start, end, "logic")
    for ls, le in line_spans(masked, start, end):
        if INSTR_RE.search(masked[ls:le]):
            fill(cats, ls, le, "instrumentation")
    toks = tokens_in(masked, start, end)
    n = len(toks)
    i = 0
    proc = False          # inside always/initial
    clocked = False       # the always block is edge-triggered
    depth = 0             # begin/end depth inside the procedural block
    gen_depth = 0         # generate nesting
    in_header = False     # module header (ports/params)
    while i < n:
        t, s, e = toks[i]
        nxt = toks[i + 1][0] if i + 1 < n else ""

        if t.startswith("`"):
            j = i
            line_end = masked.find("\n", s)
            line_end = end if line_end < 0 else line_end
            if t in ("`WHEN",):
                fill(cats, s, e, "validity")
                i += 1
                continue
            while j < n and toks[j][1] < line_end:
                j += 1
            fill(cats, s, toks[j - 1][2], "structure")
            i = j
            continue

        if t == "module":
            in_header = True
            fill(cats, s, e, "structure")
            if nxt and re.match(r"[A-Za-z_]", nxt):
                fill(cats, toks[i + 1][1], toks[i + 1][2], "structure")
                i += 1
            i += 1
            continue

        if in_header and t in ("#", "(", ")", ";"):
            fill(cats, s, e, "structure")
            if t == ";":
                in_header = False
            i += 1
            continue

        if t in VERILOG_DECL_KW and not (proc and t not in VERILOG_DECL_KW):
            j = i
            par = 0
            while j < n:
                tj = toks[j][0]
                if tj == "(":
                    par += 1
                elif tj == ")":
                    if par == 0:
                        break
                    par -= 1
                elif par == 0 and (tj in (";", "=") or (in_header and tj == ",")):
                    break
                j += 1
            is_param = t in ("parameter", "localparam")
            if j < n and toks[j][0] == "=" and is_param:
                k = j
                par = 0
                while k < n:
                    tk = toks[k][0]
                    if tk == "(":
                        par += 1
                    elif tk == ")":
                        if par == 0:
                            break
                        par -= 1
                    elif par == 0 and tk in (";", ","):
                        break
                    k += 1
                j = k
            last = j if j < n and toks[j][0] in (";", ",") else j - 1
            fill(cats, s, toks[last][2] if last < n else e, "declarations")
            i = j + 1 if (j < n and toks[j][0] in (";", ",")) else j
            continue

        if t == "always" or t.startswith("always_"):
            proc = True
            depth = 0
            j = i + 1
            clocked = t == "always_ff"
            if j < n and toks[j][0] == "@":
                k = j + 1
                if k < n and toks[k][0] == "(":
                    par = 1
                    k += 1
                    while k < n and par > 0:
                        if toks[k][0] == "(":
                            par += 1
                        elif toks[k][0] == ")":
                            par -= 1
                        elif toks[k][0] in ("posedge", "negedge"):
                            clocked = True
                        k += 1
                j = k
            elif j < n and toks[j][0] == "*":
                j += 1
            fill(cats, s, toks[j - 1][2], "staging" if clocked else "structure")
            i = j
            continue

        if t == "initial":
            proc = True
            clocked = False
            depth = 0
            fill(cats, s, e, "structure")
            i += 1
            continue

        if proc:
            if t == "begin":
                depth += 1
                fill(cats, s, e, "structure")
                i += 1
                continue
            if t == "end":
                depth -= 1
                fill(cats, s, e, "structure")
                i += 1
                if depth <= 0:
                    proc = False
                continue
            if t == "for":
                j = i + 1
                if j < n and toks[j][0] == "(":
                    par = 1
                    j += 1
                    while j < n and par > 0:
                        par += toks[j][0] == "("
                        par -= toks[j][0] == ")"
                        j += 1
                fill(cats, s, toks[j - 1][2], "structure")
                i = j
                continue
            if clocked and t == "<=":
                stmt_start = i - 1
                while stmt_start >= 0 and toks[stmt_start][0] not in (";", "begin", "end", ")", "else", ":"):
                    stmt_start -= 1
                stmt_start += 1
                if stmt_start < i and toks[stmt_start][0] in ("if", "case"):
                    stmt_start = i - 1
                    while stmt_start >= 0 and toks[stmt_start][0] not in (")", ";", "begin", "else", ":"):
                        stmt_start -= 1
                    stmt_start += 1
                j = i + 1
                while j < n and toks[j][0] != ";":
                    j += 1
                rhs = toks[i + 1:j]
                plain = len(rhs) >= 1 and re.match(r"[A-Za-z_]", rhs[0][0]) is not None and (
                    len(rhs) == 1 or (rhs[1][0] == "[" and rhs[-1][0] == "]"))
                if plain:
                    fill(cats, toks[stmt_start][1], toks[j][2] if j < n else e, "staging")
                else:
                    fill(cats, toks[stmt_start][1], e, "staging")
                    fill(cats, e, toks[j][2] if j < n else e, "logic")
                i = j + 1
                if depth <= 0 and not (i < n and toks[i][0] == "else"):
                    proc = False
                continue
            if t == ";" and depth <= 0 and not (i + 1 < n and toks[i + 1][0] == "else"):
                proc = False
            i += 1
            continue

        if t in ("generate", "endgenerate"):
            gen_depth += t == "generate"
            gen_depth -= t == "endgenerate"
            fill(cats, s, e, "structure")
            i += 1
            continue

        if t in VERILOG_STRUCT_KW or t in VERILOG_PROC_KW:
            j = i + 1
            if t in ("if", "for", "case", "casez", "casex") and j < n and toks[j][0] == "(":
                par = 1
                j += 1
                while j < n and par > 0:
                    par += toks[j][0] == "("
                    par -= toks[j][0] == ")"
                    j += 1
            if t == "end" and j < n and toks[j][0] == ":" and j + 1 < n:
                j += 2
            if t == "begin" and j < n and toks[j][0] == ":" and j + 1 < n:
                j += 2
            fill(cats, s, toks[j - 1][2], "structure")
            i = j
            continue

        if t == "assign":
            i += 1
            continue

        if re.match(r"[A-Za-z_]", t) and not t.startswith("`") and nxt in ("#", "(") or (
                re.match(r"[A-Za-z_]", t) and i + 1 < n and re.match(r"[A-Za-z_]", nxt) and i + 2 < n and toks[i + 2][0] == "("):
            if t in ("clk_gate",) or t.startswith("gen_Clk"):
                cat = "validity"
            else:
                cat = "structure"
            j = i
            while j < n and toks[j][0] != ";":
                j += 1
            fill(cats, s, toks[j][2] if j < n else e, cat)
            i = j + 1
            continue

        i += 1


TLV_REGION_RE = re.compile(r"^\\(m5_TLV_version|TLV_version|m5|m4|SV_plus|SV|TLV|viz_\w+|viz)\b")
TLV_STMT_START_RE = re.compile(r"^(<<\d+|>>\d+)?[$*{\\]")
ALIGN_RE = re.compile(r"(<<\d+|>>\d+|<>\d+)")
SCOPE_REF_RE = re.compile(r"(?<![\w$])(/\w+(\[[^\]]*\])?|\|\w+)(?=[<>$*/\[])")
PLUMBING_RE = re.compile(r"^\s*(\$\w+(\[[^\]]*\])?\s*=\s*\*\w+|\*\w+\s*=\s*\$\w+(\[[^\]]*\])?)\s*;\s*$")


# Return [(start, end, kind)] regions of a TL-Verilog file, where kind is one of
# m5, sv, tlv, viz, sv_plus (an \SV_plus block nested in \TLV, ended by dedent).
def tlv_regions(text):
    regions = []
    lines = list(line_spans(text))
    cur = ("tlv", 0)
    sub = None          # (kind, indent, start) for \SV_plus / \viz nested regions
    for ls, le in lines:
        line = text[ls:le]
        stripped = line.lstrip(" ")
        indent = len(line) - len(stripped)
        m = TLV_REGION_RE.match(stripped)
        if m and indent == 0:
            if sub:
                regions.append((sub[2], ls, sub[0]))
                sub = None
            regions.append((cur[1], ls, cur[0]))
            kind = m.group(1)
            if kind in ("m5", "m4"):
                cur = ("m5", ls)
            elif kind in ("SV", "SV_plus"):
                cur = ("sv", ls)
            elif kind.startswith("viz"):
                cur = ("viz", ls)
            elif kind in ("m5_TLV_version", "TLV_version"):
                cur = ("hdr", ls)
            else:
                cur = ("tlv", ls)
            continue
        if cur[0] == "tlv":
            if sub and stripped.strip() and indent <= sub[1]:
                regions.append((sub[2], ls, sub[0]))
                sub = None
            if m and indent > 0 and not sub:
                kind = m.group(1)
                sub = ("sv_plus" if kind == "SV_plus" else "viz", indent, ls)
    if sub:
        regions.append((sub[2], len(text), sub[0]))
    regions.append((cur[1], len(text), cur[0]))
    out = []
    for s, e, k in regions:
        if e > s:
            out.append((s, e, k))
    out.sort()
    return out


# Classify the body of one \TLV region (already free of \SV_plus / \viz sub-regions).
def classify_tlv_body(cats, masked, start, end, plumbing):
    fill(cats, start, end, "logic")
    stmt = []            # accumulated (ls, le) of the current multi-line statement
    open_stmt = False

    def flush():
        if stmt:
            classify_tlv_statement(cats, masked, stmt[0][0], stmt[-1][1])
        stmt.clear()

    for ls, le in line_spans(masked, start, end):
        line = masked[ls:le]
        code = line.strip()
        if not code:
            continue
        if INSTR_RE.search(code):
            flush()
            fill(cats, ls, le, "instrumentation")
            continue
        head = code[0]
        if head == "\\":
            flush()
            fill(cats, ls, le, "structure")
            continue
        if head in "|/":
            flush()
            fill(cats, ls, le, "structure")
            continue
        if head == "@":
            flush()
            fill(cats, ls, le, "staging")
            continue
        if head == "?":
            flush()
            fill(cats, ls, le, "validity")
            continue
        if code.startswith(("m5", "m4", "']", "'])")) or code.startswith("'"):
            flush()
            fill(cats, ls, le, "structure")
            continue
        if TLV_STMT_START_RE.match(code) or not open_stmt:
            flush()
            if PLUMBING_RE.match(line):
                plumbing[0] += sum(1 for k in range(ls, le) if cats[k] not in ("comments", "whitespace"))
        stmt.append((ls, le))
        open_stmt = not code.rstrip().endswith(";")
    flush()


# Classify one TL-Verilog assignment statement spanning masked[start:end].
def classify_tlv_statement(cats, masked, start, end):
    text = masked[start:end]
    for m in ALIGN_RE.finditer(text):
        fill(cats, start + m.start(), start + m.end(), "staging")
    for m in SCOPE_REF_RE.finditer(text):
        g = m.group(1)
        fill(cats, start + m.start(1), start + m.start(1) + len(g), "structure")
    eq = find_assign_eq(text)
    if eq < 0:
        return
    lhs = text[:eq]
    depth = 0
    for k, c in enumerate(lhs):
        if c == "[":
            depth += 1
        if depth > 0 and cats[start + k] == "logic":
            cats[start + k] = "declarations"
        if c == "]":
            depth -= 1


# Offset of the assignment "=" at bracket depth 0 (not part of ==, <=, >=, !=), else -1.
def find_assign_eq(text):
    depth = 0
    for k, c in enumerate(text):
        if c in "[({":
            depth += 1
        elif c in "])}":
            depth -= 1
        elif c == "=" and depth == 0:
            prev = text[k - 1] if k > 0 else ""
            nxt = text[k + 1] if k + 1 < len(text) else ""
            if prev not in "<>!=" and nxt != "=":
                return k
    return -1


# Classify a whole .tlv file. Returns (cats, plumbing_chars).
def classify_tlv_file(text):
    regions = tlv_regions(text)
    m5_regions = [(s, e) for s, e, k in regions if k == "m5"]
    cats, masked = mask_comments(text, m5_regions)
    plumbing = [0]
    for s, e, kind in regions:
        if kind == "tlv":
            classify_tlv_body(cats, masked, s, e, plumbing)
        elif kind in ("sv", "sv_plus"):
            fill(cats, s, e, "untouched")
        elif kind == "viz":
            fill(cats, s, e, "instrumentation")
        else:
            fill(cats, s, e, "structure")
    # region header lines and M4/M5 macro lines are structure in every region
    for ls, le in line_spans(masked):
        code = masked[ls:le].strip()
        if code.startswith("\\") or code.startswith(("m4_", "m5_", "m5+", "']", "'")):
            fill(cats, ls, le, "structure")
    return cats, plumbing[0]


def classify_verilog_file(text):
    cats, masked = mask_comments(text)
    classify_verilog(cats, masked, 0, len(text))
    return cats, 0


# Count categories and lines for a list of files with the given classifier.
def count_files(files, classifier):
    totals = {c: 0 for c in CATEGORIES}
    lines_total = 0
    lines_code = 0
    plumbing = 0
    for f in files:
        with open(f, "r", encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        cats, pl = classifier(text)
        plumbing += pl
        for c in cats:
            totals[c] += 1
        for ls, le in line_spans(text):
            lines_total += 1
            if any(cats[k] not in ("comments", "whitespace") for k in range(ls, le)):
                lines_code += 1
    totals["total"] = len(text) if len(files) == 1 else sum(totals[c] for c in CATEGORIES)
    totals["total"] = sum(totals[c] for c in CATEGORIES)
    totals["code"] = sum(totals[c] for c in CODE_CATEGORIES)
    totals["lines"] = lines_total
    totals["lines_code"] = lines_code
    totals["port_plumbing"] = plumbing
    return totals


def pick(files, *names):
    for name in names:
        p = os.path.join(files, name)
        if os.path.isfile(p) or os.path.islink(p):
            return [p]
    return []


def sets_from_dirs(dirs, feved):
    sets = []
    for d in dirs:
        d = d.rstrip("/")
        tlv = pick(d, "fully_feved.tlv", "wip.tlv") if feved else pick(d, "wip.tlv", "fully_feved.tlv")
        sets.append({"name": os.path.basename(d), "verilog": pick(d, "orig.sv"),
                     "tlv": tlv, "gensv": pick(d, "wip.sv", "wip_gen.sv")})
    return sets


def ratio(a, b):
    return round(a / b, 3) if b else ""


def measure(entry, no_gensv):
    v = count_files(entry["verilog"], classify_verilog_file)
    t = count_files(entry["tlv"], classify_tlv_file)
    g = count_files(entry["gensv"], classify_verilog_file) if entry.get("gensv") and not no_gensv else None
    row = {"module": entry["name"]}
    for prefix, tot in (("verilog", v), ("tlv", t)):
        row[prefix + "_chars_total"] = tot["total"]
        row[prefix + "_chars_code"] = tot["code"]
        for c in CATEGORIES:
            row[prefix + "_chars_" + c] = tot[c]
        row[prefix + "_lines"] = tot["lines"]
        row[prefix + "_lines_code"] = tot["lines_code"]
    row["tlv_chars_port_plumbing"] = t["port_plumbing"]
    if g:
        row["gensv_chars_total"] = g["total"]
        row["gensv_chars_code"] = g["code"]
        for c in CATEGORIES:
            row["gensv_chars_" + c] = g[c]
        row["gensv_lines"] = g["lines"]
        row["gensv_lines_code"] = g["lines_code"]
    else:
        for k in ["gensv_chars_total", "gensv_chars_code"] + ["gensv_chars_" + c for c in CATEGORIES] + ["gensv_lines", "gensv_lines_code"]:
            row[k] = ""
    row["ratio_chars"] = ratio(v["total"], t["total"])
    row["ratio_chars_excl_ws_comments"] = ratio(v["code"], t["code"])
    row["ratio_lines"] = ratio(v["lines_code"], t["lines_code"])
    row["ratio_lines_total"] = ratio(v["lines"], t["lines"])
    return row


def print_table(rows):
    hdr = ("module", "V code", "T code", "ratio", "V lines", "T lines", "ratio", "T untouched", "T plumbing", "Gen code")
    print("%-18s %8s %8s %6s %8s %8s %6s %11s %10s %9s" % hdr)
    for r in rows:
        print("%-18s %8d %8d %6s %8d %8d %6s %11d %10d %9s" % (
            r["module"], r["verilog_chars_code"], r["tlv_chars_code"], r["ratio_chars_excl_ws_comments"],
            r["verilog_lines_code"], r["tlv_lines_code"], r["ratio_lines"],
            r["tlv_chars_untouched"], r["tlv_chars_port_plumbing"], r["gensv_chars_code"]))
    print()
    print("Category breakdown (code characters):")
    print("%-18s %-8s %7s %7s %7s %7s %7s %7s %7s" % ("module", "side", "logic", "decl", "struct", "stage", "valid", "instr", "untch"))
    for r in rows:
        for side in ("verilog", "tlv", "gensv"):
            if r[side + "_chars_total"] == "":
                continue
            print("%-18s %-8s %7d %7d %7d %7d %7d %7d %7d" % (
                r["module"], side, r[side + "_chars_logic"], r[side + "_chars_declarations"],
                r[side + "_chars_structure"], r[side + "_chars_staging"], r[side + "_chars_validity"],
                r[side + "_chars_instrumentation"], r[side + "_chars_untouched"]))


def write_csv(rows, path):
    with open(path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        for r in rows:
            w.writerow(r)


# Stacked bars in the style of the ICCD 2017 Fig. 11 / Fig. 13: per set, Orig SV, TLV,
# and Gen SV, each stacked by category, y in kCharacters. Comments and whitespace sit
# on top in greys so the code portion reads as the paper's excluded-ws/comments total.
def write_png(rows, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Patch

    colors = {"logic": "#2a78d6", "declarations": "#eb6834", "structure": "#1baf7a",
              "staging": "#eda100", "validity": "#e87ba4", "instrumentation": "#008300",
              "untouched": "#4a3aa7", "comments": "#b9b8b1", "whitespace": "#e3e2dc"}
    labels = {"logic": "Logic", "declarations": "Declarations", "structure": "Structure",
              "staging": "Staging", "validity": "Validity", "instrumentation": "Instrumentation",
              "untouched": "Untouched (SV inside TLV)", "comments": "Comments", "whitespace": "Whitespace"}
    sides = [("verilog", "Orig SV"), ("tlv", "TLV"), ("gensv", "Gen SV")]
    width = 0.26
    fig, ax = plt.subplots(figsize=(max(10, 1.15 * len(rows) + 2), 6.2))
    x0 = 0.0
    xt = []
    xl = []
    for r in rows:
        for j, (side, lab) in enumerate(sides):
            if r[side + "_chars_total"] == "":
                continue
            base = 0.0
            x = x0 + (j - 1) * (width + 0.03)
            for c in CATEGORIES:
                v = r[side + "_chars_" + c] / 1000.0
                if v <= 0:
                    continue
                ax.bar(x, v, width, bottom=base, color=colors[c], edgecolor="#fcfcfb", linewidth=0.8)
                base += v
            ax.text(x, base + 0.05, lab, ha="center", va="bottom", fontsize=6.5, rotation=90, color="#52514e")
        xt.append(x0)
        xl.append(r["module"])
        x0 += 1.0
    ax.set_xticks(xt)
    ax.set_xticklabels(xl, rotation=35, ha="right", fontsize=9)
    ax.set_ylabel("kCharacters")
    ax.set_title("Code comparison, ICCD 2017 methodology: hand-written Verilog vs TL-Verilog vs SandPiper output", fontsize=10)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.yaxis.grid(True, color="#e3e2dc", linewidth=0.6)
    ax.set_axisbelow(True)
    handles = [Patch(facecolor=colors[c], label=labels[c]) for c in CATEGORIES]
    ax.legend(handles=handles, fontsize=8, frameon=False, ncol=3, loc="upper left")
    fig.tight_layout()
    fig.savefig(path, dpi=160)


def main():
    ap = argparse.ArgumentParser(description="ICCD-2017-style character-category code stats for Verilog vs TL-Verilog.")
    ap.add_argument("dirs", nargs="*", help="module conversion directories")
    ap.add_argument("--manifest", help="JSON list of explicit file sets")
    ap.add_argument("--csv")
    ap.add_argument("--png")
    ap.add_argument("--feved", action="store_true", help="prefer fully_feved.tlv over wip.tlv")
    ap.add_argument("--no-gensv", action="store_true")
    ap.add_argument("--dump", help="write a per-character category dump for one set (debugging the rules)")
    args = ap.parse_args()

    sets = sets_from_dirs(args.dirs, args.feved)
    if args.manifest:
        with open(args.manifest) as fh:
            sets += json.load(fh)
    if not sets:
        ap.error("no module dirs or manifest given")
    for s in sets:
        if not s["verilog"] or not s["tlv"]:
            sys.exit("missing orig.sv or wip.tlv for %s" % s["name"])

    if args.dump:
        s = sets[0]
        with open(args.dump, "w") as out:
            for side, files, clf in (("verilog", s["verilog"], classify_verilog_file), ("tlv", s["tlv"], classify_tlv_file)):
                for f in files:
                    text = open(f).read()
                    cats, _ = clf(text)
                    out.write("==== %s %s\n" % (side, f))
                    for ls, le in line_spans(text):
                        letter = {"logic": "L", "declarations": "D", "structure": "S", "staging": "T",
                                  "validity": "V", "instrumentation": "I", "untouched": "U",
                                  "whitespace": ".", "comments": "c", None: "?"}
                        tags = "".join(letter[cats[k]] for k in range(ls, le))
                        out.write(text[ls:le] + "\n" + tags + "\n")
        return

    rows = [measure(s, args.no_gensv) for s in sets]
    print_table(rows)
    if args.csv:
        write_csv(rows, args.csv)
    if args.png:
        write_png(rows, args.png)


if __name__ == "__main__":
    main()
