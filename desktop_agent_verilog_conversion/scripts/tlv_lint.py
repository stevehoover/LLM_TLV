#!/usr/bin/env python3

# Mechanical lint for the TL-Verilog and .eqy files of one conversion module directory.
#
# Usage: ./tlv_lint.py [--strict] <module-dir>
#        ./tlv_lint.py [--strict] --tlv <file.tlv> [<file.tlv> ...]
#
# The first form checks <module-dir>/wip.tlv and every <module-dir>/fev*.eqy. The second form
# checks stand-alone .tlv files (no .eqy checks), for running the lint over reference corpora.
# --strict adds spec-conformance rules that SandPiper itself does not enforce (see ID-SHORT).
#
# fev.sh runs this before SandPiper so that whole classes of errors are reported locally, in
# milliseconds, instead of after a SandPiper-SaaS round trip. The rules are purely textual;
# nothing is elaborated. Each rule cites the section of the TL-Verilog (TL-X 1d) spec, or of
# the TL-Verilog Macro Preprocessor User Guide, that it enforces. Every rule was checked against
# sandpiper-saas 1.14 with small probe files and against the proven serv conversions, the
# Makerchip tutorial and example corpora, and warp-v, which must all lint clean.
#
#   ID-SHORT         A $sig, /hier, or |pipe name must begin with at least two letters (spec 7.1).
#                    SandPiper rejects /x and |p but accepts $a, $a1 and $i_trap, so for $ names
#                    only the bare single-letter form ($a, $q1) is reported, and only with --strict.
#   ID-CASE          A /hier or |pipe name is lowercase; a leading capital is rejected by SandPiper
#                    (spec 7.1, 7.4). A capital inside a name ($subOp) is accepted and not reported.
#   ID-KEYWORD       An ALL-CAPS $ name is a keyword slot; only $ANY and $RETAIN are keywords
#                    (spec 7, 7.4). Case is part of the identifier type: $foo is a pipesignal,
#                    $Foo a state signal, $FOO a keyword.
#   ID-STATE-ASSIGN  $CamelCase is a state signal and must be assigned with <= or an explicit
#                    alignment such as <<1 (spec 16.1).
#   REGION-END       A non-comment line at column 0 ends a \TLV or \SV_plus region, silently
#                    turning the rest of the region into SystemVerilog (spec 5.2, 5.3).
#   INDENT-3         Scope and statement lines in a \TLV region are indented in steps of three
#                    spaces (spec 9.1).
#   INDENT-TAB       Tabs are forbidden in TL-X regions (spec 9.1).
#   BAD-SCOPE        The first element of a reference path must name an ancestor of the current
#                    scope (looked up by name) or one of its children; there is no way to reach a
#                    sibling except through the common ancestor (spec 16.4, 10).
#   SCOPE-DUP        A hierarchy or pipeline name must differ from every ancestor's, because
#                    ancestor lookup is by name (spec 10).
#   ALIGN-PLACE      The alignment (<>0, >>N, <<N) goes at the end of the path, immediately
#                    before $sig (spec 16.4).
#   M5-QUOTE         M5 quotes [' and '] must balance within a region (Macros Guide 9).
#   M5-CONT-INDENT   Continuation lines of a multi-line m5+ call are indented past the call; the
#                    guide says exactly three spaces (Macros Guide 5.3, 5.4). SandPiper accepts any
#                    deeper indentation and fails at the call's own indentation, which is what is
#                    reported.
#   M5-ARG-COMMENT   // is not a comment to M5, so it cannot appear inside an argument list
#                    (Macros Guide 5.3, 12).
#
# Scope resolution builds the logical scope tree from indentation, merging all lexical occurrences
# of a scope (TL-X scope is reentrant, spec 9.3). Locally defined \TLV macros are expanded at
# their m5+ call sites for the purpose of scope resolution only, and \TLV macros in locally
# included files (m4_include_lib of a relative path) are read for expansion too. Library macros
# can create scopes this lint cannot see, so BAD-SCOPE reports only the sibling pattern: the first
# path element is neither an ancestor nor a child, but a scope of that name hangs off an ancestor.
# Nothing is reported inside \TLV blocks passed as macro arguments, inside macros that are never
# called in the file, or under a macro-named scope such as /m5_RING_STOP_HIER.
#
# Output: nothing and exit status 0 when clean; one line per finding, in the form
#     <file>:<line>: <RULE>: <message> (spec <section>)
# and exit status 1 when there are findings; exit status 2 if the module directory is malformed.

import os
import re
import sys

STRICT = False
DOLLAR_KEYWORDS = ("ANY", "RETAIN")
MACRO_NAME_RE = re.compile(r"[mM][45]_")
SCOPE_LINE_RE = re.compile(r"^([/|])([A-Za-z_]\w*)")
STAGE_LINE_RE = re.compile(r"^@(-?\d+|\+\+|\+=-?\d+)\s*$")
WHEN_LINE_RE = re.compile(r"^\?(\$\$?|\*)[A-Za-z_]\w*\s*$")
BLOCK_LINE_RE = re.compile(r"^\\([A-Za-z_]\w*)(.*)$")
REGION_HEADER_RE = re.compile(r"^\\([A-Za-z_]\w*)(.*)$")
MACRO_DEF_RE = re.compile(r"^\\TLV\s+(\w+)\s*\(([^)]*)\)\s*$")
DOLLAR_RE = re.compile(r"(?<![\\$])\$(\$?)(\^?)([A-Za-z_]\w*)")
ALIGN_RE = re.compile(r"(<>|>>|<<)-?\d+")
M5_CALL_START_RE = re.compile(r"(?<![\w.])m[45]([_+])([A-Za-z_]\w*)\(")
M5_PLUS_CALL_RE = re.compile(r"^m[45]\+([A-Za-z_]\w*)\((.*)\)\s*$")
STATE_ASSIGN_RE = re.compile(r"^\$\$?([A-Z][A-Za-z0-9_]*)(\[[^\]]*\])?\s*=[^=]")
INCLUDE_RE = re.compile(r"m[45]_(?:include_lib|include_url|include)\(\['([^']+)'\]\)")
BLANK_BLOCK_ARG_RE = re.compile(r"^\\TLV\s*$")
OPAQUE_BLOCKS = ("viz_js", "viz_alpha")
SV_BLOCKS = ("SV_plus", "always_comb")


# One finding, printed as <file>:<line>: <RULE>: <message> (spec <section>).
class Finding:
    # file and line locate the finding; rule is the short rule name; spec is the section cited.
    def __init__(self, file, line, rule, msg, spec):
        self.file = file
        self.line = line
        self.rule = rule
        self.msg = msg
        self.spec = spec

    # Identity for deduplication (the same line can be reached by several passes).
    def key(self):
        return (self.file, self.line, self.rule, self.msg)

    # The output line format.
    def __str__(self):
        return f"{self.file}:{self.line}: {self.rule}: {self.msg} (spec {self.spec})"


# A node of the logical behavioral scope tree: the root (/top) or a /hier or |pipe scope.
class Node:
    # sigil is "/" or "|"; parent is None only for the root.
    def __init__(self, sigil, name, parent):
        self.sigil = sigil
        self.name = name
        self.parent = parent
        self.children = {}

    # The key by which a scope is looked up: sigil plus name, e.g. "/cnt_w1" or "|default".
    def key(self):
        return self.sigil + self.name

    # Return the child with the given key, creating it if needed.
    def child(self, sigil, name):
        k = sigil + name
        if k not in self.children:
            self.children[k] = Node(sigil, name, self)
        return self.children[k]

    # The full path from the root, e.g. "/top/serv_rf_ram_if|default".
    def path(self):
        parts = []
        n = self
        while n.parent is not None:
            parts.append(n.key())
            n = n.parent
        return "/top" + "".join(reversed(parts))

    # All nodes below (and including) this one whose key matches.
    def find_all(self, key):
        found = [self] if self.key() == key else []
        for c in self.children.values():
            found.extend(c.find_all(key))
        return found


# A locally defined \TLV macro: its parameter list and body lines (with original line numbers).
class Macro:
    # report_refs: whether references inside the body are reported when it is expanded. False for
    # macros read from an included file, which are proven separately.
    def __init__(self, name, params, file, report_refs=True):
        self.name = name
        self.params = params
        self.file = file
        self.report_refs = report_refs
        self.body = []      # list of (lineno, raw)


# Compute the indentation of a raw line, counting a column-0 '!' line-type character as a space
# (spec 6, 9.1). Returns (indent, rest) where rest is the text after the indentation.
def indentation(raw):
    i = 0
    if raw.startswith("!"):
        i = 1
    while i < len(raw) and raw[i] in " \t":
        i += 1
    return i, raw[i:]


# Strip HDL comments and double-quoted strings from one line so that only code is scanned.
# in_block: whether the line starts inside a /* */ comment.
# Returns (code, in_block_after, comment_pos) where comment_pos is the index in the original line
# at which a // comment was cut, or None. A // inside an M5 quote opened on the same line is not
# treated as a comment (a URL inside m4_include_url(['https://...']) is the common case).
def strip_comments(raw, in_block):
    out = []
    i = 0
    n = len(raw)
    quote = 0
    comment_pos = None
    while i < n:
        if in_block:
            j = raw.find("*/", i)
            if j < 0:
                return "".join(out), True, comment_pos
            i = j + 2
            in_block = False
            out.append(" ")
            continue
        c = raw[i]
        if raw.startswith("['", i):
            quote += 1
            out.append("['")
            i += 2
        elif raw.startswith("']", i):
            if quote > 0:
                quote -= 1
            out.append("']")
            i += 2
        elif c == '"':
            j = i + 1
            while j < n and raw[j] != '"':
                if raw[j] == "\\":
                    j += 1
                j += 1
            out.append('""')
            i = j + 1
        elif raw.startswith("/*", i):
            in_block = True
            i += 2
        elif raw.startswith("//", i) and quote == 0:
            comment_pos = i
            break
        else:
            out.append(c)
            i += 1
    return "".join(out), in_block, comment_pos


# Check a $-prefixed name. Returns (rule, message, spec) or None.
def check_dollar_name(name):
    if name.startswith("_") or MACRO_NAME_RE.search(name):
        return None
    if re.fullmatch(r"[A-Z][A-Z0-9_]*", name):
        if name in DOLLAR_KEYWORDS:
            return None
        return ("ID-KEYWORD",
                f"${name}: an ALL-CAPS $ name is reserved for keywords (only ${' and $'.join(DOLLAR_KEYWORDS)} exist). "
                f"Case is part of the identifier type: $lower_case is a pipesignal, $CamelCase is a state signal, "
                f"$UPPER_CASE is a keyword. For a pipesignal write ${name.lower()}",
                "7, 7.4")
    if name[0].isupper():
        return None
    # The spec requires two leading letters for every name. SandPiper 1.14 accepts $a, $a1 and
    # $i_trap (the serv conversions use $i_*/$o_* names throughout, and the Makerchip examples use
    # $a), so this is a spec-conformance rule, reported only with --strict.
    if STRICT and re.fullmatch(r"[a-z][0-9]*", name):
        return ("ID-SHORT",
                f"${name}: a pipesignal name must begin with at least two lowercase letters; "
                f"${name[0]}{name} is legal",
                "7.1")
    return None


# Check a /hier or |pipe scope name. Returns (rule, message, spec) or None.
def check_scope_name(sigil, name):
    if name.startswith("_") or MACRO_NAME_RE.search(name):
        return None
    kind = "hierarchy" if sigil == "/" else "pipeline"
    if len(name) < 2 or not name[0].isalpha() or not name[1].isalpha():
        return ("ID-SHORT",
                f"{sigil}{name}: a {kind} name must begin with at least two letters; "
                f"{sigil}{name[0]}{name} is legal",
                "7.1")
    if name[0].isupper():
        return ("ID-CASE",
                f"{sigil}{name}: a {kind} name is lowercase (spec lists /beh_hier and |pipeline); a leading "
                f"capital is a different identifier type. Write {sigil}{name[0].lower()}{name[1:]}",
                "7.1, 7.4")
    return None


# Map a scope name written through the tlv_lib hierarchy convention to the name M5 produces:
# m5_define_hier(YY, 10) makes /m5_YY_HIER expand to /yy[9:0] (likewise M4_YY_HIER, M5_YY_HIER).
# Other names are returned unchanged.
def hier_name(name):
    m = re.fullmatch(r"[mM][45]_(\w+)_HIER", name)
    return m.group(1).lower() if m else name


# Skip a balanced [...] starting at code[i] == '['. Returns the index after the closing bracket
# (or len(code) if unbalanced).
def skip_brackets(code, i):
    depth = 0
    n = len(code)
    while i < n:
        c = code[i]
        if c == "\\":
            i += 2
            continue
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return n


# Find every scoped pipesignal reference in a line of code. Yields dicts with:
#   elems: list of (sigil, name) path elements, in order
#   align: the alignment text (e.g. "<>0") or ""
#   misplaced: True if an alignment was followed by more path instead of $ (ALIGN-PLACE)
#   sig: the signal name after $, or None when misplaced
# Bracketed index expressions are scanned recursively, since they may contain references.
def find_refs(code):
    refs = []
    i = 0
    n = len(code)
    while i < n:
        c = code[i]
        if c in "/|" and i + 1 < n and (code[i + 1].isalpha() or code[i + 1] == "_") and \
                (i == 0 or (code[i - 1] not in "\\$" and not code[i - 1].isalnum() and code[i - 1] != "_")):
            j = i
            elems = []
            while j < n and code[j] in "/|" and j + 1 < n and (code[j + 1].isalpha() or code[j + 1] == "_"):
                sigil = code[j]
                m = re.match(r"[A-Za-z_]\w*", code[j + 1:])
                name = m.group(0)
                j += 1 + len(name)
                if sigil == "/" and j < n and code[j] == "[":
                    end = skip_brackets(code, j)
                    refs.extend(find_refs(code[j + 1:end - 1]))
                    j = end
                elems.append((sigil, hier_name(name)))
            m = ALIGN_RE.match(code, j)
            align = ""
            if m:
                align = m.group(0)
                j = m.end()
            if j < n and code[j] == "$":
                m = re.match(r"\$\$?\^?([A-Za-z_]\w*)", code[j:])
                if m:
                    refs.append({"elems": elems, "align": align, "misplaced": False, "sig": m.group(1)})
                    j += m.end()
            elif align and j < n and code[j] in "/|" and j + 1 < n and code[j + 1].isalpha():
                refs.append({"elems": elems, "align": align, "misplaced": True, "sig": None})
            i = max(j, i + 1)
        else:
            i += 1
    return refs


# Split an M5 argument list at top-level commas, honoring [' '] quotes and parentheses.
def split_m5_args(text):
    args = []
    cur = []
    depth = 0
    quote = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("['", i):
            quote += 1
            cur.append("['")
            i += 2
            continue
        if text.startswith("']", i):
            quote = max(0, quote - 1)
            cur.append("']")
            i += 2
            continue
        c = text[i]
        if quote == 0:
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            elif c == "," and depth == 0:
                args.append("".join(cur).strip())
                cur = []
                i += 1
                continue
        cur.append(c)
        i += 1
    args.append("".join(cur).strip())
    return args


# Walks the lines of a \TLV or \SV_plus region, maintaining the indentation-driven scope stack and
# the logical scope tree, and resolving scoped references against them.
class ScopeWalker:
    # scope_checks: report BAD-SCOPE. False for the definition pass of a macro, whose instantiation
    # context is unknown until it is expanded at a call site.
    def __init__(self, root, findings, macros, scope_checks):
        self.root = root
        self.findings = findings
        self.macros = macros
        self.scope_checks = scope_checks
        self.stack = []     # entries: dict(indent, kind, node, name)
        self.depth = 0

    # Reset the stack at a region boundary.
    def reset(self):
        self.stack = []

    # The behavioral scope node of the innermost open scope.
    def node(self):
        for e in reversed(self.stack):
            if e["node"] is not None:
                return e["node"]
        return self.root

    # The innermost open block entry (SV_plus, always_comb, opaque, or a \TLV block argument) whose
    # body contains the current line. Scope entries may sit above a \TLV block argument on the stack.
    def block(self):
        for e in reversed(self.stack):
            if e["kind"] in ("sv_block", "opaque", "tlvblock"):
                return e
        return None

    # The indentation of the outermost open \TLV block argument containing the current line, or
    # None. Anything inside such a block (including nested \SV_plus blocks) is macro argument text.
    def tlv_block_indent(self):
        for e in self.stack:
            if e["kind"] == "tlvblock":
                return e["indent"]
        return None

    # Record a finding.
    def add(self, file, line, rule, msg, spec):
        self.findings.append(Finding(file, line, rule, msg, spec))

    # Feed one code line. Pops the stack to the line's indentation, classifies the line, pushes a
    # scope or block entry when appropriate, and (when check_refs) resolves the references on it.
    # Returns a dict describing the line: kind in {scope, stage, when, block, statement}, and the
    # block entry the line sits in (None if not inside a block body).
    def feed(self, file, lineno, indent, code, check_refs=True, check_names=True):
        while self.stack and self.stack[-1]["indent"] >= indent:
            self.stack.pop()
        blk = self.block()
        info = {"kind": "statement", "block": blk, "scope_line": False}
        if blk is not None and blk["kind"] == "opaque":
            return info
        if self.tlv_block_indent() is not None:
            # A \TLV block passed as a macro argument is instantiated wherever the macro puts it,
            # so its references cannot be resolved here.
            check_refs = False
        stripped = code.strip()
        if blk is None or blk["kind"] == "tlvblock":
            m = SCOPE_LINE_RE.match(stripped)
            if m:
                rest = stripped[m.end():]
                if m.group(1) == "/" and rest.startswith("["):
                    rest = rest[skip_brackets(rest, 0):]
                if rest.strip() == "":
                    sigil, name = m.group(1), m.group(2)
                    info["kind"] = "scope"
                    info["scope_line"] = True
                    if check_names:
                        r = check_scope_name(sigil, name)
                        if r:
                            self.add(file, lineno, r[0], r[1], r[2])
                    name = hier_name(name)
                    parent = self.node()
                    # Like BAD-SCOPE, only in live code: the main regions and expansions of macros
                    # that are called there (a macro never called is dead text).
                    if check_refs and self.scope_checks and not name.startswith("_") and \
                            not MACRO_NAME_RE.search(name):
                        n = parent
                        while n is not None and n.parent is not None:
                            if n.sigil == sigil and n.name == name:
                                self.add(file, lineno, "SCOPE-DUP",
                                         f"{sigil}{name} is declared inside {n.path()}; a scope name must differ "
                                         f"from every ancestor's, because references look ancestors up by name",
                                         "10")
                                break
                            n = n.parent
                    node = parent.child(sigil, name)
                    self.stack.append({"indent": indent, "kind": "scope", "node": node, "name": sigil + name})
                    return info
            if STAGE_LINE_RE.match(stripped):
                info["kind"] = "stage"
                info["scope_line"] = True
                return info
            if WHEN_LINE_RE.match(stripped):
                info["kind"] = "when"
                info["scope_line"] = True
                if check_refs:
                    self.check_refs(file, lineno, stripped)
                return info
            m = BLOCK_LINE_RE.match(stripped)
            if m:
                kw = m.group(1)
                info["kind"] = "block"
                info["scope_line"] = True
                if kw in SV_BLOCKS:
                    self.stack.append({"indent": indent, "kind": "sv_block", "node": None, "name": kw})
                elif kw == "TLV":
                    self.stack.append({"indent": indent, "kind": "tlvblock", "node": None, "name": kw})
                elif kw in ("source", "end_source"):
                    pass
                else:
                    self.stack.append({"indent": indent, "kind": "opaque", "node": None, "name": kw})
                return info
        if check_refs:
            self.check_refs(file, lineno, code)
        return info

    # Resolve every scoped reference in code against the current scope.
    def check_refs(self, file, lineno, code, ctx=None):
        if ctx is None:
            ctx = self.node()
        for ref in find_refs(code):
            path = "".join(s + n for s, n in ref["elems"])
            if ref["misplaced"]:
                self.add(file, lineno, "ALIGN-PLACE",
                         f"{path}{ref['align']}...: the alignment {ref['align']} belongs at the end of the path, "
                         f"immediately before $sig (e.g. /rf_ram_if|default<>0$rgnt, not |default<>0/rf_ram_if$rgnt)",
                         "16.4")
                continue
            self.resolve(file, lineno, ctx, ref)

    # Resolve one reference: the first path element must be /top, an ancestor of ctx (by name,
    # including ctx itself), or a child of ctx. Descent below that is not checked when a child is
    # unknown, since it may be declared in a library or by a macro that is not expanded here.
    def resolve(self, file, lineno, ctx, ref):
        elems = ref["elems"]
        if not elems:
            return
        sigil, name = elems[0]
        if name.startswith("_") or MACRO_NAME_RE.search(name):
            return
        key = sigil + name
        if key == "/top":
            node = self.root
        else:
            node = None
            n = ctx
            while n is not None:
                if n.key() == key:
                    node = n
                    break
                n = n.parent
            if node is None:
                node = ctx.children.get(key)
            if node is None:
                # Report only the sibling pattern: a scope of that name hangs off an ancestor of
                # ctx. Scopes elsewhere in the tree may be reachable through macro-created scopes
                # this lint cannot see, and a macro-named or parameter-named ancestor means the
                # ancestor chain itself is unknown.
                ancestors = []
                n = ctx
                while n is not None:
                    ancestors.append(n)
                    n = n.parent
                if any(a.parent is not None and (a.name.startswith("_") or MACRO_NAME_RE.search(a.name))
                       for a in ancestors):
                    return
                # A macro-named child (other than the m5_X_HIER convention, mapped above) means the
                # set of children is unknown.
                if any(c.name.startswith("_") or MACRO_NAME_RE.search(c.name) for c in ctx.children.values()):
                    return
                # From the top-level scope (an \SV_plus region or an .eqy match line) there are
                # no unknown ancestors, so any deeper scope of that name is a wrong path.
                others = [n for n in self.root.find_all(key)
                          if n is not self.root and (ctx is self.root or n.parent in ancestors[1:])]
                if others and self.scope_checks:
                    rest = "".join(s + n for s, n in elems[1:])
                    fix = others[0].path() + rest + ref["align"] + "$" + ref["sig"]
                    self.add(file, lineno, "BAD-SCOPE",
                             f"{key}{rest}{ref['align']}${ref['sig']}: from inside {ctx.path()}, {key} is neither an "
                             f"ancestor nor a child scope (it is {others[0].path()}). A path starts at an ancestor by "
                             f"name or at a child; there is no way to name a sibling except through the common "
                             f"ancestor. Write {fix}",
                             "16.4, 10")
                return
        for sigil, name in elems[1:]:
            if name.startswith("_") or MACRO_NAME_RE.search(name):
                return
            node = node.children.get(sigil + name)
            if node is None:
                return

    # Expand a locally defined macro at a call site for scope resolution: feed its body lines with
    # their indentation rebased to the call's, after substituting simple parameters. Findings are
    # reported at the macro definition's own lines.
    def expand(self, macro, args, call_indent, file, check_refs=None):
        if self.depth > 4:
            return
        if check_refs is None:
            check_refs = macro.report_refs
        params = [p.strip() for p in macro.params.split(",")] if macro.params.strip() else []
        subs = []
        if len(params) == len(args):
            for p, a in zip(params, args):
                if p and re.fullmatch(r"[^\w\s]*\w+", p) and a and "['" not in a and " " not in a:
                    subs.append((re.compile(r"(?<![\w])" + re.escape(p) + r"(?![\w])"), a))
        saved = list(self.stack)
        self.depth += 1
        in_block = False
        for lineno, raw in macro.body:
            code, in_block, _ = strip_comments(raw, in_block)
            if not code.strip():
                continue
            ind, _ = indentation(raw)
            for rx, a in subs:
                code = rx.sub(a, code)
            info = self.feed(macro.file, lineno, ind - 3 + call_indent, code, check_refs=check_refs,
                             check_names=False)
            m = M5_PLUS_CALL_RE.match(code.strip())
            if m and m.group(1) in self.macros and info["block"] is None:
                inner = self.macros[m.group(1)]
                self.expand(inner, split_m5_args(m.group(2)), ind - 3 + call_indent, file,
                            check_refs=check_refs and inner.report_refs)
        self.depth -= 1
        self.stack = saved


# Read the \TLV macro definitions of a file, for expansion only. Returns {name: Macro}.
def read_macros(path, report_refs):
    macros = {}
    cur = None
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            lines = f.read().splitlines()
    except OSError:
        return macros
    for i, raw in enumerate(lines, 1):
        if raw.startswith("\\"):
            m = MACRO_DEF_RE.match(raw)
            if m:
                cur = Macro(m.group(1), m.group(2), path, report_refs)
                macros[cur.name] = cur
            else:
                cur = None
            continue
        if cur is not None:
            if raw.strip() and not raw.startswith((" ", "!", "\t")) and not raw.lstrip().startswith(("//", "/*")):
                cur = None
                continue
            cur.body.append((i, raw))
    return macros


# Pass 1 of lint_tlv: walk every \TLV, \SV_plus and macro region with all checks off, so that the
# logical scope tree (including expansions of local macro calls) is complete before any reference
# is resolved in pass 2. A scope may be declared after the line that references it.
def prebuild_tree(lines, macros, main_walker, macro_walkers, findings):
    region = "none"
    walker = main_walker
    in_block_comment = False
    for raw in lines:
        if raw.startswith("\\"):
            m = REGION_HEADER_RE.match(raw)
            kw = m.group(1) if m else ""
            in_block_comment = False
            if kw == "TLV":
                md = MACRO_DEF_RE.match(raw)
                if md:
                    region = "macro"
                    r = Node("/", "top", None)
                    walker = macro_walkers.setdefault(md.group(1), ScopeWalker(r, findings, macros, False))
                else:
                    region = "tlv"
                    walker = main_walker
            elif kw == "SV_plus":
                region = "sv_plus"
                walker = main_walker
            else:
                region = "other"
            walker.reset()
            continue
        if region not in ("tlv", "sv_plus", "macro"):
            continue
        code, in_block_comment, _ = strip_comments(raw, in_block_comment)
        if not code.strip():
            continue
        indent, _ = indentation(raw)
        if indent == 0 and not raw.startswith("!"):
            if region != "sv_plus" or "$" in code:
                region = "sv"
            continue
        info = walker.feed("", 0, indent, code, check_refs=False, check_names=False)
        m = M5_PLUS_CALL_RE.match(code.strip())
        if m and m.group(1) in macros and walker.scope_checks and info["block"] is None:
            walker.expand(macros[m.group(1)], split_m5_args(m.group(2)), indent, "", check_refs=False)


# Lint one TL-Verilog file. Returns (findings, root) where root is the main scope tree, used to
# check .eqy match lines against wip.tlv.
def lint_tlv(path, display_name, module_dir, extra_macros=None):
    findings = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError as ex:
        print(f"ERROR: cannot read {path}: {ex}")
        sys.exit(2)
    lines = text.splitlines()
    m5_enabled = bool(lines) and bool(re.match(r"^\\m[45]_TLV_version", lines[0]))

    # Record a finding against this file.
    def add(line, rule, msg, spec):
        findings.append(Finding(display_name, line, rule, msg, spec))

    # Macros defined in this file (linted here) and in locally included files (expansion only).
    macros = read_macros(path, report_refs=True)
    for mac in macros.values():
        mac.file = display_name
    if extra_macros:
        for k, v in extra_macros.items():
            macros.setdefault(k, v)
    if module_dir is not None:
        for m in INCLUDE_RE.finditer(text):
            inc = m.group(1)
            if "://" in inc:
                continue
            inc_path = os.path.normpath(os.path.join(module_dir, inc))
            if os.path.isfile(inc_path) and os.path.abspath(inc_path) != os.path.abspath(path):
                for k, v in read_macros(inc_path, report_refs=False).items():
                    macros.setdefault(k, v)

    root = Node("/", "top", None)
    main_walker = ScopeWalker(root, findings, macros, True)

    # M5 quote balance, on raw text with M5 line comments removed, across the whole file.
    if m5_enabled:
        depth = 0
        open_line = None
        for i, raw in enumerate(lines, 1):
            if raw.startswith("\\") and depth != 0:
                add(open_line, "M5-QUOTE", "an M5 quote [' opened here is not closed before the next region header",
                    "Macros Guide 9")
                depth = 0
                open_line = None
            t = raw.split("///", 1)[0]
            j = 0
            while j < len(t):
                if t.startswith("['", j):
                    if depth == 0:
                        open_line = i
                    depth += 1
                    j += 2
                elif t.startswith("']", j):
                    depth -= 1
                    if depth < 0:
                        add(i, "M5-QUOTE", "an M5 close quote '] has no matching open quote ['", "Macros Guide 9")
                        depth = 0
                    j += 2
                else:
                    j += 1
        if depth != 0:
            add(open_line, "M5-QUOTE", "an M5 quote [' opened here is not closed by end of file", "Macros Guide 9")

    # Pass 1: complete the scope tree. Pass 2: region-by-region walk with every check.
    macro_walkers = {}
    prebuild_tree(lines, macros, main_walker, macro_walkers, findings)
    region = "none"          # none, sv, m5, tlv, sv_plus, macro, unknown
    walker = main_walker
    in_block_comment = False
    terminated = True
    call = None              # open multi-line M5 call state
    for i, raw in enumerate(lines, 1):
        if raw.startswith("\\"):
            m = REGION_HEADER_RE.match(raw)
            kw = m.group(1) if m else ""
            if call is not None:
                call = None
            in_block_comment = False
            terminated = True
            if kw == "TLV":
                md = MACRO_DEF_RE.match(raw)
                if md:
                    # A macro body is walked on its own tree, without BAD-SCOPE: its instantiation
                    # context is only known when it is expanded at a local m5+ call site.
                    region = "macro"
                    r = Node("/", "top", None)
                    walker = macro_walkers.setdefault(md.group(1), ScopeWalker(r, findings, macros, False))
                else:
                    region = "tlv"
                    walker = main_walker
            elif kw == "SV_plus":
                region = "sv_plus"
                walker = main_walker
            elif kw == "SV":
                region = "sv"
            elif kw in ("m4", "m5"):
                region = "m5"
            elif kw.endswith("TLV_version"):
                region = "none"
            else:
                region = "unknown"
            walker.reset()
            continue
        if region not in ("tlv", "sv_plus", "macro"):
            continue

        code, in_block_comment, comment_pos = strip_comments(raw, in_block_comment)
        if not code.strip():
            continue
        indent, _ = indentation(raw)

        # Column-0 code ends the region (spec 5.2, 5.3). In an \SV_plus region the remainder is
        # SystemVerilog either way, so only a column-0 line carrying $ references is a trap there.
        if indent == 0 and not raw.startswith("!") and (region != "sv_plus" or "$" in code):
            head = code.strip()[:40]
            add(i, "REGION-END",
                f"'{head}' at column 0 ends the \\{'SV_plus' if region == 'sv_plus' else 'TLV'} region here; everything "
                f"after it is treated as SystemVerilog. TL-Verilog code must be indented (first level: three spaces)",
                "5.2, 5.3" if region == "sv_plus" else "5.3, 9.1")
            region = "sv"
            continue

        has_tab = "\t" in code or "\t" in raw[:indent]
        if has_tab:
            add(i, "INDENT-TAB", "tabs are forbidden in TL-X regions; use spaces", "9.1")

        # Scope tracking and reference resolution (BAD-SCOPE only on the main tree and expansions).
        info = walker.feed(display_name, i, indent, code, check_refs=True, check_names=True)
        blk = info["block"]
        if blk is not None and blk["kind"] == "opaque":
            continue
        in_sv_body = blk is not None and blk["kind"] == "sv_block"
        stripped = code.strip()

        # Multi-line M5 call tracking: continuation indentation and // inside argument lists.
        in_tlv_arg = False
        call_open_before = call is not None
        if call is not None:
            if walker.tlv_block_indent() == call["indent"] + 3:
                in_tlv_arg = True
            elif call["quote"] == 0 and call["plus"]:
                # The guide says exactly three spaces past the call. SandPiper accepts any deeper
                # indentation (probed at +1, +3, +6) and fails at the call's own indentation, so
                # only the latter is reported.
                if indent <= call["indent"]:
                    add(i, "M5-CONT-INDENT",
                        f"continuation line of the m5+{call['name']}(...) call on line {call['line']} is indented "
                        f"{indent} spaces, not past the call; it must be indented exactly three spaces past the call "
                        f"({call['indent'] + 3}), or the call sees a truncated argument list",
                        "Macros Guide 5.3, 5.4")
        if m5_enabled and not in_tlv_arg:
            j = 0
            n = len(code)
            while j < n:
                if call is None:
                    m = M5_CALL_START_RE.search(code, j)
                    if not m:
                        break
                    call = {"name": m.group(2), "plus": m.group(1) == "+", "indent": indent, "line": i,
                            "paren": 1, "quote": 0, "at_start": code[:m.start()].strip() == ""}
                    j = m.end()
                    continue
                if code.startswith("['", j):
                    call["quote"] += 1
                    j += 2
                elif code.startswith("']", j):
                    call["quote"] = max(0, call["quote"] - 1)
                    j += 2
                elif call["quote"] == 0 and code[j] == "(":
                    call["paren"] += 1
                    j += 1
                elif call["quote"] == 0 and code[j] == ")":
                    call["paren"] -= 1
                    j += 1
                    if call["paren"] == 0:
                        if call["at_start"] and call["line"] != i:
                            terminated = True
                        call = None
                else:
                    j += 1
            if call is not None and call["quote"] == 0 and comment_pos is not None and \
                    not raw.startswith("///", comment_pos):
                add(i, "M5-ARG-COMMENT",
                    f"// inside the argument list of m5{'+' if call['plus'] else '_'}{call['name']}(...): M5 does not "
                    f"treat // as a comment, so it becomes part of the argument. Comments are not allowed inside an "
                    f"argument list",
                    "Macros Guide 5.3, 12")

        # Indentation in steps of three (spec 9.1): scope lines always; statements when they start
        # a statement (previous statement terminated); not inside HDL block bodies or M5 calls.
        if region != "sv_plus" and not in_sv_body and not in_tlv_arg and not has_tab:
            if info["scope_line"] or (terminated and not call_open_before):
                if indent % 3 != 0:
                    add(i, "INDENT-3",
                        f"indentation of {indent} spaces is not a multiple of three; one level of scope is three "
                        f"spaces (a column-0 '!' counts as one)",
                        "9.1")

        # Identifier checks on every $name.
        for m in DOLLAR_RE.finditer(code):
            r = check_dollar_name(m.group(3))
            if r:
                add(i, r[0], r[1], r[2])
        m = STATE_ASSIGN_RE.match(stripped)
        if m and not re.fullmatch(r"[A-Z][A-Z0-9_]*", m.group(1)) and m.group(1)[1:2].isalpha():
            add(i, "ID-STATE-ASSIGN",
                f"${m.group(1)}: the leading capital makes this a state signal, which must be assigned with <= "
                f"(${m.group(1)} <= ...) or an explicit alignment (<<1${m.group(1)} = ...). If a pipesignal was "
                f"intended, name it ${re.sub(r'([a-z0-9])([A-Z])', r'\1_\2', m.group(1)).lower()}",
                "16.1, 7.4")

        # Expand local macro calls for scope resolution.
        m = M5_PLUS_CALL_RE.match(stripped)
        if m and m.group(1) in macros and walker.scope_checks and blk is None:
            walker.expand(macros[m.group(1)], split_m5_args(m.group(2)), indent, display_name)

        # Statement termination for the next line's INDENT-3 decision. A within-line m5_ call that
        # continues an assignment (e.g. "$x =" then "m5_if(...)") does not terminate it.
        if info["scope_line"]:
            terminated = True
        elif call is not None:
            terminated = False
        else:
            s = stripped
            was_terminated = terminated
            terminated = s.endswith(";") or s.endswith("['") or s.startswith("']") or \
                bool(re.match(r"m[45]\+\w+\(.*\)\s*$", s)) or bool(re.match(r"\\[A-Za-z]", s)) or \
                (was_terminated and bool(re.match(r"m[45]_\w+\(.*\)\s*$", s)))

    return findings, root


# Check the [match ...] sections of one .eqy file: gate-side pipesignal references are checked
# for identifier form, alignment placement, and scope against the wip.tlv tree (context: the
# top-level scope, since fev.sh maps them in an \SV_plus region appended to wip.tlv).
def lint_eqy(path, display_name, root, findings):
    walker = ScopeWalker(root, findings, {}, True)
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            lines = f.read().splitlines()
    except OSError as ex:
        print(f"ERROR: cannot read {path}: {ex}")
        sys.exit(2)
    in_match = False
    for i, raw in enumerate(lines, 1):
        if re.match(r"^\[match\b", raw):
            in_match = True
            continue
        if in_match:
            if not raw.strip():
                in_match = False
                continue
            s = raw.strip()
            if s.startswith("#"):
                continue
            parts = s.split()
            if len(parts) < 3:
                continue
            gate = parts[2] if parts[0].startswith("gold") else parts[1]
            for tok in parts[1:3]:
                if "$" not in tok:
                    continue
                for m in DOLLAR_RE.finditer(tok):
                    r = check_dollar_name(m.group(3))
                    if r:
                        findings.append(Finding(display_name, i, r[0], r[1], r[2]))
                if tok == gate:
                    walker.check_refs(display_name, i, tok, ctx=root)
                else:
                    for ref in find_refs(tok):
                        if ref["misplaced"]:
                            walker.check_refs(display_name, i, tok, ctx=root)
                            break


# Process command line arguments, run the checks, print sorted and deduplicated findings, and
# return the exit status (0 clean, 1 findings, 2 malformed module directory or usage).
def main():
    global STRICT
    argv = sys.argv[1:]
    if "--strict" in argv:
        STRICT = True
        argv = [a for a in argv if a != "--strict"]
    findings = []
    if argv and argv[0] == "--tlv":
        if len(argv) < 2:
            print("Usage: ./tlv_lint.py --tlv <file.tlv> [<file.tlv> ...]")
            return 2
        for p in argv[1:]:
            if not os.path.isfile(p):
                print(f"ERROR: {p} is not a file.")
                return 2
            f, _ = lint_tlv(p, p, None)
            findings.extend(f)
    else:
        if len(argv) != 1:
            print("Usage: ./tlv_lint.py <module-dir>  |  ./tlv_lint.py --tlv <file.tlv> [...]")
            return 2
        mdir = argv[0]
        wip = os.path.join(mdir, "wip.tlv")
        if not os.path.isdir(mdir) or not os.path.isfile(wip):
            print(f"ERROR: {mdir} is not a module directory containing wip.tlv.")
            return 2

        # File name as printed in findings: bare when run from the module directory, as fev.sh does.
        def disp(name):
            return name if mdir in (".", "./") else os.path.join(mdir, name)

        f, root = lint_tlv(wip, disp("wip.tlv"), mdir)
        findings.extend(f)
        for name in sorted(os.listdir(mdir)):
            if re.fullmatch(r"fev.*\.eqy", name):
                lint_eqy(os.path.join(mdir, name), disp(name), root, findings)
    seen = set()
    out = []
    for f in findings:
        if f.key() in seen:
            continue
        seen.add(f.key())
        out.append(f)
    out.sort(key=lambda f: (f.file, f.line, f.rule))
    for f in out:
        print(f)
    return 1 if out else 0


if __name__ == "__main__":
    sys.exit(main())
