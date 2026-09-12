#!/usr/bin/env python3
"""Self-contained tests for the edit-format parsers in lib/edits.py.

This file parses the source with ast and execs ONLY the top-level
definitions under test: is_no_change, extract_justification, JUSTIFY_RE,
expand_omissions, SR_BLOCK_RE, apply_search_replace. That keeps the tests
free of any environment setup (no MDIR, no MM_* variables, no network).

Run: python3 tests.py   (no pytest; prints "N/N cases passed", exit 1 on fail)
"""
import ast
import os
import re
import sys

ROUTER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lib", "edits.py")
WANTED = {"is_no_change", "extract_justification", "JUSTIFY_RE",
          "expand_omissions", "SR_BLOCK_RE", "apply_search_replace"}


def load_defs():
    tree = ast.parse(open(ROUTER).read())
    nodes = []
    for node in tree.body:
        names = set()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            names = {node.name}
        elif isinstance(node, ast.Assign):
            names = {t.id for t in node.targets if isinstance(t, ast.Name)}
        if names & WANTED:
            nodes.append(node)
    ns = {"re": re, "os": os}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), ROUTER, "exec"), ns)
    missing = WANTED - set(ns)
    if missing:
        raise RuntimeError(f"could not load from {ROUTER}: {sorted(missing)}")
    return ns


NS = load_defs()
is_no_change = NS["is_no_change"]
extract_justification = NS["extract_justification"]
JUSTIFY_RE = NS["JUSTIFY_RE"]
expand_omissions = NS["expand_omissions"]
SR_BLOCK_RE = NS["SR_BLOCK_RE"]
apply_search_replace = NS["apply_search_replace"]

CASES = []


def case(name):
    def deco(fn):
        CASES.append((name, fn))
        return fn
    return deco


ORIG10 = "\n".join(f"line{i}" for i in range(1, 11))


# ---------------- dots expansion ----------------

@case("dots: single-line replacement mid-file with two ... regions")
def _():
    new = "line1\nline2\n...\nline6\nCHANGED\nline8\n...\nline10"
    want = "line1\nline2\nline3\nline4\nline5\nline6\nCHANGED\nline8\nline9\nline10"
    got = expand_omissions(new, ORIG10)
    assert got == want, f"got {got!r}"


@case("dots: multiple ... regions at both ends of the file")
def _():
    new = "...\nline5\nX\nline7\n..."
    want = "line1\nline2\nline3\nline4\nline5\nX\nline7\nline8\nline9\nline10"
    got = expand_omissions(new, ORIG10)
    assert got == want, f"got {got!r}"


@case("dots: ... mixed with changed lines in one hunk returns None")
def _():
    new = "line1\n...\nCHANGED\nline10"
    got = expand_omissions(new, ORIG10)
    assert got is None, f"expected None, got {got!r}"


@case("dots: no-dots full file passes through unchanged")
def _():
    new = ORIG10.replace("line5", "CHANGED5")
    got = expand_omissions(new, ORIG10)
    assert got == new, f"got {got!r}"


@case("dots: identical file returns identical content")
def _():
    got = expand_omissions(ORIG10, ORIG10)
    assert got == ORIG10, f"got {got!r}"


@case("dots: new file (empty orig) without dots passes through")
def _():
    new = "brandnew1\nbrandnew2"
    got = expand_omissions(new, "")
    assert got == new, f"got {got!r}"


@case("dots: dots against empty orig fail soft to None")
def _():
    got = expand_omissions("a\n...\nb", "")
    assert got is None, f"expected None, got {got!r}"


@case("dots: pure insertion plus ... region expands correctly")
def _():
    new = "line1\nNEWLINE\nline2\n...\nline10"
    want = "line1\nNEWLINE\n" + "\n".join(f"line{i}" for i in range(2, 11))
    got = expand_omissions(new, ORIG10)
    assert got == want, f"got {got!r}"


@case("dots: deletion of a line with surrounding context kept")
def _():
    new = "line1\n...\nline4\nline6\n...\nline10"
    want = "line1\nline2\nline3\nline4\nline6\nline7\nline8\nline9\nline10"
    got = expand_omissions(new, ORIG10)
    assert got == want, f"got {got!r}"


# ---------------- search/replace ----------------

@case("sr: single block applies")
def _():
    body = "<<<<<<< SEARCH\nline5\n=======\nCHANGED5\n>>>>>>> REPLACE"
    out, err = apply_search_replace(body, ORIG10)
    assert err is None, f"err {err!r}"
    assert out == ORIG10.replace("line5", "CHANGED5"), f"got {out!r}"


@case("sr: multiple blocks apply in order")
def _():
    body = ("<<<<<<< SEARCH\nline2\nline3\n=======\nTWO\nTHREE\n>>>>>>> REPLACE\n"
            "<<<<<<< SEARCH\nline8\n=======\nEIGHT\n>>>>>>> REPLACE")
    out, err = apply_search_replace(body, ORIG10)
    assert err is None, f"err {err!r}"
    want = ORIG10.replace("line2\nline3", "TWO\nTHREE").replace("line8", "EIGHT")
    assert out == want, f"got {out!r}"


@case("sr: SEARCH not found returns error mentioning it")
def _():
    body = "<<<<<<< SEARCH\nno_such_line\n=======\nX\n>>>>>>> REPLACE"
    out, err = apply_search_replace(body, ORIG10)
    assert out is None and err and "not found" in err, f"got {out!r}, {err!r}"


@case("sr: SEARCH matching twice returns error asking for more context")
def _():
    orig = "dup\nmid\ndup\n"
    body = "<<<<<<< SEARCH\ndup\n=======\nX\n>>>>>>> REPLACE"
    out, err = apply_search_replace(body, orig)
    assert out is None and err and "more than once" in err, f"got {out!r}, {err!r}"


@case("sr: stray text outside blocks rejected")
def _():
    body = ("Here is my edit:\n"
            "<<<<<<< SEARCH\nline5\n=======\nCHANGED5\n>>>>>>> REPLACE")
    out, err = apply_search_replace(body, ORIG10)
    assert out is None and err and "outside" in err, f"got {out!r}, {err!r}"


@case("sr: missing markers (no blocks) rejected")
def _():
    out, err = apply_search_replace("just some file contents\nno markers", ORIG10)
    assert out is None and err and "No valid" in err, f"got {out!r}, {err!r}"


@case("sr: malformed block (no ======= divider) rejected")
def _():
    body = "<<<<<<< SEARCH\nline5\nCHANGED5\n>>>>>>> REPLACE"
    out, err = apply_search_replace(body, ORIG10)
    assert out is None and err is not None, f"got {out!r}, {err!r}"


@case("sr: whitespace between blocks tolerated")
def _():
    body = ("<<<<<<< SEARCH\nline2\n=======\nTWO\n>>>>>>> REPLACE\n\n\n"
            "<<<<<<< SEARCH\nline9\n=======\nNINE\n>>>>>>> REPLACE\n")
    out, err = apply_search_replace(body, ORIG10)
    assert err is None, f"err {err!r}"
    assert out == ORIG10.replace("line2", "TWO").replace("line9", "NINE"), f"got {out!r}"


@case("sr: empty replacement deletes the searched text")
def _():
    orig = "keep1\ngone\nkeep2"
    body = "<<<<<<< SEARCH\ngone\n=======\n>>>>>>> REPLACE"
    out, err = apply_search_replace(body, orig)
    assert err is None, f"err {err!r}"
    assert out == "keep1\n\nkeep2", f"got {out!r}"


@case("sr: SR_BLOCK_RE captures search and replace groups")
def _():
    m = SR_BLOCK_RE.search("<<<<<<< SEARCH\na\nb\n=======\nc\n>>>>>>> REPLACE")
    assert m and m.group(1) == "a\nb" and m.group(2) == "c", f"got {m and m.groups()!r}"


# ---------------- NO_CHANGE parsing ----------------

@case("no_change: bare NO_CHANGE")
def _():
    assert is_no_change("NO_CHANGE") is True


@case("no_change: bare NO_CHANGE with surrounding whitespace")
def _():
    assert is_no_change("  \nNO_CHANGE\n\n") is True


@case("no_change: NO_CHANGE with justification block")
def _():
    text = ("NO_CHANGE\n===JUSTIFICATION===\nThe if is inside \\SV_plus and "
            "SandPiper has no equivalent.\n===END===")
    assert is_no_change(text) is True


@case("no_change: analysis preamble before NO_CHANGE line")
def _():
    text = ("Reviewing wip.tlv: the design already uses $signal pipesignals\n"
            "throughout and no always blocks remain.\n\nNO_CHANGE")
    assert is_no_change(text) is True


@case("no_change: NO_CHANGE line with trailing spaces still counts")
def _():
    assert is_no_change("analysis first\nNO_CHANGE   \n") is True


@case("no_change: reply containing ===FILE must NOT count")
def _():
    text = "NO_CHANGE\n===FILE: wip.tlv===\nm4_TLV_version 1d\n===END==="
    assert is_no_change(text) is False


@case("no_change: reply containing a SEARCH block must NOT count")
def _():
    text = "NO_CHANGE\n<<<<<<< SEARCH\na\n=======\nb\n>>>>>>> REPLACE"
    assert is_no_change(text) is False


@case("no_change: prose mentioning NO_CHANGE mid-sentence must NOT count")
def _():
    assert is_no_change("I considered replying NO_CHANGE but edits are needed.") is False


@case("no_change: NO_CHANGE with trailing words on the line must NOT count")
def _():
    assert is_no_change("NO_CHANGE is the right call here") is False


@case("no_change: NO_CHANGE. with punctuation must NOT count")
def _():
    assert is_no_change("NO_CHANGE.") is False


# ---------------- justification extraction ----------------

@case("justify: extracts multi-line block, stripped")
def _():
    text = ("some reply\n===JUSTIFICATION===\n  The $mem array cannot be a\n"
            "pipesignal: SandPiper limitation.  \n===END===\ntrailer")
    got = extract_justification(text)
    assert got == "The $mem array cannot be a\npipesignal: SandPiper limitation.", f"got {got!r}"


@case("justify: returns None when no block present")
def _():
    assert extract_justification("NO_CHANGE") is None


@case("justify: block after a FILE block extracts only the justification")
def _():
    text = ("===FILE: wip.tlv===\ncontents here\n===END===\n"
            "===JUSTIFICATION===\nthe reason\n===END===")
    got = extract_justification(text)
    assert got == "the reason", f"got {got!r}"


@case("justify: capped at 1500 chars")
def _():
    text = "===JUSTIFICATION===\n" + "x" * 3000 + "\n===END==="
    got = extract_justification(text)
    assert got == "x" * 1500, f"got len {got and len(got)}"


@case("justify: JUSTIFY_RE is DOTALL and non-greedy to first ===END===")
def _():
    text = "===JUSTIFICATION===\nline a\nline b\n===END===\nmore\n===END==="
    m = JUSTIFY_RE.search(text)
    assert m and m.group(1) == "line a\nline b", f"got {m and m.group(1)!r}"


def main():
    passed = 0
    failures = []
    for name, fn in CASES:
        try:
            fn()
            passed += 1
        except AssertionError as e:
            failures.append(f"FAIL  {name}: {e}")
        except Exception as e:
            failures.append(f"ERROR {name}: {type(e).__name__}: {e}")
    for line in failures:
        print(line)
    print(f"{passed}/{len(CASES)} cases passed")
    sys.exit(0 if not failures else 1)


if __name__ == "__main__":
    main()
