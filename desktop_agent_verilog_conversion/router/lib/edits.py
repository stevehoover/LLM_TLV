"""Edit-format parsing and applying: the "..." omission format, aider-style
search/replace blocks, NO_CHANGE detection, and justification extraction.

tests.py loads the pure parser functions in this file (is_no_change,
extract_justification, expand_omissions, apply_search_replace and their
regexes) directly by AST, so they must stay top-level and free of imports
beyond re/os.
"""

import os
import re

from . import config

JUSTIFY_RE = re.compile(r"===JUSTIFICATION===\n(.*?)\n?===END===", re.S)


def extract_justification(text):
    m = JUSTIFY_RE.search(text)
    return m.group(1).strip()[:1500] if m else None


# NO_CHANGE may carry a justification block (as the system prompt teaches),
# and models often lead with a short analysis before the NO_CHANGE line.
# Accept NO_CHANGE standing on its own line anywhere in the reply, as long
# as the reply contains no file-edit blocks; anything stricter blocks the
# honest escape hatch (both failure modes were observed in real runs).
def is_no_change(text):
    t = text.strip()
    if t == "NO_CHANGE":
        return True
    if "===FILE" in t or "<<<<<<< SEARCH" in t:
        return False
    return bool(re.search(r"^NO_CHANGE\s*$", t, re.M))


def expand_omissions(new, orig):
    # The "..." mechanism (ported from the conversion-to-TLV repo): a "..."
    # line stands for an UNCHANGED region taken from the original file. Diff
    # line-by-line; every hunk containing "..." must map cleanly onto a block
    # of original lines. "..." mixed with edited lines in one hunk is
    # ambiguous: return None so the caller requests the full file instead of
    # guessing.
    import difflib
    nl, ol = new.split("\n"), orig.split("\n")
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, nl, ol, autojunk=False).get_opcodes():
        chunk = nl[i1:i2]
        if tag == "equal":
            out.extend(chunk)
            continue
        dots = [l for l in chunk if l.strip() == "..."]
        if not dots:
            out.extend(chunk)
        elif len(dots) == len(chunk):
            out.extend(ol[j1:j2])
        else:
            return None
    return "\n".join(out)


SR_BLOCK_RE = re.compile(r"<<<<<<< SEARCH\n(.*?)\n=======\n?(.*?)\n?>>>>>>> REPLACE", re.S)


def apply_search_replace(body, orig):
    # Aider-style search/replace: every SEARCH block must match the original
    # exactly ONCE (same whitespace). Returns (new_text, err); a non-None err
    # goes back to the model as feedback.
    pos = 0
    out = orig
    blocks = list(SR_BLOCK_RE.finditer(body))
    if not blocks:
        return None, "No valid <<<<<<< SEARCH/=======/>>>>>>> REPLACE blocks found."
    leftover = SR_BLOCK_RE.sub("", body).strip()
    if leftover:
        return None, ("Content found outside search/replace blocks. For an existing file, "
                      "provide ONLY search/replace blocks, or the complete file with none.")
    for m in blocks:
        search, replace = m.group(1), m.group(2)
        n = out.count(search)
        if n == 0:
            return None, ("SEARCH text not found in the current file (must match exactly, "
                          "including whitespace):\n" + search[:400])
        if n > 1:
            return None, ("SEARCH text matches the current file more than once; add more "
                          "surrounding context lines to make it unique:\n" + search[:400])
        out = out.replace(search, replace, 1)
    return out, None


APPLY_ERROR = ""


def apply_files(text):
    global APPLY_ERROR
    APPLY_ERROR = ""
    changed = []
    originals = {}
    for m in re.finditer(r"===FILE: (\S+)===\n(.*?)\n?===END===", text, re.S):
        name, body = m.group(1), m.group(2)
        if "/" in name or name.startswith(".") or name in config.HARNESS_FILES:
            continue
        p = os.path.join(config.MDIR, name)
        orig = open(p).read() if os.path.exists(p) else None
        if "<<<<<<< SEARCH" in body:
            if orig is None:
                APPLY_ERROR = (f"File {name} is new but uses search/replace blocks; "
                               "new files must be written out in full.")
                restore(originals)
                return [], {}
            body, err = apply_search_replace(body, orig)
            if body is None:
                APPLY_ERROR = f"Search/replace edit for {name} failed: {err}"
                restore(originals)
                return [], {}
        elif any(l.strip() == "..." for l in body.split("\n")):
            if orig is None:
                APPLY_ERROR = (f"File {name} is new but uses \"...\" omission lines; "
                               "new files must be written out in full.")
                restore(originals)
                return [], {}
            body = expand_omissions(body, orig)
            if body is None:
                APPLY_ERROR = (f"The \"...\" omission lines in {name} could not be mapped "
                               "unambiguously onto the original file (a \"...\" was mixed with "
                               "changed lines in the same region). Resend the COMPLETE file "
                               "contents without \"...\" lines.")
                restore(originals)
                return [], {}
        originals[name] = orig
        with open(p, "w") as f:
            f.write(body.rstrip() + "\n")
        changed.append(name)
    return changed, originals


def restore(originals):
    for name, body in originals.items():
        p = os.path.join(config.MDIR, name)
        if body is None:
            if os.path.exists(p):
                os.remove(p)
        else:
            with open(p, "w") as f:
                f.write(body)
