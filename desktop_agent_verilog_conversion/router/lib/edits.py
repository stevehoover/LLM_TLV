"""Edit-format parsing and applying: the "..." omission format, NO_CHANGE
detection, and justification extraction.

tests.py loads the pure parser functions in this file (is_no_change,
extract_justification, expand_omissions and their regexes) directly by AST,
so they must stay top-level and free of imports beyond re/os.
"""

import os
import re

from . import config

JUSTIFY_RE = re.compile(r"===JUSTIFICATION===\n(.*?)\n?===END===", re.S)

# An omission marker is any line beginning with "..." (the original
# conversion-to-TLV script's rule, so annotated markers like
# "... (unchanged)" also count).
DOTS_RE = re.compile(r"\s*\.\.\.")


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
    if "===FILE" in t:
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
    nl, ol = new.rstrip().split("\n"), orig.split("\n")
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, nl, ol, autojunk=False).get_opcodes():
        chunk = nl[i1:i2]
        if tag == "equal":
            out.extend(chunk)
            continue
        dots = [l for l in chunk if DOTS_RE.match(l)]
        if not dots:
            out.extend(chunk)
        elif len(dots) == len(chunk):
            out.extend(ol[j1:j2])
        else:
            return None
    return "\n".join(out)


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
        if any(DOTS_RE.match(l) for l in body.split("\n")):
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
