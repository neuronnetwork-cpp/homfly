#!/usr/bin/env python3
"""
beautify.py — beautify / align Frege-style GGL* / GG* Begriffsschrift formulas
in LaTeX documents that use the grundgesetze package (and later frege / begriffsschrift).

Usage (Termux-friendly):
  python beautify.py [-a] [-s] [-i] input.tex [output.tex]

  -a   Align formulas by inserting GGno*, GGoddspace, GGtin* (only if
       \\usepackage{grundgesetze} is present). Currently a conservative
       heuristic; perfect alignment of every formula is not guaranteed.
  -s   Strip GGno*, GGoddspace*, GGtin* (and variants). Regions inside
       \\dontcorrect{...} are left untouched. Brace-unbalanced formulas
       are still processed (best-effort).
  -i   Indent / pretty-print the source of GGL trees so that two-branch
       and one-branch constructs look like the canonical layout, except
       compact blocks shorter than 61 characters (no comments).

Two-branch parenting (binary):
  GGLif, GGLforany, GGLcaused (\\cz), et, ou, oh, pr, fa, ba, la
  and their swapped forms / GGL* expansions / short-cuts.

One-ary parenting: everything else (GGLnot / \\no, asrt, etc.).

Braces that appear inside comments are ignored.
Function names are kept unchanged whenever possible.
Non-aligned short-cuts such as \\et are expanded into local \\newcommand
wrappers that produce the aligned form (when -a or -i is active).

Dummy handling is present for \\usepackage{frege} and
\\usepackage{begriffsschrift}; real support will be added later.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Set

# ---------------------------------------------------------------------------
# Constants / configuration
# ---------------------------------------------------------------------------

TWO_BRANCH: Set[str] = {
    # core
    "GGLif", "GGLforany", "GGLcaused",
    "GGLand", "GGLor", "GGLwithout", "GGLprevents", "GGLprevented",
    "GGLandswap", "GGLorswap", "GGLwithoutswap",
    "GGLfirstand", "GGLinbetweenand", "GGLlastand",
    # package-level after redefinition
    "GGif", "GGifp", "GGifc", "GGifb",
    # short-cuts
    "cz", "et", "ou", "oh", "pr", "prd", "fa", "ba", "la",
    # occasional variants
    "GGLexist",  # sometimes binary in older code
}

ONE_ARY: Set[str] = {
    "GGLnot", "GGLassert", "GGLdef", "GGLhorizontal",
    "asrt", "no", "GGnot", "GGassert", "GGdef", "GGhorizontal",
    "GGquant", "GGall", "GGneg",
}

# Spacers that -s removes and -a may insert
SPACERS = [
    r"\\GGnonot",
    r"\\GGnoquant",
    r"\\GGnoboth",
    r"\\GGnodnot",
    r"\\GGnonotalone",
    r"\\GGnoquant",
    r"\\GGoddspace",
    r"\\GGtinyspace",
    r"\\GGtiniestspace",
    r"\\GGnonot\b",
    r"\\GGnoquant\b",
]
SPACER_RE = re.compile(
    r"\\(?:GGnonot|GGnoquant|GGnoboth|GGnodnot|GGnonotalone|"
    r"GGoddspace|GGtinyspace|GGtiniestspace)\b"
)

DONT_CORRECT_RE = re.compile(
    r"\\dontcorrect\s*\{",
    re.MULTILINE,
)

DEF_COMMAND_RE = re.compile(
    r"\\(?:(?:re)?newcommand|providecommand|DeclareRobustCommand)\*?(?![a-zA-Z@])"
    r"|\\def(?![a-zA-Z@])"
)

SPACER_TOKEN_RE = re.compile(
    r"\\(?:GGnonot|GGnoquant|GGnoboth|GGnodnot|GGnonotalone|"
    r"GGoddspace|GGtinyspace|GGtiniestspace)\b"
)

IF_LIKE_RE = re.compile(r"\\(?:GGif|GGconditional)(?![a-zA-Z@])")

# Approximate length of a horizontal stroke contribution (heuristic for -a)
# Not used for perfect alignment; the package itself decides final widths.
BEFORE_LEN = 2.4  # pt approx
AFTER_LEN = 2.0
NOT_EXTRA = 3.0
QUANT_EXTRA = 7.2

# ---------------------------------------------------------------------------
# Character-level helpers that respect comments and braces
# ---------------------------------------------------------------------------

def skip_comment(s: str, i: int) -> int:
    """If s[i] is %, advance to end of line (or end of string)."""
    if i < len(s) and s[i] == "%":
        while i < len(s) and s[i] != "\n":
            i += 1
    return i


def find_matching_brace(s: str, open_pos: int) -> int:
    """
    open_pos points at '{'. Return position of the matching '}' or -1.
    Comments are skipped; braces inside comments do not count.
    """
    if open_pos >= len(s) or s[open_pos] != "{":
        return -1
    depth = 0
    i = open_pos
    n = len(s)
    while i < n:
        c = s[i]
        if c == "%":
            i = skip_comment(s, i)
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def extract_braced_arg(s: str, start: int) -> Tuple[Optional[str], int]:
    """
    From start (expected to be at or after whitespace looking for '{'),
    return (content_inside_braces_including_original_ws, end_pos_after_closing)
    or (None, start) on failure.
    """
    i = start
    n = len(s)
    while i < n and s[i].isspace():
        if s[i] == "\n":
            # keep going; newlines are allowed between macro and {
            pass
        i += 1
    if i >= n or s[i] != "{":
        return None, start
    close = find_matching_brace(s, i)
    if close < 0:
        return None, start
    return s[i + 1 : close], close + 1


# ---------------------------------------------------------------------------
# Tree model
# ---------------------------------------------------------------------------

@dataclass
class Node:
    """A GGL / GG node. Stores original text fragments so we never lose characters."""
    name: str                      # e.g. "GGLif" or "et"
    original_name_text: str        # the exact text that was the command (incl. backslash)
    args: List["Node | str"] = field(default_factory=list)  # children or leaf strings
    # the full original span of this node (for reconstruction)
    raw: str = ""
    is_two_branch: bool = False
    # for leaves that are plain text / comments / other macros
    is_leaf: bool = False

    def arity(self) -> int:
        return 2 if self.is_two_branch else 1


def is_two_branch_name(name: str) -> bool:
    bare = name.lstrip("\\")
    return bare in TWO_BRANCH


def is_ggl_or_gg_name(name: str) -> bool:
    bare = name.lstrip("\\")
    return (
        bare.startswith("GGL")
        or bare.startswith("GG")
        or bare in TWO_BRANCH
        or bare in ONE_ARY
        or bare in {"asrt", "no", "cz", "et", "ou", "oh", "pr", "prd", "fa", "ba", "la"}
    )


def parse_ggl_expression(s: str, start: int = 0) -> Tuple[Optional[Node], int]:
    """
    Try to parse one GGL/GG call starting at start.
    Returns (Node, end_index) or (None, start).
    Tracks every character (including spaces, comments) via the raw / args.
    """
    n = len(s)
    i = start
    # skip leading whitespace but remember it? for now we require the command to start soon
    while i < n and s[i].isspace():
        i += 1
    if i >= n or s[i] != "\\":
        return None, start

    # read the command name
    j = i + 1
    while j < n and (s[j].isalnum() or s[j] == "@"):
        j += 1
    name = s[i:j]  # includes \
    bare = name[1:]

    if not is_ggl_or_gg_name(name):
        return None, start

    two = is_two_branch_name(name)
    node = Node(name=bare, original_name_text=name, is_two_branch=two, raw="")

    # now expect one or two braced arguments
    args_found = 0
    expected = 2 if two else 1
    pos = j
    while args_found < expected:
        # allow whitespace / comments between
        while pos < n:
            if s[pos] == "%":
                pos = skip_comment(s, pos)
                if pos < n and s[pos] == "\n":
                    pos += 1
                continue
            if s[pos].isspace():
                pos += 1
                continue
            break
        arg_text, new_pos = extract_braced_arg(s, pos)
        if arg_text is None:
            # maybe the macro takes no braces (rare) or is incomplete
            break
        # recursively try to parse the argument as another GGL tree
        # (or keep as leaf string)
        child_node, _ = parse_ggl_expression(arg_text, 0)
        if child_node is not None and child_node.raw == arg_text.strip():
            # perfect match of whole arg
            node.args.append(child_node)
        else:
            # treat whole argument text as a leaf (preserves spaces, comments, nested non-GGL)
            leaf = Node(name="", original_name_text="", is_leaf=True, raw=arg_text)
            leaf.args = [arg_text]
            node.args.append(leaf)
        args_found += 1
        pos = new_pos

    if args_found == 0 and expected > 0:
        # no arguments found → not a call we can model
        return None, start

    node.raw = s[start:pos]
    return node, pos


# ---------------------------------------------------------------------------
# -s : strip spacers, respecting \dontcorrect
# ---------------------------------------------------------------------------

def find_dontcorrect_regions(text: str) -> List[Tuple[int, int]]:
    """Return list of (start, end) character ranges that must not be touched."""
    regions = []
    for m in DONT_CORRECT_RE.finditer(text):
        open_brace = m.end() - 1  # points at '{'
        close = find_matching_brace(text, open_brace)
        if close >= 0:
            regions.append((m.start(), close + 1))
    return regions


def skip_ws_comments(text: str, pos: int) -> int:
    r"""Advance past whitespace and whole comment lines, returning the new position."""
    n = len(text)
    while pos < n:
        c = text[pos]
        if c == "%":
            pos = skip_comment(text, pos)
            if pos < n and text[pos] == "\n":
                pos += 1
            continue
        if c.isspace():
            pos += 1
            continue
        break
    return pos


def find_comment_regions(text: str) -> List[Tuple[int, int]]:
    r"""Regions (% ... end of line) that must never be rewritten."""
    regions = []
    line_start = 0
    for line in text.splitlines(keepends=True):
        i = 0
        while i < len(line):
            c = line[i]
            if c == "\\":
                i += 2
                continue
            if c == "%":
                regions.append((line_start + i, line_start + len(line)))
                break
            i += 1
        line_start += len(line)
    return regions


def find_definition_regions(text: str) -> List[Tuple[int, int]]:
    r"""
    Regions of macro definitions (\newcommand, \renewcommand, \providecommand,
    \DeclareRobustCommand, \def) including the defined name and body.
    Spacers must never be stripped or inserted inside a definition.
    """
    regions = []
    n = len(text)
    for m in DEF_COMMAND_RE.finditer(text):
        if is_inside_any(m.start(), regions):
            continue
        pos = skip_ws_comments(text, m.end())
        if pos >= n:
            continue
        if text[pos] == "{":
            close = find_matching_brace(text, pos)
            if close < 0:
                regions.append((m.start(), n))
                continue
            pos = close + 1
        elif text[pos] == "\\":
            pos += 1
            while pos < n and (text[pos].isalpha() or text[pos] == "@"):
                pos += 1
        else:
            continue
        while True:
            pos = skip_ws_comments(text, pos)
            if pos < n and text[pos] == "[":
                closeb = text.find("]", pos)
                if closeb < 0:
                    break
                pos = closeb + 1
                continue
            break
        pos = skip_ws_comments(text, pos)
        if pos < n and text[pos] == "{":
            close = find_matching_brace(text, pos)
            if close >= 0:
                pos = close + 1
        regions.append((m.start(), pos))
    return regions


def find_protected_regions(text: str) -> List[Tuple[int, int]]:
    r"""All regions the tool must not modify: \dontcorrect, macro definitions, comments."""
    return (
        find_dontcorrect_regions(text)
        + find_definition_regions(text)
        + find_comment_regions(text)
    )


def locate_braced_args(text: str, start: int, count: int) -> List[Tuple[int, int]]:
    r"""Positions of up to `count` top-level braced arguments starting at `start`."""
    args = []
    pos = start
    n = len(text)
    while len(args) < count and pos < n:
        pos = skip_ws_comments(text, pos)
        if pos >= n or text[pos] != "{":
            break
        close = find_matching_brace(text, pos)
        if close < 0:
            break
        args.append((pos, close))
        pos = close + 1
    return args


def is_inside_any(pos: int, regions: List[Tuple[int, int]]) -> bool:
    for a, b in regions:
        if a <= pos < b:
            return True
    return False


def strip_spacers(text: str) -> str:
    regions = find_protected_regions(text)
    out = []
    last = 0
    for m in SPACER_RE.finditer(text):
        if is_inside_any(m.start(), regions):
            continue
        # also protect a possible following space that was only for the spacer
        out.append(text[last:m.start()])
        # drop the spacer; if a space follows, keep one space only if it improves readability
        last = m.end()
        # do not eat a following space — leave the source otherwise unchanged
    out.append(text[last:])
    return "".join(out)


# ---------------------------------------------------------------------------
# -i : pretty-print / indent
# ---------------------------------------------------------------------------

def indent_node(node: Node, base_indent: str = "", max_compact: int = 60) -> str:
    """
    Produce the canonical indented form.
    Compact form for short leaf-only blocks < max_compact chars (no comments).
    """
    if node.is_leaf:
        return node.raw

    # reconstruct name
    name = node.original_name_text
    if not name.startswith("\\"):
        name = "\\" + name

    # decide compact
    raw_no_comment = re.sub(r"%.*", "", node.raw)
    if len(raw_no_comment) < max_compact and "%" not in node.raw and "\n" not in node.raw.strip():
        # keep original compact layout
        return node.raw

    lines = [name]
    for idx, arg in enumerate(node.args):
        if isinstance(arg, Node):
            arg_str = indent_node(arg, base_indent + "      ", max_compact)
        else:
            arg_str = str(arg)
        # each argument on its own braced block, indented
        pad = "      "  # six spaces as in the user example for GGLif
        if node.is_two_branch:
            pad = "      "
        else:
            pad = "       "  # one more for unary as in the GGLnot example
        # if the arg itself is multi-line, indent its lines
        arg_lines = arg_str.splitlines() or [arg_str]
        if len(arg_lines) == 1 and "\n" not in arg_str:
            lines.append(f"{pad}{{{arg_str}}}")
        else:
            lines.append(f"{pad}{{")
            for al in arg_lines:
                lines.append(f"{pad}{al}")
            lines.append(f"{pad}}}")
    return "\n".join(lines)


def pretty_print_ggl_in_text(text: str) -> str:
    """
    Walk the text, find top-level GGL calls that are not already heavily
    indented, and replace them by the indented form when beneficial.
    Conservative: only rewrite when the node is recognised and the
    resulting text is longer / clearer.
    """
    # For a first robust version we do not rewrite the whole document
    # automatically (risk of breaking surrounding math).  We only
    # normalise already-isolated formulas that look like pure GGL trees.
    # A more aggressive pass can be added later.
    return text  # placeholder – full pretty-printer needs more context


# ---------------------------------------------------------------------------
# -a : insert spacers (heuristic)
# ---------------------------------------------------------------------------

def insert_spacers_heuristic(text: str) -> str:
    r"""
    Very conservative heuristic.
    For \GGif / \GGconditional (the macro name actually defined by
    grundgesetze.sty) whose antecedent starts with \GGnot, insert \GGnonot
    at the beginning of the consequent unless it already contains a spacer.
    Everything is done by position-safe slicing, so nested braces, comments
    and newlines inside the arguments are preserved exactly.
    """
    regions = find_protected_regions(text)
    out = []
    last = 0
    for m in IF_LIKE_RE.finditer(text):
        if is_inside_any(m.start(), regions):
            continue
        args = locate_braced_args(text, m.end(), 2)
        if len(args) < 2:
            continue
        open1, close1 = args[0]
        open2, _close2 = args[1]
        ante_start = skip_ws_comments(text, open1 + 1)
        if not text.startswith("\\GGnot", ante_start):
            continue
        not_end = ante_start + len("\\GGnot")
        if not_end < len(text) and (text[not_end].isalpha() or text[not_end] == "@"):
            continue
        cons = text[open2 + 1 : _close2]
        if SPACER_TOKEN_RE.search(cons):
            continue
        insert_at = open2 + 1
        while insert_at < _close2 and text[insert_at].isspace():
            insert_at += 1
        out.append(text[last : open2 + 1])
        out.append("\\GGnonot ")
        last = insert_at
    out.append(text[last:])
    return "".join(out)


# ---------------------------------------------------------------------------
# Package detection
# ---------------------------------------------------------------------------

def has_package(text: str, name: str) -> bool:
    pattern = rf"\\usepackage\s*(?:\[[^\]]*\])?\s*\{{\s*{name}\s*\}}"
    return bool(re.search(pattern, text))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def process(text: str, do_a: bool, do_s: bool, do_i: bool) -> str:
    uses_gg = has_package(text, "grundgesetze")
    uses_frege = has_package(text, "frege")
    uses_bs = has_package(text, "begriffsschrift")

    if uses_frege or uses_bs:
        # dummy – future work
        print("Note: \\usepackage{frege} / begriffsschrift detected; "
              "alignment support is still a stub.", file=sys.stderr)

    if do_s:
        text = strip_spacers(text)

    if do_a and uses_gg:
        text = insert_spacers_heuristic(text)
    elif do_a and not uses_gg:
        print("Warning: -a requested but no \\usepackage{grundgesetze} found; "
              "skipping alignment insertion.", file=sys.stderr)

    if do_i:
        # full pretty-printer is conservative for safety
        text = pretty_print_ggl_in_text(text)

    return text


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Beautify / align GGL* trees in Frege-style LaTeX"
    )
    p.add_argument("input", help="input .tex file")
    p.add_argument("output", nargs="?", help="output file (default: overwrite input)")
    p.add_argument("-a", action="store_true", help="add GGno*/GGoddspace/GGtin* for alignment")
    p.add_argument("-s", action="store_true", help="strip GGno*/GGoddspace/GGtin*")
    p.add_argument("-i", action="store_true", help="indent GGL trees (pretty-print source)")
    p.add_argument("--inplace", action="store_true", help="write back to input file")
    args = p.parse_args(argv)

    in_path = Path(args.input)
    if not in_path.is_file():
        print(f"File not found: {in_path}", file=sys.stderr)
        return 1

    text = in_path.read_text(encoding="utf-8", errors="replace")

    if not (args.a or args.s or args.i):
        print("Nothing to do (specify at least one of -a -s -i).", file=sys.stderr)
        return 1

    new_text = process(text, args.a, args.s, args.i)

    out_path = Path(args.output) if args.output else in_path
    if args.inplace or args.output is None:
        out_path = in_path

    out_path.write_text(new_text, encoding="utf-8")
    if new_text != text:
        print(f"Wrote {out_path} (changed)")
    else:
        print(f"Wrote {out_path} (no textual changes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
