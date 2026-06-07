#!/usr/bin/env python3
"""Inline the `Bytes` predicate at every call site.

Rewrite rules (applied in Gobra annotation context only):

  sl.Bytes(s, a, b)                  -> (0 <= a && a <= b && b <= cap(s) &&
                                          forall i int :: { &s[i] } a <= i && i < b
                                          ==> acc(&s[i]))
  acc(sl.Bytes(s, a, b), p)          -> same body, with the fraction p propagated
                                          into the inner acc(&s[i], p)
  fold sl.Bytes(...)                 -> entire physical line deleted
  unfold sl.Bytes(...)               -> entire physical line deleted
  unfolding sl.Bytes(...) in e       -> e
  unfolding acc(sl.Bytes(...), p) in -> e

The same rules apply to `slices.Bytes(...)` (unaliased import) and, with
--specs-only, to bare `Bytes(...)` in slices.gobra spec lines.

In .go files, only text inside Gobra annotations is rewritten:
  - line comments starting with //@ or // @
  - block comments delimited by /*@ ... @*/
Plain comments and string literals are left untouched.

In .gobra files, all source outside string literals is rewritten (except
that --specs-only skips function bodies).
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


# ----- low-level scanning helpers ----------------------------------------- #

def find_matching(text: str, open_pos: int) -> int:
    """Return index of the close paren matching text[open_pos] == '('.

    Skips nested parens, string literals, line comments, and block comments.
    """
    assert text[open_pos] == '('
    depth = 0
    i = open_pos
    n = len(text)
    while i < n:
        c = text[i]
        # Skip strings
        if c == '"' or c == "'":
            i = _skip_string(text, i)
            continue
        if c == '`':
            j = text.find('`', i + 1)
            i = (j + 1) if j != -1 else n
            continue
        # Skip comments. Note: do not treat // or /* in args as code.
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            j = text.find('\n', i)
            i = j if j != -1 else n
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            j = text.find('*/', i + 2)
            i = (j + 2) if j != -1 else n
            continue
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError(f"unmatched paren at offset {open_pos}")


def _skip_string(text: str, i: int) -> int:
    quote = text[i]
    i += 1
    n = len(text)
    while i < n:
        c = text[i]
        if c == '\\':
            i += 2
            continue
        if c == quote:
            return i + 1
        if c == '\n':  # not a real Go string, give up
            return i
        i += 1
    return n


def split_top_level_commas(text: str) -> list[str]:
    """Split a comma-separated expression list at the top level."""
    parts: list[str] = []
    depth = 0
    start = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == '"' or c == "'":
            i = _skip_string(text, i)
            continue
        if c == '`':
            j = text.find('`', i + 1)
            i = (j + 1) if j != -1 else n
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif c == ',' and depth == 0:
            parts.append(text[start:i].strip())
            start = i + 1
        i += 1
    parts.append(text[start:].strip())
    return parts


def is_id_char(c: str) -> bool:
    return c.isalnum() or c == '_'


def expr_is_atomic(expr: str) -> bool:
    """True if expr is a single identifier (possibly dotted), no operators."""
    s = expr.strip()
    if not s:
        return False
    for ch in s:
        if ch.isalnum() or ch in '_.':
            continue
        return False
    return True


def expr_is_wrapped(expr: str) -> bool:
    """True if expr is entirely wrapped in matching parens."""
    s = expr.strip()
    if len(s) < 2 or s[0] != '(' or s[-1] != ')':
        return False
    try:
        return find_matching(s, 0) == len(s) - 1
    except ValueError:
        return False


# ----- annotation extraction (for .go files) ------------------------------- #

@dataclass
class Region:
    start: int  # inclusive
    end: int    # exclusive


def annotation_regions(text: str) -> list[Region]:
    """Return rewriteable regions of a .go file (inside Gobra annotations)."""
    regions: list[Region] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == '"' or c == "'":
            i = _skip_string(text, i)
            continue
        if c == '`':
            j = text.find('`', i + 1)
            i = (j + 1) if j != -1 else n
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            j = text.find('\n', i)
            line_end = j if j != -1 else n
            body = text[i + 2:line_end]
            stripped = body.lstrip()
            if stripped.startswith('@'):
                ann_start = (i + 2) + (len(body) - len(stripped)) + 1  # after '@'
                regions.append(Region(ann_start, line_end))
            i = line_end
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            j = text.find('*/', i + 2)
            block_end = j if j != -1 else n
            # Gobra block annotation starts with /*@ and ends with @*/
            if text[i + 2:i + 3] == '@':
                ann_start = i + 3
                ann_end = block_end - 1 if (j != -1 and text[block_end - 1] == '@') else block_end
                regions.append(Region(ann_start, ann_end))
            i = block_end + 2 if j != -1 else n
            continue
        i += 1
    return regions


def gobra_regions(text: str, specs_only: bool) -> list[Region]:
    """Return rewriteable regions of a .gobra file.

    Excludes string literals and (when specs_only) function bodies.
    """
    regions: list[Region] = []
    cur_start = 0
    i = 0
    n = len(text)

    def flush(end: int):
        if end > cur_start:
            regions.append(Region(cur_start, end))

    while i < n:
        c = text[i]
        if c == '"' or c == "'":
            flush(i)
            i = _skip_string(text, i)
            cur_start = i
            continue
        if c == '`':
            flush(i)
            j = text.find('`', i + 1)
            i = (j + 1) if j != -1 else n
            cur_start = i
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            flush(i)
            j = text.find('\n', i)
            i = j if j != -1 else n
            cur_start = i
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            flush(i)
            j = text.find('*/', i + 2)
            i = (j + 2) if j != -1 else n
            cur_start = i
            continue
        if specs_only and c == '{' and _is_top_level_func_brace(text, i):
            flush(i)
            close = _find_matching_brace(text, i)
            i = close + 1 if close != -1 else n
            cur_start = i
            continue
        i += 1
    flush(n)
    return regions


def _find_matching_brace(text: str, open_pos: int) -> int:
    """Find matching '}' for text[open_pos] == '{', ignoring comments/strings."""
    assert text[open_pos] == '{'
    depth = 0
    i = open_pos
    n = len(text)
    while i < n:
        c = text[i]
        if c == '"' or c == "'":
            i = _skip_string(text, i)
            continue
        if c == '`':
            j = text.find('`', i + 1)
            i = (j + 1) if j != -1 else n
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            j = text.find('\n', i)
            i = j if j != -1 else n
            continue
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            j = text.find('*/', i + 2)
            i = (j + 2) if j != -1 else n
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def _is_top_level_func_brace(text: str, brace_pos: int) -> bool:
    """Heuristic: is `text[brace_pos] == '{'` the opening brace of a func body?

    Scans backwards from brace_pos through whitespace and a ')' (the func
    parameter list / return type). If we ultimately find `func` on a line
    that starts a declaration, return True.

    This is intentionally conservative: only `func` (optionally preceded by
    `pure`, `ghost`, identifiers, return-type tokens) bodies are skipped.
    The `pred BodyName { ... }` form is *not* skipped — predicate bodies
    are spec context and should be rewritten if any Bytes appears (none do
    in slices.gobra except the Bytes definition itself, which contains no
    `Bytes(` call).
    """
    j = brace_pos - 1
    while j >= 0 and text[j] in ' \t':
        j -= 1
    # Walk back over (possibly) `) Type`, return types, parens, identifiers.
    paren_depth = 0
    saw_close_paren = False
    while j >= 0:
        c = text[j]
        if c == ')':
            paren_depth += 1
            saw_close_paren = True
            j -= 1
            continue
        if c == '(':
            paren_depth -= 1
            if paren_depth < 0:
                return False
            j -= 1
            continue
        if paren_depth > 0:
            j -= 1
            continue
        # Outside any parens.
        if c.isalnum() or c in '_ \t\n[],.*':
            # Look for 'func' keyword as a token boundary.
            if c == 'c' and text[max(0, j - 3):j + 1] == 'func' and (
                    j - 4 < 0 or not is_id_char(text[j - 4])):
                return saw_close_paren  # func with a signature => has body
            j -= 1
            continue
        # Hit some other punctuation/operator: not a func decl.
        return False
    return False


def in_any_region(pos: int, regions: list[Region]) -> bool:
    for r in regions:
        if r.start <= pos < r.end:
            return True
    return False


# ----- core rewrite engine ------------------------------------------------- #

PREDICATE_NAMES = ('sl.Bytes', 'slices.Bytes')


@dataclass
class Match:
    """A single Bytes(...) invocation we plan to rewrite."""
    pred_start: int        # index of first char of e.g. 'sl.Bytes' or 'Bytes'
    paren_open: int        # index of '('
    paren_close: int       # index of matching ')'
    args: list[str]        # [s, start, end]
    enclosing_acc: tuple[int, int, str] | None = None
    # (acc_start_offset_in_text, acc_close_offset_in_text, fraction_string)
    enclosing_unfolding: tuple[int, int] | None = None
    # (unfolding_keyword_start, end_of_' in ' delimiter)
    statement_kind: str | None = None
    # 'fold' or 'unfold' if the entire physical line is a fold/unfold of this
    line_start: int = 0
    line_end: int = 0


def find_bytes_matches(text: str, regions: list[Region], allow_bare: bool) -> list[Match]:
    matches: list[Match] = []
    for r in regions:
        i = r.start
        end = r.end
        while i < end:
            c = text[i]
            if c == 'B' and text[i:i + 6] == 'Bytes(':
                # Check identifier boundary: previous char must not be id-char
                # AND must follow either 'sl.', 'slices.', or be bare (allow_bare).
                if i > 0 and is_id_char(text[i - 1]):
                    i += 1
                    continue
                prefix_start = i
                # Look back for 'sl.' or 'slices.'
                if i >= 3 and text[i - 3:i] == 'sl.' and (i - 4 < 0 or not is_id_char(text[i - 4])):
                    prefix_start = i - 3
                elif i >= 7 and text[i - 7:i] == 'slices.' and (i - 8 < 0 or not is_id_char(text[i - 8])):
                    prefix_start = i - 7
                else:
                    if not allow_bare:
                        i += 1
                        continue
                    # Bare `Bytes(` is allowed only in slices.gobra. But skip
                    # `pred Bytes(...)` (the predicate's own declaration) and
                    # any other declaration context (`func Bytes(...)`).
                    k = i - 1
                    while k >= 0 and text[k] in ' \t\n':
                        k -= 1
                    # k now points to last char of preceding token (or -1).
                    # Check if it's the end of a keyword like 'pred' or 'func'.
                    if k >= 3 and text[k - 3:k + 1] == 'pred' and (k - 4 < 0 or not is_id_char(text[k - 4])):
                        i += 1
                        continue
                    if k >= 3 and text[k - 3:k + 1] == 'func' and (k - 4 < 0 or not is_id_char(text[k - 4])):
                        i += 1
                        continue
                # paren_open is at i+5 (the '(' after 'Bytes')
                paren_open = i + 5
                try:
                    paren_close = find_matching(text, paren_open)
                except ValueError:
                    i += 1
                    continue
                args_text = text[paren_open + 1:paren_close]
                args = split_top_level_commas(args_text)
                if len(args) != 3:
                    i = paren_close + 1
                    continue
                m = Match(
                    pred_start=prefix_start,
                    paren_open=paren_open,
                    paren_close=paren_close,
                    args=args,
                )
                _classify_context(text, m, region_end=end)
                matches.append(m)
                # Skip past the close paren (and any enclosing acc/unfolding)
                skip_to = paren_close + 1
                if m.enclosing_acc is not None:
                    skip_to = max(skip_to, m.enclosing_acc[1] + 1)
                if m.enclosing_unfolding is not None:
                    skip_to = max(skip_to, m.enclosing_unfolding[1])
                if m.statement_kind is not None:
                    skip_to = max(skip_to, m.line_end)
                i = skip_to
                continue
            if c == '"' or c == "'":
                i = _skip_string(text, i)
                continue
            if c == '`':
                j = text.find('`', i + 1)
                i = (j + 1) if j != -1 else end
                continue
            i += 1
    return matches


def _classify_context(text: str, m: Match, region_end: int) -> None:
    """Fill in enclosing_acc / enclosing_unfolding / statement_kind on m."""
    # 1) Look left for `acc(` immediately wrapping this predicate.
    j = m.pred_start - 1
    while j >= 0 and text[j] in ' \t\n':
        j -= 1
    # We want text[j-3:j+1] == 'acc(' but with the `(` right before pred_start
    # (modulo whitespace).
    # Actually: the predicate is the *first* arg of acc(). So the chars right
    # before pred_start (skipping ws) should be '('.
    if j >= 0 and text[j] == '(':
        # Is this paren preceded by 'acc'?
        k = j - 1
        while k >= 0 and text[k] in ' \t\n':
            k -= 1
        if k >= 2 and text[k - 2:k + 1] == 'acc' and (k - 3 < 0 or not is_id_char(text[k - 3])):
            acc_start = k - 2
            acc_open = j
            # Find matching close of acc(...)
            try:
                acc_close = find_matching(text, acc_open)
            except ValueError:
                acc_close = None
            if acc_close is not None and acc_close > m.paren_close:
                # Extract args of acc(...)
                acc_args = split_top_level_commas(text[acc_open + 1:acc_close])
                if len(acc_args) == 2:
                    # First arg is the predicate; second is the fraction.
                    m.enclosing_acc = (acc_start, acc_close, acc_args[1].strip())

    # 2) Look left for `unfolding` (possibly with acc-wrapped predicate).
    span_start = m.enclosing_acc[0] if m.enclosing_acc else m.pred_start
    span_end = m.enclosing_acc[1] if m.enclosing_acc else m.paren_close
    k = span_start - 1
    while k >= 0 and text[k] in ' \t\n':
        k -= 1
    if k >= 8 and text[k - 8:k + 1] == 'unfolding' and (k - 9 < 0 or not is_id_char(text[k - 9])):
        # Find ` in ` after span_end at the same paren depth (0).
        in_pos = _find_in_keyword(text, span_end + 1, region_end)
        if in_pos != -1:
            # in_pos points to 'i' of 'in'; the token is 2 chars.
            m.enclosing_unfolding = (k - 8, in_pos + 2)

    # 3) Detect statement-level fold/unfold.
    # Find start of physical line.
    line_start = text.rfind('\n', 0, m.pred_start) + 1  # 0 if no newline
    # Walk forward through leading whitespace and any annotation prefix.
    p = line_start
    # In .go files, the line may be like `\t// @ \tfold sl.Bytes(...)`.
    # Skip leading whitespace, then optional `//`/`/*` and `@`, then ws.
    while p < m.pred_start and text[p] in ' \t':
        p += 1
    if text[p:p + 2] == '//':
        p += 2
        while p < m.pred_start and text[p] in ' \t':
            p += 1
        if text[p:p + 1] == '@':
            p += 1
        while p < m.pred_start and text[p] in ' \t':
            p += 1
    elif text[p:p + 2] == '/*':
        p += 2
        if text[p:p + 1] == '@':
            p += 1
        while p < m.pred_start and text[p] in ' \t\n':
            p += 1
    # Now look for fold/unfold keyword, optionally preceded by `ghost` / `defer`.
    keyword = None
    q = p
    # Skip optional `ghost ` prefix.
    if text[q:q + 5] == 'ghost' and q + 5 < len(text) and text[q + 5] in ' \t':
        q += 5
        while q < m.pred_start and text[q] in ' \t':
            q += 1
    # Skip optional `defer ` prefix.
    if text[q:q + 5] == 'defer' and q + 5 < len(text) and text[q + 5] in ' \t':
        q += 5
        while q < m.pred_start and text[q] in ' \t':
            q += 1
    if text[q:q + 7] == 'unfold ' or text[q:q + 7] == 'unfold\t':
        keyword = 'unfold'
        kw_end = q + 6
    elif text[q:q + 5] == 'fold ' or text[q:q + 5] == 'fold\t':
        keyword = 'fold'
        kw_end = q + 4
    if keyword is not None:
        # Skip ws between keyword and predicate/acc.
        r = kw_end
        while r < m.pred_start and text[r] in ' \t':
            r += 1
        if r == span_start:
            # The keyword is immediately followed by the predicate (or acc).
            # Find end of physical line.
            nl = text.find('\n', span_end)
            line_end = (nl + 1) if nl != -1 else len(text)
            # If this line is inside a /*@ ... @*/ block, the line ending logic
            # is the same — we still strip the whole line.
            m.statement_kind = keyword
            m.line_start = line_start
            m.line_end = line_end


def _find_in_keyword(text: str, start: int, region_end: int) -> int:
    """Find the position of ` in ` (or ` in\\n` / ` in\\t`) starting from `start`.

    Returns the index of the 'i' in 'in', or -1 if not found before region_end.
    Only considers top-level (paren-depth 0) occurrences.
    """
    depth = 0
    i = start
    n = min(len(text), region_end)
    while i < n:
        c = text[i]
        if c == '"' or c == "'":
            i = _skip_string(text, i)
            continue
        if c == '`':
            j = text.find('`', i + 1)
            i = (j + 1) if j != -1 else n
            continue
        if c == '(' or c == '[' or c == '{':
            depth += 1
        elif c == ')' or c == ']' or c == '}':
            depth -= 1
            if depth < 0:
                return -1
        elif depth == 0:
            # Look for token 'in' surrounded by separators.
            if c == 'i' and text[i:i + 2] == 'in':
                prev_ok = (i == 0) or (not is_id_char(text[i - 1]))
                next_ok = (i + 2 >= n) or (not is_id_char(text[i + 2]))
                if prev_ok and next_ok:
                    return i
        i += 1
    return -1


# ----- replacement building ------------------------------------------------ #

def render_body(s_expr: str, start_expr: str, end_expr: str, perm: str | None) -> str:
    """Return the inlined body string, wrapped in parens.

    Special-cases:
      - if s is non-atomic, wrap as (s)
      - if perm is None, emit acc(&s[i]); else acc(&s[i], perm)
    """
    s = s_expr.strip()
    se = start_expr.strip()
    ee = end_expr.strip()
    if expr_is_atomic(s) or expr_is_wrapped(s):
        s_in_brackets = f'&{s}[i]'
        s_in_cap = f'cap({s})'
    else:
        s_in_brackets = f'&({s})[i]'
        s_in_cap = f'cap({s})'
    if perm is None:
        inner_acc = f'acc({s_in_brackets})'
    else:
        inner_acc = f'acc({s_in_brackets}, {perm.strip()})'
    return (f'(0 <= {se} && {se} <= {ee} && {ee} <= {s_in_cap} && '
            f'forall i int :: {{ {s_in_brackets} }} '
            f'{se} <= i && i < {ee} ==> {inner_acc})')


@dataclass
class Edit:
    start: int
    end: int
    text: str


def build_edits(text: str, matches: list[Match]) -> list[Edit]:
    edits: list[Edit] = []
    seen_lines: set[int] = set()
    # Sort by position so we can dedupe overlapping statement-line deletions.
    for m in sorted(matches, key=lambda x: x.pred_start):
        if m.statement_kind is not None:
            if m.line_start in seen_lines:
                continue
            seen_lines.add(m.line_start)
            edits.append(Edit(m.line_start, m.line_end, ''))
            continue
        if m.enclosing_unfolding is not None:
            # Replace [unfolding ... in ] with ''.
            # Also consume trailing whitespace, including a newline plus the
            # following line's leading indentation, so a multi-line form like
            #   return unfolding sl.Bytes(...) in
            #       expr
            # collapses to `return expr` (otherwise Gobra parses the `return`
            # as a bare statement before the expression).
            uf_start, in_end = m.enclosing_unfolding
            consume_end = in_end
            while consume_end < len(text) and text[consume_end] in ' \t':
                consume_end += 1
            if consume_end < len(text) and text[consume_end] == '\n':
                consume_end += 1
                while consume_end < len(text) and text[consume_end] in ' \t':
                    consume_end += 1
                # If the next line is a Gobra annotation prefix (`//@` / `// @`
                # in a .go file, or just indentation in a .gobra file), keep it.
                if text[consume_end:consume_end + 3] in ('//@', '/*@'):
                    pass  # leave annotation prefix
                elif text[consume_end:consume_end + 2] == '//':
                    # Plain comment; preserve.
                    pass
            edits.append(Edit(uf_start, consume_end, ''))
            continue
        if m.enclosing_acc is not None:
            acc_start, acc_close, frac = m.enclosing_acc
            new = render_body(m.args[0], m.args[1], m.args[2], frac)
            edits.append(Edit(acc_start, acc_close + 1, new))
            continue
        new = render_body(m.args[0], m.args[1], m.args[2], None)
        edits.append(Edit(m.pred_start, m.paren_close + 1, new))
    return edits


def apply_edits(text: str, edits: list[Edit]) -> str:
    # Apply right-to-left.
    parts = []
    last = len(text)
    for e in sorted(edits, key=lambda e: e.start, reverse=True):
        parts.append(text[e.end:last])
        parts.append(e.text)
        last = e.start
    parts.append(text[:last])
    return ''.join(reversed(parts))


# ----- top-level driver ---------------------------------------------------- #

def rewrite_text(text: str, file_kind: str, specs_only: bool = False,
                 allow_bare: bool = False) -> str:
    if file_kind == 'go':
        regions = annotation_regions(text)
    elif file_kind == 'gobra':
        regions = gobra_regions(text, specs_only=specs_only)
    else:
        raise ValueError(f'unknown file_kind: {file_kind}')
    matches = find_bytes_matches(text, regions, allow_bare=allow_bare)
    edits = build_edits(text, matches)
    return apply_edits(text, edits)


def file_kind_for(path: Path) -> str | None:
    if path.suffix == '.gobra':
        return 'gobra'
    if path.suffix == '.go':
        try:
            with open(path, 'rb') as f:
                head = f.read(8192).decode('utf-8', errors='replace')
        except OSError:
            return None
        # Look for a `// +gobra` build-tag-style marker on its own line.
        for line in head.splitlines():
            if line.strip() == '// +gobra':
                return 'go'
        return None
    return None


def process_file(path: Path, specs_only: bool, allow_bare: bool, dry_run: bool) -> int:
    kind = file_kind_for(path)
    if kind is None:
        return 0
    original = path.read_text(encoding='utf-8')
    rewritten = rewrite_text(original, file_kind=kind, specs_only=specs_only,
                             allow_bare=allow_bare)
    if rewritten == original:
        return 0
    if dry_run:
        return 1
    path.write_text(rewritten, encoding='utf-8')
    return 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('paths', nargs='+')
    ap.add_argument('--specs-only', action='store_true',
                    help='inside .gobra files, skip function bodies')
    ap.add_argument('--allow-bare', action='store_true',
                    help='also match bare `Bytes(` (use only in slices.gobra)')
    ap.add_argument('--dry-run', action='store_true')
    args = ap.parse_args(argv)
    changed = 0
    for p in args.paths:
        path = Path(p)
        if path.is_dir():
            for sub in sorted(path.rglob('*')):
                if sub.is_file():
                    changed += process_file(sub, args.specs_only,
                                            args.allow_bare, args.dry_run)
        else:
            changed += process_file(path, args.specs_only,
                                    args.allow_bare, args.dry_run)
    print(f'changed {changed} file(s)', file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
