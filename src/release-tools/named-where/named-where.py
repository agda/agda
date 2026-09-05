#!/usr/bin/env python3

"""Find and classify named `where` modules in Agda code bases.

A *named* `where` module is the `module M where` form of a `where` clause:

    f x = rhs
      module M where
      g = ...

as opposed to an ordinary module declaration `module M where`, which starts a
new declaration in the enclosing block.  The two are told apart by layout: a
named `where` module belongs to the preceding clause and is therefore indented
*deeper* than the layout column of the enclosing declaration block.

Agda also counts `module _ where` in this position as a named `where` module
(it is a `SomeWhere` clause in `Agda.Syntax.Concrete`), so it is reported here
too, with a separate sub-count.

The tool works purely lexically (comments, string/char literals, literate
markup and layout are handled, but nothing else), so it also copes with code
bases that no longer parse with a recent Agda.

Usage: named-where.py [OPTIONS] [FILE_OR_DIR ...]
"""

import argparse
import os
import re
import sys

# ---------------------------------------------------------------------------
# File discovery
# ---------------------------------------------------------------------------

# Literate extensions understood by Agda, see Agda.Syntax.Parser.Literate.
LITERATE_EXTS = ['.lagda', '.lagda.rst', '.lagda.tex', '.lagda.md',
                 '.lagda.org', '.lagda.tree', '.lagda.typ']
AGDA_EXTS = ['.agda'] + LITERATE_EXTS

SKIP_DIRS = {'.git', '.svn', '.hg', '_build', 'dist-newstyle', 'MAlonzo',
             '.stack-work', 'node_modules'}


def agda_kind(path):
    """Return the recognised Agda extension of PATH, or None."""
    base = os.path.basename(path)
    # Longest extension first, so that `.lagda.md` beats `.lagda`.
    for ext in sorted(AGDA_EXTS, key=len, reverse=True):
        if base.endswith(ext) and len(base) > len(ext):
            return ext
    return None


def find_files(root):
    """Yield Agda files under ROOT (a file or a directory)."""
    if os.path.isfile(root):
        if agda_kind(root):
            yield root
        return
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames
                             if d not in SKIP_DIRS and not d.startswith('.'))
        for name in sorted(filenames):
            path = os.path.join(dirpath, name)
            if agda_kind(path):
                yield path


# ---------------------------------------------------------------------------
# Literate preprocessing: blank out everything that is not Agda code,
# preserving line and column numbers (cf. Agda's `illiterate`).
# ---------------------------------------------------------------------------

def _bleach(line):
    return ''.join(c if c == '\n' else ' ' for c in line)


def _illiterate_generic(lines, is_begin, is_end):
    out, in_code = [], False
    for line in lines:
        if in_code:
            if is_end(line):
                in_code = False
                out.append(_bleach(line))
            else:
                out.append(line)
        else:
            if is_begin(line):
                in_code = True
            out.append(_bleach(line))
    return out


_MD_BEGIN = re.compile(r'^\s*```(\S*)\s*$')
_MD_END = re.compile(r'^\s*```\s*$')


def _illiterate_md(lines):
    """Markdown/Typst: ``` and ```agda blocks are code, other tags are not."""
    out, in_code, in_other = [], False, False
    for line in lines:
        if in_code:
            if _MD_END.match(line):
                in_code = False
                out.append(_bleach(line))
            else:
                out.append(line)
        elif in_other:
            if _MD_END.match(line):
                in_other = False
            out.append(_bleach(line))
        else:
            m = _MD_BEGIN.match(line)
            if m:
                if m.group(1) in ('', 'agda'):
                    in_code = True
                else:
                    in_other = True
            out.append(_bleach(line))
    return out


_RST_CODE = re.compile(r'^(.*)::\s*$')
_RST_COMMENT = re.compile(r'^\s*\.\.(\s.*)?$')


def _illiterate_rst(lines):
    """reStructuredText: an indented block after a line ending in `::`."""
    out = []
    state = 'text'     # 'text' | 'seek' (looking for the indent) | 'code'
    indent = ''
    for line in lines:
        if state == 'code':
            if line.strip() == '' or line.startswith(indent):
                out.append(line)
                continue
            state = 'text'
        if state == 'seek':
            if line.strip() == '':
                out.append(_bleach(line))
                continue
            ws = re.match(r'[ \t]*', line).group(0)
            if ws:
                indent, state = ws, 'code'
                out.append(line)
                continue
            state = 'text'
        # state == 'text'
        out.append(_bleach(line))
        if not _RST_COMMENT.match(line) and _RST_CODE.match(line):
            state = 'seek'
    return out


def illiterate(text, ext):
    """Blank out non-code parts of a literate file, keeping positions."""
    if ext == '.agda':
        return text
    lines = text.splitlines(keepends=True)
    if ext in ('.lagda', '.lagda.tex'):
        return ''.join(_illiterate_generic(
            lines,
            lambda l: re.search(r'\\begin\{code\}', l),
            lambda l: re.match(r'^[ \t]*\\end\{code\}', l)))
    if ext in ('.lagda.md', '.lagda.typ'):
        return ''.join(_illiterate_md(lines))
    if ext == '.lagda.rst':
        return ''.join(_illiterate_rst(lines))
    if ext == '.lagda.org':
        return ''.join(_illiterate_generic(
            lines,
            lambda l: re.match(r'^\s*#\+begin_src\s+agda2\b', l, re.I),
            lambda l: re.match(r'^\s*#\+end_src\s*$', l, re.I)))
    if ext == '.lagda.tree':
        return ''.join(_illiterate_generic(
            lines,
            lambda l: re.search(r'\\agda\{', l),
            lambda l: re.match(r'^[ \t]*\}', l)))
    return text


# ---------------------------------------------------------------------------
# Comment and literal removal (positions preserved)
# ---------------------------------------------------------------------------

# Characters that cannot occur inside an Agda identifier
# (cf. the `@ident` rule in Agda.Syntax.Parser.Lexer).
NON_IDENT = set(' \t\r\n(){};@."')

_CHAR_LIT = re.compile(r"'(\\[^']*|[^'\\])'")


def strip_comments(text):
    """Blank out comments, pragmas and literals, preserving all positions."""
    out = list(text)
    n = len(text)

    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n':
                out[k] = ' '

    i = 0
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"' and text[j] != '\n':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            blank(i, j)
            i = j
        elif c == "'" and (i == 0 or text[i - 1] in NON_IDENT):
            m = _CHAR_LIT.match(text, i)
            if m:
                blank(i, m.end())
                i = m.end()
            else:
                i += 1
        elif text.startswith('{-#', i):
            j = text.find('#-}', i)
            j = n if j < 0 else j + 3
            blank(i, j)
            i = j
        elif text.startswith('{-', i):
            start, depth, j = i, 1, i + 2
            while j < n and depth:
                if text.startswith('{-', j):
                    depth += 1
                    j += 2
                elif text.startswith('-}', j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            blank(start, j)
            i = j
        elif text.startswith('--', i) and (i == 0 or text[i - 1] in NON_IDENT):
            j = text.find('\n', i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        else:
            i += 1
    return ''.join(out)


# ---------------------------------------------------------------------------
# Tokenisation
# ---------------------------------------------------------------------------

_TOKEN = re.compile(r'\.\.\.|[(){};@]|\.|[^\s(){};@.]+')


class Token:
    __slots__ = ('text', 'line', 'col')

    def __init__(self, text, line, col):
        self.text, self.line, self.col = text, line, col


def tokenize(text):
    tokens = []
    for lineno, line in enumerate(text.split('\n'), start=1):
        for m in _TOKEN.finditer(line):
            tokens.append(Token(m.group(0), lineno, m.start()))
    return tokens


# ---------------------------------------------------------------------------
# Layout tracking and detection of named `where` modules
# ---------------------------------------------------------------------------

# Agda.Syntax.Parser.Tokens.layoutKeywords
LAYOUT_KEYWORDS = {
    'abstract', 'do', 'field', 'instance', 'let', 'macro', 'mutual',
    'postulate', 'primitive', 'private', 'variable', 'where', 'opaque',
}

OPEN_BRACKETS = {'(', '{'}
CLOSE_BRACKETS = {')', '}'}


class Block:
    """A layout block."""
    __slots__ = ('col', 'kw', 'decls')

    def __init__(self, col, kw):
        self.col, self.kw, self.decls = col, kw, []


class Hit:
    __slots__ = ('line', 'col', 'name', 'kind')

    def __init__(self, line, col, name, kind):
        self.line, self.col, self.name, self.kind = line, col, name, kind


def _match_where_module(tokens, i):
    """If tokens[i:] is `module [attrs] NAME where`, return NAME, else None."""
    j = i + 1
    # Skip attributes: @0, @erased, @(...)
    while j < len(tokens) and tokens[j].text == '@':
        j += 1
        if j < len(tokens) and tokens[j].text == '(':
            depth = 0
            while j < len(tokens):
                if tokens[j].text in OPEN_BRACKETS:
                    depth += 1
                elif tokens[j].text in CLOSE_BRACKETS:
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
        else:
            j += 1
    if j + 1 >= len(tokens):
        return None
    name, kw = tokens[j], tokens[j + 1]
    if kw.text != 'where':
        return None
    if name.text in LAYOUT_KEYWORDS or name.text in ('...', '.', '=', '|'):
        return None
    return name.text


def _lhs(tokens, start, end):
    """The left-hand side of the declaration starting at START (up to END).

    Stops at the first top-level `=` or layout keyword, which is where every
    LHS ends."""
    res, depth = [], 0
    for k in range(start, min(end, len(tokens))):
        t = tokens[k].text
        if t in OPEN_BRACKETS:
            depth += 1
        elif t in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and (t == '=' or t in LAYOUT_KEYWORDS):
            break
        res.append(t)
    return res


def _is_continuation(lhs):
    """Is this the LHS of a follow-up clause of a `with`/`rewrite` clause?"""
    return bool(lhs) and (lhs[0] == '...' or '|' in lhs)


def _block_flags(tokens, block, limit):
    """(has_with, has_rewrite) for the clause currently open in BLOCK.

    Walks back over preceding sibling clauses as long as they are follow-up
    clauses (`... | p` or `f x | p`) of a `with`/`rewrite` clause."""
    has_with = has_rewrite = False
    decls = block.decls
    for j in range(len(decls) - 1, -1, -1):
        start = decls[j]
        end = decls[j + 1] if j + 1 < len(decls) else limit
        lhs = _lhs(tokens, start, end)
        if 'with' in lhs:
            has_with = True
        if 'rewrite' in lhs:
            has_rewrite = True
        if not _is_continuation(lhs):
            break
    return has_with, has_rewrite


def scan_tokens(tokens):
    """Return the list of named `where` modules found in TOKENS."""
    hits = []
    stack = []
    pending = None          # layout keyword awaiting the block's first token
    prev_line = None
    prev_semi = False

    for i, tok in enumerate(tokens):
        first_on_line = tok.line != prev_line

        if not stack:
            # The very first token opens the top-level block.  Its column is
            # not necessarily 0: a file need not have a `module` header, and
            # in literate files the code may be indented.
            stack.append(Block(tok.col, 'top'))
            pending = None
            is_decl = True
        elif pending is not None:
            if stack and tok.col <= stack[-1].col:
                pass            # empty layout block
            else:
                stack.append(Block(tok.col, pending))
            pending = None
            is_decl = True
        elif first_on_line:
            while len(stack) > 1 and tok.col < stack[-1].col:
                stack.pop()
            if tok.col < stack[0].col:
                # Can happen in literate files whose code blocks are indented
                # differently; treat the outdented token as top level.
                stack[0].col = tok.col
            is_decl = tok.col == stack[-1].col
        else:
            is_decl = prev_semi

        if is_decl:
            stack[-1].decls.append(i)

        if tok.text == 'module' and not is_decl:
            name = _match_where_module(tokens, i)
            if name is not None:
                has_with = has_rewrite = False
                for blk in reversed(stack):
                    if not blk.decls:
                        continue
                    w, r = _block_flags(tokens, blk, i)
                    has_with |= w
                    has_rewrite |= r
                kind = 'with' if has_with else \
                       'rewrite' if has_rewrite else 'plain'
                hits.append(Hit(tok.line, tok.col + 1, name, kind))

        if tok.text in LAYOUT_KEYWORDS:
            pending = tok.text
        elif tok.text == 'in':
            # `in` closes the innermost `let` block -- but only if there is
            # one: the block may already have been closed by indentation, and
            # then we must not pop anything.
            for k in range(len(stack) - 1, -1, -1):
                if stack[k].kw == 'let':
                    del stack[k:]
                    break

        prev_semi = tok.text == ';'
        prev_line = tok.line

    return hits


def scan_file(path, ext):
    with open(path, 'r', encoding='utf-8', errors='replace') as f:
        text = f.read()
    return scan_tokens(tokenize(strip_comments(illiterate(text, ext))))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(
        prog='named-where.py',
        description='Find and classify named `where` modules in Agda code.',
        epilog='Locations are printed in GNU format: FILE:LINE: KIND.')
    p.add_argument('paths', nargs='*', default=['.'], metavar='FILE_OR_DIR',
                   help='where to search (default: the current directory)')
    p.add_argument('-a', '--all', action='store_true',
                   help='list all named `where` modules, not just those '
                        'under `with`/`rewrite`')
    p.add_argument('-c', '--column', action='store_true',
                   help='include the column in the reported locations')
    p.add_argument('-q', '--quiet', action='store_true',
                   help='print the summary only')
    p.add_argument('-f', '--files', action='store_true',
                   help='list the scanned files instead of scanning them')
    args = p.parse_args(argv)

    paths = args.paths or ['.']
    files = []
    for root in paths:
        if not os.path.exists(root):
            print('%s: no such file or directory' % root, file=sys.stderr)
            return 2
        files.extend(find_files(root))

    if args.files:
        for f in files:
            print(f)
        return 0

    total = anonymous = 0
    counts = {'with': 0, 'rewrite': 0, 'plain': 0}
    listing = []

    for path in files:
        try:
            hits = scan_file(path, agda_kind(path))
        except OSError as e:
            print('%s: %s' % (path, e), file=sys.stderr)
            continue
        for h in hits:
            total += 1
            if h.name == '_':
                anonymous += 1
            counts[h.kind] += 1
            if args.all or h.kind != 'plain':
                where = ('%s:%d:%d' % (path, h.line, h.col)) if args.column \
                        else ('%s:%d' % (path, h.line))
                listing.append('  %s: %s' % (where, h.kind))

    print('Scanned %d Agda file%s.' % (len(files),
                                       '' if len(files) == 1 else 's'))
    print()
    print('  named `where` modules    : %2d' % total)
    print('    thereof `module _`     : %2d' % anonymous)
    print('  under `with`             : %2d' % counts['with'])
    print('  not `with` but `rewrite` : %2d' % counts['rewrite'])
    print('  neither                  : %2d' % counts['plain'])
    if listing and not args.quiet:
        print()
        for line in listing:
            print(line)
    return 0


if __name__ == '__main__':
    sys.exit(main())
