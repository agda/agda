# `named-where` — find and classify named `where` modules

Background: [#2897](https://github.com/agda/agda/issues/2897) and
[#8698](https://github.com/agda/agda/issues/8698).  Named `where` modules in
clauses whose context has been refined (by pattern matching) or re-typed (by
`with`-abstraction) are unsound and are rejected by Agda.  We are considering
deprecating named `where` modules in `with`/`rewrite` blocks altogether, so we
want to know how prevalent they are in existing code.

## What counts as a named `where` module

The `module M where` form of a `where` clause:

```agda
f x = rhs
  module M where
  g = ...
```

as opposed to an ordinary module declaration, which starts a new declaration in
the enclosing block.  The two are told apart by *layout*: a named `where` module
belongs to the preceding clause and is therefore indented deeper than the layout
column of the enclosing block (or sits on the same line as the right-hand side,
as in `f = e module M where`).

Agda also treats `module _ where` in this position as a named (`SomeWhere`)
`where` module, so it is counted here too, with a separate sub-count.

## Usage

```
src/release-tools/named-where/named-where.py [OPTIONS] [FILE_OR_DIR ...]
```

With no argument the search starts in the current directory.  Directories are
searched recursively for `.agda` and `.lagda[.md|.rst|.tex|.org|.tree|.typ]`
files; `.git`, `_build`, `dist-newstyle`, `MAlonzo`, `node_modules` and hidden
directories are skipped.

Options:

| option | meaning |
|---|---|
| `-a`, `--all`    | list all named `where` modules, not only those under `with`/`rewrite` |
| `-c`, `--column` | include the column in the reported locations |
| `-q`, `--quiet`  | print the summary only |
| `-f`, `--files`  | list the files that would be scanned |

Example:

```
$ src/release-tools/named-where/named-where.py test/
Scanned 4927 Agda files.

  named `where` modules    : 49
    thereof `module _`     : 12
  under `with`             :  2
  not `with` but `rewrite` :  2
  neither                  : 45

  test/Fail/Issue3823.agda:50: rewrite
  test/Fail/Issue8698.agda:41: with
  test/Succeed/Issue3824.agda:14: rewrite
  test/Succeed/Issue8698.agda:34: with
```

Locations are printed in GNU format (`FILE:LINE: KIND`), so editors can jump to
them.

## How it works

The tool is purely lexical, so it also copes with code bases that no longer
parse with a recent Agda:

1. **Literate files** are *illiterated*: everything outside the code blocks is
   blanked out, keeping line and column numbers intact (as Agda does).
2. **Comments, pragmas and string/character literals** are blanked out.
   Block comments nest; `--` only starts a comment at a token boundary, so
   identifiers such as `x--y` and `_--_` are left alone.
3. The result is **tokenised** and run through a simplified version of Agda's
   **layout** algorithm (the layout keywords are those of
   `Agda.Syntax.Parser.Tokens.layoutKeywords`).  A `module NAME where` whose
   `module` token does *not* start a declaration in the current layout block is
   a named `where` module.
4. Each hit is **classified** by looking at the enclosing clause and, through
   nested `where` blocks, at the enclosing clauses of that: `with` if any of
   them is a `with` clause, otherwise `rewrite` if any of them is a `rewrite`
   clause, otherwise `plain`.  Follow-up clauses (`... | p`, `f x | p`) are
   traced back to the `with`/`rewrite` clause that introduced them.

Note that a `with`-clause affects nested anonymous `where` blocks too, so

```agda
f x with p
... | true = aux
  where
  aux = ...
    module M where   -- classified as `with`
```

counts as being under `with`.

## Tests

```
src/release-tools/named-where/test/run-tests.sh
```

runs the tool on `test/Cases.agda` (a valid Agda file covering ordinary module
declarations, multi-line right-hand sides, `with` in both styles, `rewrite`,
nesting inside anonymous `where` blocks, `module _ where`, and decoys in
comments and string literals) plus one file per literate format, and diffs the
result against `test/expected.txt`.

The expected values were cross-checked against Agda itself by temporarily
making `Agda.TypeChecking.Rules.Def.checkWhere` report every named `where`
module it checks.

## Survey (2026-09-05)

| code base | files | named `where` modules | thereof `module _` | under `with` | `rewrite` |
|---|---:|---:|---:|---:|---:|
| Agda test suite (`test/`)      | 4927 | 49 | 12 | 2 | 2 |
| standard library (`std-lib/src`) | 1183 | 9 | 0 | 0 | 0 |
| cubical library (`cubical/Cubical`) | 1172 | 9 | 5 | 0 | 0 |

The four hits in the test suite are the regression tests for #8698 and #3823/#3824;
neither library uses a named `where` module under `with` or `rewrite` at all.

### Cross-check against Agda

`Agda.TypeChecking.Rules.Def.checkWhere` was temporarily patched to report every
named `where` module it checks, and Agda was run over both libraries and the
test suites:

* standard library: 9 reported by Agda, 9 found by the tool, **identical**;
* cubical library: 9 reported by Agda, 9 found by the tool, **identical**;
* test suites: all 36 reported by Agda are found by the tool; the additional
  ones the tool reports are in files the suites do not check (`test/Fail`
  tests that abort earlier, `test/LaTeXAndHTML/`) or are *empty* named `where`
  modules, which Agda discards before `checkWhere` sees them.
