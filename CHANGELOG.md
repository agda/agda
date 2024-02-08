Release notes for Agda version 2.6.4.2
======================================

This is a bug-fix release.  It aims to be API-compatible with 2.6.4.1.
Agda 2.6.4.2 supports GHC versions 8.6.5 to 9.8.1.

Highlights
----------

- Fix an inconsistency in Cubical Agda related to catch-all clauses: [Issue #7033](https://github.com/agda/agda/issues/7033)
- Fix a bug related to `opaque`:  [Issue #6972](https://github.com/agda/agda/issues/6972)
- Fix some internal errors:
  * [Issue #7029](https://github.com/agda/agda/issues/7029)
  * [Issue #7034](https://github.com/agda/agda/issues/7034)
  * [Issue #7044](https://github.com/agda/agda/issues/7044)
- Fix building with cabal flag `-f debug-serialisation`: [Issue #7081](https://github.com/agda/agda/issues/7081)

List of closed issues
---------------------

For 2.6.4.2, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.4.2+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

- [Issue #6972](https://github.com/agda/agda/issues/6972): Unfolding fails when code is split up into multiple files
- [Issue #6999](https://github.com/agda/agda/issues/6999): Unification failure for function type with erased argument
- [Issue #7020](https://github.com/agda/agda/issues/7020): question: haskell backend extraction of `Data.Nat.DivMod.DivMod`?
- [Issue #7029](https://github.com/agda/agda/issues/7029): Internal error on confluence check when rewriting a defined symbol with a hole
- [Issue #7033](https://github.com/agda/agda/issues/7033): transpX clauses can be beat out by user-written _ clauses, leading to proof of ⊥
- [Issue #7034](https://github.com/agda/agda/issues/7034): Internal error with --two-level due to blocking on solved meta
- [Issue #7044](https://github.com/agda/agda/issues/7044): Serializer crashes on blocked definitions when using --allow-unsolved-metas
- [Issue #7048](https://github.com/agda/agda/issues/7048): hcomp symbols in interface not hidden under --cubical-compatible
- [Issue #7059](https://github.com/agda/agda/issues/7059): Don't recompile if --keep-pattern-variables option changes
- [Issue #7070](https://github.com/agda/agda/issues/7070): Don't set a default maximum heapsize for Agda runs
- [Issue #7081](https://github.com/agda/agda/issues/7081): Missing `IsString` instance with debug flags enabled
- [Issue #7095](https://github.com/agda/agda/issues/7095): Agda build flags appear as "automatic", but they are all "manual"

These PRs not corresponding to issues were merged:

- [PR #6988](https://github.com/agda/agda/issues/6988): Provide a `.agda-lib` for Agda builtins
- [PR #7065](https://github.com/agda/agda/issues/7065): Some documentation fixes
- [PR #7072](https://github.com/agda/agda/issues/7072): Add 'Inference in Agda' to the list of tutorials
- [PR #7091](https://github.com/agda/agda/issues/7091): Add course to “Courses using Agda”
