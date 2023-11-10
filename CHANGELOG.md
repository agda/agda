Release notes for Agda version 2.6.5
====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 8.6.5 to 9.8.1.

Pragmas and options
-------------------

* When the new pragma option `--opaque` is used, then every function
  definition, mutual block, `unquoteDecl` or `unquoteDef` that is not
  explicitly marked as opaque or transparent is put into a separate
  opaque block ([#6934](https://github.com/agda/agda/issues/6934)).

  Local definitions in where clauses are put into the same opaque
  block as their parent definitions, unless `opaque` or `transparent`
  are used.

  Note that definitions in let expressions or before a record type's
  last field declaration are not made opaque.

Syntax
------

Additions to the Agda syntax.

* [**Breaking**] The new keyword `transparent` introduces a block of
  transparent definitions
  ([#6934](https://github.com/agda/agda/issues/6934)). This keyword
  can be used to make definitions inside opaque blocks transparent,
  and also to make definitions transparent when `--opaque` is used.

Language
--------

Changes to type checker and other components defining the Agda language.

Reflection
----------

Changes to the meta-programming facilities.

Library management
------------------

Interaction and emacs mode
--------------------------

Backends
--------

Other issues closed
-------------------

For 2.6.5, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.6.5+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.6.5`.
