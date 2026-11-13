Release notes for Agda version 2.10.0
=====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 9.2.8 to 9.14.1.

* New: GitHub releases include a statically linked Linux ARM64 binary
  (see [#7603](https://github.com/agda/agda/issues/7603)).

Pragmas and options
-------------------

Errors
------

Warnings
--------

* New warning `WrongAssociativity` suggests `infixr` for prefix operators
  declared with `infixl` and `infixl` for postfix operators declared with
  `infixr`.

* Warning `ShadowingInTelescope` is now on by default.

* `InstanceNoOutputTypeName` and `InstanceArgWithExplicitArg` now also warn
  about instance `variable` declarations and anonymous instance arguments
  in function types.

* New warning `PragmaCompileDefined` when a `COMPILE GHC` pragma overrides
  the definition of a (non-abstract) function.

Syntax
------

Changes to the Agda syntax.

Language
--------

Changes to type checker and other components defining the Agda language.

Builtins
--------

* Binding the `BUILTIN REWRITE` relation will now reduce the name before binding it.
  This means you can now use an alias to another type as the rewrite relation
  (see https://github.com/agda/agda/issues/6697).

Reflection
----------

Library management
------------------

Interaction and emacs mode
--------------------------

* Bindings for all unicode mathematical font and other stylized variants of
  Latin letters, Greek letters, and digits, the superscript letters `𐞥ꟲꟳꟴ꟱𐞲ᶹ`,
  and the variant equality symbols `⧣﹦꞊`.

* The Emacs mode is now less eager to "pop up" the Agda information
  buffer.

Backends
--------

Issues closed
-------------

For 2.10.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.10.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

### Consistency issues

### Internal errors

### Other regressions

### Other issues

Pull requests merged for 2.10.0
-------------------------------
