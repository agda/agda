Release notes for Agda version 2.10.0
=====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 9.2.8 to 9.14.1.

Pragmas and options
-------------------

Errors
------

* New error `WrongNamedArgumentInLHS` for a named hidden argument on a left hand side
  that does not exist, replacing `WrongHidingInLHS` in this case.
  Like `WrongNamedArgument` on the right hand side, it lists the possible argument names
  (see [#8739](https://github.com/agda/agda/issues/8739)).
  Likewise, error `NoParameterOfName` now lists the possible parameter names.

Warnings
--------

* Warning `ShadowingInTelescope` is now on by default.

* New warning `LibraryVersionConflict` when a project uses different versions of one library
  (see [#8875](https://github.com/agda/agda/issues/8875)).
  The warning shows the dependency tree leading to the conflicting versions
  and the involved `.agda-lib` files:
  ```
  Different versions of the library 'standard-library' depended on:
  [my-project]
    ├─ [standard-library-2.3]
    └─ [my-lib]
        └─ standard-library-2.4 as [standard-library]
  Library files:
  [my-project]: /path/to/my-project/my-project.agda-lib:<line>.<col>-<col>
  [my-lib]: /path/to/my-lib/my-lib.agda-lib:<line>.<col>-<col>
  [standard-library-2.3]: /path/to/agda-stdlib-2.3/standard-library.agda-lib:1:1
  [standard-library]: /path/to/agda-stdlib-2.4/standard-library.agda-lib:1:1
  ```

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

* `unquoteDecl` and `unquoteDef` now check that the meta-program
  actually defines all the given identifiers
  (issue [#8851](https://github.com/agda/agda/issues/8851)).
  Previously, an identifier that was not declared by the meta-program
  caused an internal error, and a data type that was only declared
  (via `declareData`) but not defined (via `defineData`)
  was silently accepted (see [#7576](https://github.com/agda/agda/issues/7576)).
  Now both are reported as missing definitions.

Library management
------------------

Interaction and emacs mode
--------------------------

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
