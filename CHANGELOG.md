Release notes for Agda version 2.6.3
====================================

Installation and infrastructure
-------------------------------

Agda supports GHC versions 8.0.2 to 9.2.1.

Language
--------

* The new option `--erased-cubical` turns on a variant of Cubical Agda
  (see [#4701](https://github.com/agda/agda/issues/4701)).

  When this variant of Cubical Agda is used glue (and some related
  builtins) may only be used in erased settings. One can import
  regular Cubical Agda code from this variant of Cubical Agda, but
  names defined using Cubical Agda are (mostly) treated as if they had
  been marked as erased. See the [reference
  manual](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical-agda-with-erased-glue-and-erased-higher-constructors)
  for more details.

  The GHC and JS backends can compile code that uses
  `--erased-cubical` if the top-level module uses this flag.

  This feature is experimental.

Compiler backends
-----------------

* Both the GHC and JS backends now refuse to compile code that uses
  `--cubical`.

  Note that support for compiling code that uses `--erased-cubical`
  has been added to both backends (see above).

LaTeX backend
-------------
