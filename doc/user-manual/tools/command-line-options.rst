.. _command-line-options:

********************
Command-line options
********************

Command-line options
--------------------

Agda accepts the following options.

General options
~~~~~~~~~~~~~~~

=================================  ================  ===========================================
:samp:`--version`                  :samp:`-V`        Show version number

:samp:`--help`                     :samp:`-?`        Show basically this help

:samp:`--interactive`              :samp:`-I`        Start in interactive mode
                                                     (no longer supported)

:samp:`--interaction`                                For use with the Emacs mode
                                                     (no need to invoke yourself)
=================================  ================  ===========================================

Compilation
~~~~~~~~~~~

See :ref:`compilers` for backend-specific options.

=================================  ================  ===========================================
:samp:`--no-main`                                    Do not treat the requested module as the
                                                     main module of a program when compiling

:samp:`--compile-dir={DIR}`                          Set :samp:`{DIR}` as directory for compiler
                                                     output (default: the project root)

:samp:`--no-forcing`                                 Disable the forcing optimisation
=================================  ================  ===========================================

Generating highlighted source code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

=================================  ================  ===========================================
:samp:`--vim`                                        Generate Vim_ highlighting files

:samp:`--latex`                                      Generate LaTeX with highlighted source code
                                                     (see :ref:`generating-latex`)

:samp:`--latex-dir={DIR}`                            Set directory in which LaTeX files are
                                                     placed to :samp:`{DIR}` (default: latex)

:samp:`--count-clusters`                             Count extended grapheme clusters when
                                                     generating LaTeX
                                                     code (see :ref:`grapheme-clusters`)

:samp:`--html`                                       Generate HTML files with highlighted source
                                                     code (see :ref:`generating-html`)

:samp:`--html-dir={DIR}`                             Set directory in which HTML files are
                                                     placed to :samp:`{DIR}` (default: html)

:samp:`--css={URL}`                                  Set URL of the CSS file used by the HTML
                                                     files to :samp:`{URL}` (can be relative)

:samp:`--dependency-graph={FILE}`                    Generate a Dot_ file :samp:`{FILE}` with a
                                                     module dependency graph
=================================  ================  ===========================================

Imports and libraries
~~~~~~~~~~~~~~~~~~~~~

(see :ref:`package-system`)

=================================  ================  ===========================================
:samp:`--ignore-interfaces`                          Ignore interface files (re-type check
                                                     everything)

:samp:`--include-path={DIR}`       :samp:`-i={DIR}`  Look for imports in :samp:`{DIR}`

:samp:`--library={DIR}`            :samp:`-l={LIB}`  Use library :samp:`{LIB}`

:samp:`--library-file={FILE}`                        Use :samp:`{FILE}` instead of the standard
                                                     libraries file

:samp:`--no-libraries`                               Don't use any library files

:samp:`--no-default-libraries`                       Don't use default library files
=================================  ================  ===========================================

Sharing and caching
~~~~~~~~~~~~~~~~~~~

=================================  ================  ===========================================
:samp:`--sharing`                                    Enable sharing and call-by-need evaluation
                                                     (experimental) (default: OFF)

:samp:`--no-sharing`                                 Disable sharing and call-by-need evaluation

:samp:`--caching`                                    Enable caching of typechecking
                                                     (experimental) (default: OFF)

:samp:`--no-caching`                                 Disable caching of typechecking

:samp:`--only-scope-checking`                        Only scope-check the top-level module,
                                                     do not type-check it
=================================  ================  ===========================================


.. _command-line-pragmas:

Command-line and pragma options
-------------------------------

The following options can also be given in .agda files in the
``{-# OPTIONS --{opt₁} --{opt₂} ... #-}`` form at the top of the file.

Printing and debugging
~~~~~~~~~~~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--show-implicit`                                                Show implicit arguments when printing

:samp:`--show-irrelevant`                                              Show irrelevant arguments when printing

:samp:`--verbose={N}`                               :samp:`-v={N}`     Set verbosity level to :samp:`{N}`
==================================================  =================  ===========================================

Copatterns and projections
~~~~~~~~~~~~~~~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--copatterns`                                                   Enable definitions by copattern
                                                                       matching (default; see :ref:`copatterns`)

:samp:`--no-copatterns`                                                Disable definitions by copattern
                                                                       matching

:samp:`--postfix-projections`                                          Make postfix projection notation the
                                                                       default
==================================================  =================  ===========================================

Experimental features
~~~~~~~~~~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--proof-irrelevance`                                            Enable proof irrelevance
                                                                       (experimental feature)

:samp:`--injective-type-constructors`                                  Enable injective type constructors
                                                                       (makes Agda anti-classical and
                                                                       possibly inconsistent)

:samp:`--guardedness-preserving-type-constructors`                     Treat type constructors as
                                                                       inductive constructors when checking
                                                                       productivity

:samp:`--experimental-irrelevance`                                     Enable potentially unsound irrelevance
                                                                       features (irrelevant levels, irrelevant
                                                                       data matching)
                                                                       (see :ref:`irrelevance`)

:samp:`--rewriting`                                                    Enable declaration and use of REWRITE
                                                                       rules
                                                                       (see :ref:`rewriting`)
==================================================  =================  ===========================================

Errors and warnings
~~~~~~~~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--allow-unsolved-metas`                                         Succeed and create interface file
                                                                       regardless of unsolved meta variables
                                                                       (see :ref:`metavariables`)

:samp:`--no-positivity-check`                                          Do not warn about not strictly positive
                                                                       data types
                                                                       (see :ref:`positivity-checking`)

:samp:`--no-termination-check`                                         Do not warn about possibly
                                                                       nonterminating code
                                                                       (see :ref:`termination-checking`)

:samp:`--warning={MODE}`                            :samp:`-W={MODE}`  Set warning mode to :samp:`{MODE}`
                                                                       (available:
                                                                       :samp:`warn` display warnings,
                                                                       :samp:`error` turn warnings into errors,
                                                                       and :samp:`ignore` ignore warnings)
==================================================  =================  ===========================================

Pattern matching and equality
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--without-K`                                                    Disables definitions using Streicher’s
                                                                       K axiom (see :ref:`without-K`)

:samp:`--with-K`                                                       Overrides a global ``--without-K``
                                                                       in a file (see :ref:`without-K`)

:samp:`--no-pattern-matching`                                          Disable pattern matching completely

:samp:`--exact-split`                                                  Require all clauses in a definition to
                                                                       hold as definitional equalities unless
                                                                       marked ``CATCHALL``
                                                                       (see :ref:`case-trees`)

:samp:`--no-exact-split`                                               Do not require all clauses in a definition
                                                                       to hold as definitional equalities
                                                                       (default)

:samp:`--no-eta-equality`                                              Default records to no-eta-equality
                                                                       (see :ref:`eta-expansion`)
==================================================  =================  ===========================================

Search depth
~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--termination-depth={N}`                                        Allow termination checker to count
                                                                       decrease/increase upto :samp:`{N}`
                                                                       (default: 1;
                                                                       see :ref:`termination-checking`)

:samp:`--instance-search-depth={N}`                                    Set instance search depth to
                                                                       :samp:`{N}` (default: 500; see
                                                                       :ref:`instance-arguments`)
==================================================  =================  ===========================================

Other features
~~~~~~~~~~~~~~

==================================================  =================  ===========================================
:samp:`--safe`                                                         Disable postulates, unsafe ``OPTION``
                                                                       pragmas and ``primTrustMe``
                                                                       (see :ref:`safe-agda`)

:samp:`--type-in-type`                                                 Ignore universe levels
                                                                       (this makes Agda inconsistent; see
                                                                       :ref:`universe-levels`)

:samp:`--sized-types`                                                  Use sized types
                                                                       (default, inconsistent with
                                                                       "musical" coinduction; see
                                                                       :ref:`sized-types`)

:samp:`--no-sized-types`                                               Disable sized types
                                                                       (see :ref:`sized-types`)

:samp:`--universe-polymorphism`                                        Enable universe polymorphism (default;
                                                                       see :ref:`universe-levels`)

:samp:`--no-universe-polymorphism`                                     Disable universe polymorphism
                                                                       (see :ref:`universe-levels`)

:samp:`--no-irrelevant-projections`                                    Disable projection of irrelevant record
                                                                       fields
                                                                       (see :ref:`irrelevance`)
==================================================  =================  ===========================================


.. _Vim: http://www.vim.org/
.. _Dot: http://www.graphviz.org/content/dot-language
