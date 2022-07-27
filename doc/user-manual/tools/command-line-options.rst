.. _command-line-options:

********************
Command-line options
********************

Command-line options
--------------------

Agda accepts the following options.

General options
~~~~~~~~~~~~~~~

.. option:: --help[={TOPIC}], -?[{TOPIC}]

     Show basically this help, or more help about ``TOPIC``. Current
     topics available: ``warning``.

.. option:: --interaction

     For use with the Emacs mode (no need to invoke yourself).

.. option:: --interaction-json

     .. versionadded:: 2.6.1

     For use with other editors such as Atom (no need to invoke
     yourself).

.. option:: --interactive, -I

     Start in interactive mode (no longer supported).

.. option:: --no-projection-like

     .. versionadded:: 2.6.1

     Turn off the analysis whether a type signature likens that of a
     projection.

     Projection-likeness is an optimization that reduces the size of
     terms by dropping parameter-like reconstructible function
     arguments. Thus, it is advisable to leave this optimization on,
     the flag is meant for debugging Agda.

.. option:: --only-scope-checking

     Only scope-check the top-level module, do not type-check it (see
     :ref:`quickLaTeX`).

.. option:: --version, -V

     Show version number.

.. option:: --print-agda-dir

     .. versionadded:: 2.6.2

     Outputs the root (:envvar:`AGDA_DIR`)
     of the directory structure holding Agda's data files
     such as core libraries, style files for the backends etc.

.. option:: --transliterate

     .. versionadded:: 2.6.3

     When writing to stdout or stderr Agda will (hopefully) replace
     code points that are not supported by the current locale or code
     page by something else, perhaps question marks.

     This option is not supported when :option:`--interaction` or
     :option:`--interaction-json` are used, because when those options
     are used Agda uses UTF-8 when writing to stdout (and when reading
     from stdin).

Compilation
~~~~~~~~~~~

See :ref:`compilers` for backend-specific options.

.. option:: --compile-dir={DIR}

     Set ``DIR`` as directory for compiler output (default: the
     project root).

.. option:: --no-main

     Do not treat the requested module as the main module of a program
     when compiling.

.. option:: --with-compiler={PATH}

     Set ``PATH`` as the executable to call to compile the backend's
     output (default: ghc for the GHC backend).

Generating highlighted source code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --count-clusters

     Count extended grapheme clusters when generating LaTeX code (see
     :ref:`grapheme-clusters`).

.. option:: --css={URL}

     Set URL of the CSS file used by the HTML files to ``URL`` (can be
     relative).

.. option:: --dependency-graph={FILE}

     Generate a Dot_ file ``FILE`` with a module dependency graph.

.. option:: --dependency-graph-include={LIBRARY}

     Include modules from the given library in the dependency graph.
     This option can be used multiple times to include modules from
     several libraries. If this option is not used at all, then all
     modules are included. (Note that the module given on the command
     line might not be included.)

     A module ``M`` is considered to be in the library ``L`` if ``L``
     is the ``name`` of a ``.agda-lib`` file ``A``
     :ref:`associated<The_agda-lib_files_associated_to_a_give_Agda_file>`
     to ``M`` (even if ``M``'s file can not be found via the
     ``include`` paths in ``A``).

.. option:: --html

     Generate HTML files with highlighted source code (see
     :ref:`generating-html`).

.. option:: --html-dir={DIR}

     Set directory in which HTML files are placed to ``DIR`` (default:
     html).

.. option:: --html-highlight=[code,all,auto]

     Whether to highlight non-Agda code as comments in generated HTML
     files (default: all; see :ref:`generating-html`).

.. option:: --latex

     Generate LaTeX with highlighted source code (see
     :ref:`generating-latex`).

.. option:: --latex-dir={DIR}

     Set directory in which LaTeX files are placed to ``DIR``
     (default: latex).

.. option:: --vim

     Generate Vim_ highlighting files.

Imports and libraries
~~~~~~~~~~~~~~~~~~~~~

(see :ref:`package-system`)

.. option:: --ignore-all-interfaces

     Ignore *all* interface files, including builtin and primitive
     modules; only use this if you know what you are doing!

.. option:: --ignore-interfaces

     Ignore interface files (re-type check everything, except for
     builtin and primitive modules).

.. option:: --include-path={DIR}, -i={DIR}

     Look for imports in ``DIR``.

.. option:: --library={DIR}, -l={LIB}

     Use library ``LIB``.

.. option:: --library-file={FILE}

     Use ``{FILE}`` instead of the standard libraries file.

.. option:: --local-interfaces

     .. versionadded:: 2.6.1

     Read and write interface files next to the Agda files they
     correspond to (i.e. do not attempt to regroup them in a
     ``_build/`` directory at the project's root).

.. option:: --no-default-libraries

     Don't use default library files.

.. option:: --no-libraries

     Don't use any library files.

.. _command-line-pragmas:

Command-line and pragma options
-------------------------------

The following options can also be given in .agda files using the
:ref:`OPTIONS<options-pragma>` pragma.

Caching
~~~~~~~

.. option:: --caching, --no-caching

     Enable [disable] caching of typechecking (default).

     Default: ``--caching``

Printing and debugging
~~~~~~~~~~~~~~~~~~~~~~

.. option:: --no-unicode

     Don't use unicode characters to print terms.

.. option:: --show-implicit

     Show implicit arguments when printing.

.. option:: --show-irrelevant

     Show irrelevant arguments when printing.

.. option:: --verbose={N}, -v={N}

     Set verbosity level to ``N``.

.. option:: --profile={PROF}

    Turn on profiling option ``PROF``. Available options are

    .. list-table::

       * - ``internal``
         - Measure time taken by various parts of the system (type checking, serialization, etc)
       * - ``modules``
         - Measure time spent on individual (Agda) modules
       * - ``definitions``
         - Measure time spent on individual (Agda) definitions
       * - ``sharing``
         - Measure things related to sharing
       * - ``serialize``
         - Collect detailed statistics about serialization
       * - ``constraints``
         - Collect statistics about constraint solving
       * - ``metas``
         - Count number of created metavariables
       * - ``interactive``
         - Measure time of interactive commands

    Only one of ``internal``, ``modules``, and ``definitions`` can be turned on
    at a time. You can also give ``--profile=all`` to turn on all profiling
    options (choosing ``internal`` over ``modules`` and ``definitions``, use
    ``--profile=modules --profile=all`` to pick ``modules`` instead).

Copatterns and projections
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --copatterns, --no-copatterns

     Enable [disable] definitions by copattern matching (see
     :ref:`copatterns`).

     Default: ``--copatterns``

.. option:: --postfix-projections

     Make postfix projection notation the default.

Experimental features
~~~~~~~~~~~~~~~~~~~~~

.. option:: --confluence-check, --local-confluence-check

     .. versionadded:: 2.6.1

     Enable optional (global or local) confluence checking of REWRITE
     rules (see :ref:`confluence-check`).

.. option:: --cubical

     Enable cubical features. Turns on :option:`--without-K` (see
     :ref:`cubical`).

.. option:: --erased-cubical

     Enable a :ref:`variant<erased-cubical>` of Cubical Agda, and turn
     on :option:`--without-K`.

.. option:: --experimental-irrelevance

     Enable potentially unsound irrelevance features (irrelevant
     levels, irrelevant data matching) (see :ref:`irrelevance`).

.. option:: --injective-type-constructors

     Enable injective type constructors (makes Agda anti-classical and
     possibly inconsistent).

.. option:: --rewriting

     Enable declaration and use of REWRITE rules (see
     :ref:`rewriting`).

.. option:: --allow-exec

     Enable system calls during type checking (see :ref:`reflection`).

Errors and warnings
~~~~~~~~~~~~~~~~~~~

.. option:: --allow-incomplete-matches

     .. versionadded:: 2.6.1

     Succeed and create interface file regardless of incomplete
     pattern-matching definitions. See, also, the
     :ref:`NON_COVERING<non_covering-pragma>` pragma.

.. option:: --allow-unsolved-metas

     Succeed and create interface file regardless of unsolved meta
     variables (see :ref:`metavariables`).

.. option:: --no-positivity-check

     Do not warn about not strictly positive data types (see
     :ref:`positivity-checking`).

.. option:: --no-termination-check

     Do not warn about possibly nonterminating code (see
     :ref:`termination-checking`).

.. option:: --warning={GROUP|FLAG}, -W {GROUP|FLAG}

     Set warning group or flag (see :ref:`warnings`).

Pattern matching and equality
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --exact-split, --no-exact-split

     Require [do not require] all clauses in a definition to hold as
     definitional equalities unless marked ``CATCHALL`` (see
     :ref:`case-trees`).

     Default: ``--no-exact-split``

.. option:: --no-eta-equality

     Default records to no-eta-equality (see :ref:`eta-expansion`).

.. option:: --no-flat-split

     .. versionadded:: 2.6.1

     Disable pattern matching on ``@♭`` arguments (see
     :ref:`pattern-matching-on-flat`).

.. option:: --no-pattern-matching

     Disable pattern matching completely.

.. option:: --with-K

     Overrides a global :option:`--without-K` in a file (see
     :ref:`without-K`).

.. option:: --without-K

     Disables definitions using Streicher’s K axiom (see
     :ref:`without-K`).

.. option:: --keep-pattern-variables

     .. versionadded:: 2.6.1

     Prevent interactive case splitting from replacing variables with
     dot patterns (see :ref:`dot-patterns`).

Search depth and instances
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --instance-search-depth={N}

     Set instance search depth to ``N`` (default: 500; see
     :ref:`instance-arguments`),

.. option:: --inversion-max-depth={N}

     Set maximum depth for pattern match inversion to ``N`` (default:
     50). Should only be needed in pathological cases.

.. option:: --termination-depth={N}

     Allow termination checker to count decrease/increase upto ``N``
     (default: 1; see :ref:`termination-checking`).

.. option:: --overlapping-instances, --no-overlapping-instances

     Consider [do not consider] recursive instance arguments during
     pruning of instance candidates.

     Default: ``--no-overlapping-instances``


Other features
~~~~~~~~~~~~~~

.. option:: --double-check

     Enable double-checking of all terms using the internal
     typechecker.

.. option:: --guardedness, --no-guardedness

     Enable [disable] constructor-based guarded corecursion (see
     :ref:`coinduction`).

     The option ``--guardedness`` is inconsistent with sized types and
     it is turned off by :option:`--safe` (but can be turned on again,
     as long as not also :option:`--sized-types` is on).

     Default: ``--guardedness``

.. option:: --irrelevant-projections, --no-irrelevant-projections

     .. versionadded:: 2.5.4

     Enable [disable] projection of irrelevant record fields (see
     :ref:`irrelevance`). The option ``--irrelevant-projections``
     makes Agda inconsistent.

     Default (since version 2.6.1): ``--no-irrelevant-projections``

.. option:: --auto-inline

     Turn on automatic compile-time inlining. See :ref:`inline-pragma` for more information.

.. option:: --no-auto-inline

     Disable automatic compile-time inlining (default). Only definitions marked
     ``INLINE`` will be inlined.

.. option:: --no-fast-reduce

     Disable reduction using the Agda Abstract Machine.

.. option:: --call-by-name

     Disable call-by-need evaluation in the Agda Abstract Machine.

.. option:: --no-forcing

     Disable the forcing optimisation. Since Agda 2.6.1 is a pragma
     option.

.. option:: --no-print-pattern-synonyms

     Always expand :ref:`pattern-synonyms` during printing. With this
     option enabled you can use pattern synonyms freely, but Agda will
     not use any pattern synonyms when printing goal types or error
     messages, or when generating patterns for case splits.

.. option:: --no-syntactic-equality

     Disable the syntactic equality shortcut in the conversion
     checker.

.. option:: --syntactic-equality={N}

     .. versionadded:: 2.6.3

     Give the syntactic equality shortcut ``N`` units of fuel (``N``
     must be a natural number).

     If ``N`` is omitted, then the syntactic equality shortcut is
     enabled without any restrictions.

     If ``N`` is given, then the syntactic equality shortcut is given
     ``N`` units of fuel. The exact meaning of this is
     implementation-dependent, but successful uses of the shortcut do
     not affect the amount of fuel.

.. option:: --safe

     Disable postulates, unsafe :ref:`OPTIONS<options-pragma>` pragmas
     and ``primTrustMe``. Turns off :option:`--sized-types` and
     :option:`--guardedness` (at most one can be turned back on again)
     (see :ref:`safe-agda`).

.. option:: --sized-types, --no-sized-types

     Enable [disable] sized types (see :ref:`sized-types`).

     The option ``--sized-types`` is inconsistent with
     constructor-based guarded corecursion and it is turned off by
     :option:`--safe` (but can be turned on again, as long as not also
     :option:`--guardedness` is on).

     Default: ``--sized-types``

.. option:: --type-in-type

     Ignore universe levels (this makes Agda inconsistent; see
     :ref:`type-in-type <type-in-type>`).

.. option:: --omega-in-omega

     Enable typing rule `Setω : Setω` (this makes Agda inconsistent;
     see :ref:`omega-in-omega <omega-in-omega>`).

.. option:: --universe-polymorphism, --no-universe-polymorphism

     Enable [disable] universe polymorphism (see
     :ref:`universe-levels`).

     Default: ``--universe-polymorphism``

.. option:: --cumulativity, --no-cumulativity

     .. versionadded:: 2.6.1

     Enable [disable] cumulative subtyping of universes, i.e. if `A :
     Set i` then also `A : Set j` for all `j >= i`.

     Default: ``--no-cumulativity``

.. option:: --no-import-sorts

     .. versionadded:: 2.6.2

     Disable the implicit statement `open import Agda.Primitive using
     (Set; Prop)` at the start of each top-level Agda module.

.. option:: --save-metas, --no-save-metas

     .. versionadded:: 2.6.3

     Save [or do not save] meta-variables in ``.agdai`` files. The
     alternative is to expand the meta-variables to their definitions.
     This option can affect performance. The default is to not save
     the meta-variables.

.. option:: --erase-record-parameters

     ..versionadded:: 2.6.3

     Automatically marks parameters to definitions in a record module
     as erased.

.. _warnings:

Warnings
~~~~~~~~

The :option:`-W` or :option:`--warning` option can be used to disable
or enable different warnings. The flag ``-W error`` (or
``--warning=error``) can be used to turn all warnings into errors,
while ``-W noerror`` turns this off again.

A group of warnings can be enabled by ``-W {group}``, where ``group``
is one of the following:

.. option:: all

     All of the existing warnings.

.. option:: warn.

     Default warning level

.. option:: ignore

     Ignore all warnings.

The command ``agda --help=warning`` provides information about which
warnings are turned on by default.

Individual warnings can be turned on and off by ``-W {Name}`` and ``-W
{noName}`` respectively. The flags available are:

.. option:: AbsurdPatternRequiresNoRHS

     RHS given despite an absurd pattern in the LHS.

.. option:: CantGeneralizeOverSorts

     Attempt to generalize over sort metas in 'variable' declaration.

.. option:: CoInfectiveImport

     Importing a file not using e.g. :option:`--safe` from one which
     does.

.. option:: CoverageIssue

     Failed coverage checks.

.. option:: CoverageNoExactSplit

     Failed exact split checks.

.. option:: DeprecationWarning

     Feature deprecation.

.. option:: EmptyAbstract

     Empty ``abstract`` blocks.

.. option:: EmptyInstance

     Empty ``instance`` blocks.

.. option:: EmptyMacro

     Empty ``macro`` blocks.

.. option:: EmptyMutual

     Empty ``mutual`` blocks.

.. option:: EmptyPostulate

     Empty ``postulate`` blocks.

.. option:: EmptyPrimitive

     Empty ``primitive`` blocks.

.. option:: EmptyPrivate

     Empty ``private`` blocks.

.. option:: EmptyRewritePragma

     Empty ``REWRITE`` pragmas.

.. option:: IllformedAsClause

     Illformed ``as``-clauses in ``import`` statements.

.. option:: InfectiveImport

     Importing a file using e.g. :option;`--cubical` into one which
     doesn't.

.. option:: InstanceNoOutputTypeName

     Instance arguments whose type does not end in a named or variable
     type are never considered by instance search.

.. option:: InstanceArgWithExplicitArg

   Instance arguments with explicit arguments are never considered by
   instance search.

.. option:: InstanceWithExplicitArg

     Instance declarations with explicit arguments are never
     considered by instance search.

.. option:: InvalidCatchallPragma

     :ref:`CATCHALL<catchall-pragma>` pragmas before a non-function clause.

.. option:: InvalidNoPositivityCheckPragma

     No positivity checking pragmas before non-`data``, ``record`` or
     ``mutual`` blocks.

.. option:: InvalidTerminationCheckPragma

     Termination checking pragmas before non-function or ``mutual``
     blocks.

.. option:: InversionDepthReached

     Inversions of pattern-matching failed due to exhausted inversion
     depth.

.. option:: LibUnknownField

     Unknown field in library file.

.. option:: MissingDefinitions

     Names declared without an accompanying definition.

.. option:: ModuleDoesntExport

     Names mentioned in an import statement which are not exported by
     the module in question.

.. option:: NotAllowedInMutual

     Declarations not allowed in a mutual block.

.. option:: NotStrictlyPositive

     Failed strict positivity checks.

.. option:: OldBuiltin

     Deprecated :ref:`BUILTIN<built-ins>` pragmas.

.. option:: OverlappingTokensWarning

     Multi-line comments spanning one or more literate text blocks.

.. option:: PolarityPragmasButNotPostulates

     Polarity pragmas for non-postulates.

.. option:: PragmaCompiled

     :ref:`COMPILE<foreign-function-interface>` pragmas not allowed in safe mode.

.. option:: PragmaCompileErased

     :ref:`COMPILE<foreign-function-interface>` pragma targeting an erased symbol.

.. option:: PragmaNoTerminationCheck

     :ref:`NO_TERMINATION_CHECK<terminating-pragma>` pragmas are deprecated.

.. option:: RewriteMaybeNonConfluent

     Failed confluence checks while computing overlap.

.. option:: RewriteNonConfluent

     Failed confluence checks while joining critical pairs.

.. option:: SafeFlagNonTerminating

     :ref:`NON_TERMINATING<non_terminating-pragma>` pragmas with the safe flag.

.. option:: SafeFlagNoPositivityCheck

     :ref:`NO_POSITIVITY_CHECK<no_positivity_check-pragma>` pragmas with the safe flag.

.. option:: SafeFlagNoUniverseCheck

     :ref:`NO_UNIVERSE_CHECK<no_universe_check-pragma>` pragmas with the safe flag.

.. option:: SafeFlagPolarity

     :ref:`POLARITY<polarity-pragma>` pragmas with the safe flag.

.. option:: SafeFlagPostulate

     ``postulate`` blocks with the safe flag

.. option:: SafeFlagPragma

     Unsafe :ref:`OPTIONS<options-pragma>` pragmas with the safe flag.

.. option:: SafeFlagTerminating

     :ref:`TERMINATING<terminating-pragma>` pragmas with the safe flag.

.. option:: SafeFlagWithoutKFlagPrimEraseEquality

     ``primEraseEquality`` used with the safe and without-K flags.

.. option:: ShadowingInTelescope

     Repeated variable name in telescope.

.. option:: TerminationIssue

     Failed termination checks.

.. option:: UnknownFixityInMixfixDecl

     Mixfix names without an associated fixity declaration.

.. option:: UnknownNamesInFixityDecl

     Names not declared in the same scope as their syntax or fixity
     declaration.

.. option:: UnknownNamesInPolarityPragmas

     Names not declared in the same scope as their polarity pragmas.

.. option:: UnreachableClauses

     Unreachable function clauses.

.. option:: UnsolvedConstraints

     Unsolved constraints.

.. option:: UnsolvedInteractionMetas

     Unsolved interaction meta variables.

.. option:: UnsolvedMetaVariables

     Unsolved meta variables.

.. option:: UselessAbstract

     ``abstract`` blocks where they have no effect.

.. option:: UselessInline

     :ref:`INLINE<inline-pragma>` pragmas where they have no effect.

.. option:: UselessInstance

     ``instance`` blocks where they have no effect.

.. option:: UselessPrivate

     ``private`` blocks where they have no effect.

.. option:: UselessPublic

     ``public`` blocks where they have no effect.

.. option:: WithoutKFlagPrimEraseEquality

     ``primEraseEquality`` used with the without-K flags.

.. option:: WrongInstanceDeclaration

     Terms marked as eligible for instance search should end with a
     name.

Examples
--------

Run Agda with all warnings
enabled, except for warnings about empty ``abstract`` blocks:

.. code-block:: console

   agda -W all --warning=noEmptyAbstract file.agda

Run Agda on a file which uses the standard library.
Note that you must have already created a ``libraries`` file
as described in :ref:`package-system`

.. code-block:: console

   agda -l standard-library -i. file.agda

(Or if you have added ``standard-library`` to your ``defaults`` file, simply ``agda file.agda``)

.. _consistency-checking-options:

Consistency checking of options used
------------------------------------

Agda checks that options used in imported modules are consistent with
each other.

An *infective* option is an option that if used in one module, must be
used in all modules that depend on this module. The following options
are infective:

* :option:`--cubical`
* ``--prop``
* ``--rewriting``

A *coinfective* option is an option that if used in one module, must
be used in all modules that this module depends on. The following
options are coinfective:

* :option:`--safe`
* :option:`--without-K`
* :option:`--no-universe-polymorphism`
* :option:`--no-sized-types`
* :option:`--no-guardedness`

Agda records the options used when generating an interface file. If
any of the following options differ when trying to load the interface
again, the source file is re-typechecked instead:

* :option:`--termination-depth`
* :option:`--no-unicode`
* :option:`--allow-unsolved-metas`
* :option:`--allow-incomplete-matches`
* :option:`--no-positivity-check`
* :option:`--no-termination-check`
* :option:`--type-in-type`
* :option:`--omega-in-omega`
* :option:`--no-sized-types`
* :option:`--no-guardedness`
* :option:`--injective-type-constructors`
* ``--prop``
* :option:`--no-universe-polymorphism`
* :option:`--irrelevant-projections`
* :option:`--experimental-irrelevance`
* :option:`--without-K`
* :option:`--exact-split`
* :option:`--no-eta-equality`
* :option:`--rewriting`
* :option:`--cubical`
* :option:`--overlapping-instances`
* :option:`--safe`
* :option:`--double-check`
* :option:`--no-syntactic-equality`
* :option:`--no-auto-inline`
* :option:`--no-fast-reduce`
* :option:`--instance-search-depth`
* :option:`--inversion-max-depth`
* :option:`--warning`
* :option:`--allow-exec`
* :option:`--save-metas`


.. _Vim: https://www.vim.org/
.. _Dot: http://www.graphviz.org/content/dot-language
