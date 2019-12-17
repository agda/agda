.. _command-line-options:

********************
Command-line options
********************

Command-line options
--------------------

Agda accepts the following options.

General options
~~~~~~~~~~~~~~~

.. option:: --version, -V

     Show version number

.. option:: --help[={TOPIC}], -?[{TOPIC}]

     Show basically this help, or more help about ``TOPIC``. Current
     topics available: ``warning``.

.. option:: --interactive, -I

     Start in interactive mode (no longer supported).

.. option:: --interaction

     For use with the Emacs mode (no need to invoke yourself).

.. option:: --interaction-json

     For use with other editors such as Atom (no need to invoke
     yourself).

.. option:: --only-scope-checking

     Only scope-check the top-level module, do not type-check it.

Compilation
~~~~~~~~~~~

See :ref:`compilers` for backend-specific options.

.. option:: --no-main

     Do not treat the requested module as the main module of a program
     when compiling.

.. option:: --compile-dir={DIR}

     Set ``DIR`` as directory for compiler output (default: the
     project root).

.. option:: --no-forcing

     Disable the forcing optimisation.

.. option:: --with-compiler={PATH}

     Set ``PATH`` as the executable to call to compile the backend's
     output (default: ghc for the GHC backend).

Generating highlighted source code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

See :ref:`LaTeX backend options<latex-backend-options>` and :ref:`HTML
backend options<html-backend-options>` for specific options for LaTeX
and HTML.

.. option:: --vim

     Generate Vim_ highlighting files.

.. option:: --latex

     Generate LaTeX with highlighted source code (see
     :ref:`generating-latex`).

.. option:: --html

     Generate HTML files with highlighted source code (see
     :ref:`generating-html`).

.. option:: --dependency-graph={FILE}

     Generate a Dot_ file ``FILE`` with a module dependency graph.

Imports and libraries
~~~~~~~~~~~~~~~~~~~~~

(see :ref:`package-system`)

.. option:: --ignore-interfaces

     Ignore interface files (re-type check everything, except for
     builtin and primitive modules).

.. option:: --ignore-all-interfaces

     Ignore *all* interface files, including builtin and primitive
     modules; only use this if you know what you are doing!

.. option:: --local-interfaces

     Read and write interface files next to the Agda files they
     correspond to (i.e. do not attempt to regroup them in a
     ``_build/`` directory at the project's root).

.. option:: --include-path={DIR}, -i={DIR}

     Look for imports in ``DIR``.

.. option:: --library={DIR}, -l={LIB}

     Use library ``LIB``.

.. option:: --library-file={FILE}

     Use ``{FILE}`` instead of the standard libraries file.

.. option:: --no-libraries

     Don't use any library files.

.. option:: --no-default-libraries

     Don't use default library files.

.. _command-line-pragmas:

Command-line and pragma options
-------------------------------

The following options can also be given in .agda files in the
``{-# OPTIONS --{opt₁} --{opt₂} ... #-}`` form at the top of the file.

Caching
~~~~~~~

.. option:: --caching

     Enable caching of typechecking (default).

.. option:: --no-caching

     Disable caching of typechecking.

Printing and debugging
~~~~~~~~~~~~~~~~~~~~~~

.. option:: --show-implicit

     Show implicit arguments when printing.

.. option:: --show-irrelevant

     Show irrelevant arguments when printing.

.. option:: --no-unicode

     Don't use unicode characters to print terms.

.. option:: --verbose={N}, -v={N}

     Set verbosity level to ``N``.

Copatterns and projections
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --copatterns

     Enable definitions by copattern matching (default; see
     :ref:`copatterns`).

.. option:: --no-copatterns

     Disable definitions by copattern matching.

.. option:: --postfix-projections

     Make postfix projection notation the default.

Experimental features
~~~~~~~~~~~~~~~~~~~~~

.. option:: --injective-type-constructors

     Enable injective type constructors (makes Agda anti-classical and
     possibly inconsistent).

.. option:: --experimental-irrelevance

     Enable potentially unsound irrelevance features (irrelevant
     levels, irrelevant data matching) (see :ref:`irrelevance`).

.. option:: --rewriting

     Enable declaration and use of REWRITE rules (see
     :ref:`rewriting`).

.. option:: --cubical

     Enable cubical features. Turns on :option:`--without-K` (see
     :ref:`cubical`).

Errors and warnings
~~~~~~~~~~~~~~~~~~~

.. option:: --allow-unsolved-metas

     Succeed and create interface file regardless of unsolved meta
     variables (see :ref:`metavariables`).

.. option:: --allow-incomplete-matches

     .. versionadded:: 2.6.1

     Succeed and create interface file regardless of incomplete
     pattern-matching definitions. See, also, the
     :ref:`NON_COVERING<non_covering_pragma>` pragma.

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

.. option:: --without-K

     Disables definitions using Streicher’s K axiom (see
     :ref:`without-K`).

.. option:: --with-K

     Overrides a global :option:`--without-K` in a file (see
     :ref:`without-K`).

.. option:: --no-pattern-matching

     Disable pattern matching completely.

.. option:: --exact-split

     Require all clauses in a definition to hold as definitional
     equalities unless marked ``CATCHALL`` (see :ref:`case-trees`).

.. option:: --no-exact-split

     Do not require all clauses in a definition to hold as
     definitional equalities (default).

.. option:: --no-eta-equality

     Default records to no-eta-equality (see :ref:`eta-expansion`).

Search depth and instances
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --termination-depth={N}

     Allow termination checker to count decrease/increase upto ``N``
     (default: 1; see :ref:`termination-checking`).

.. option:: --instance-search-depth={N}

     Set instance search depth to ``N`` (default: 500; see
     :ref:`instance-arguments`),

.. option:: --inversion-max-depth={N}

     Set maximum depth for pattern match inversion to ``N`` (default:
     50). Should only be needed in pathological cases.

.. option:: --no-overlapping-instances

     Don't consider recursive instance arguments during pruning of
     instance candidates (default).

.. option:: --overlapping-instances

     Consider recursive instance arguments during pruning of instance
     candidates.


Other features
~~~~~~~~~~~~~~

.. option:: --safe

     Disable postulates, unsafe ``OPTION`` pragmas and
     ``primTrustMe``. Turns off :option:`--sized-types` and
     :option:`--guardedness` (at most one can be turned back on again)
     (see :ref:`safe-agda`).

.. option:: --type-in-type

     Ignore universe levels (this makes Agda inconsistent; see
     :ref:`universe-levels`).

.. option:: --omega-in-omega

     Enable typing rule `Setω : Setω` (this makes Agda inconsistent).

.. option:: --sized-types

     Enable sized types (default, inconsistent with constructor-based
     guarded corecursion; see :ref:`sized-types`). Turned off by
     :option:`--safe` (but can be turned on again, as long as not also
     :option:`--guardedness` is on).

.. option:: --no-sized-types

     Disable sized types (see :ref:`sized-types`).

.. option:: --guardedness

     Enable constructor-based guarded corecursion (default,
     inconsistent with sized types; see :ref:`coinduction`). Turned
     off by :option:`--safe` (but can be turned on again, as long as
     not also :option:`--sized-types` is on).

.. option:: --no-guardedness

     Disable constructor-based guarded corecursion (see
     :ref:`coinduction`).

.. option:: --universe-polymorphism

     Enable universe polymorphism (default; see
     :ref:`universe-levels`).

.. option:: --no-universe-polymorphism

     Disable universe polymorphism (see :ref:`universe-levels`).

.. option:: --irrelevant-projections

     .. versionadded:: 2.5.4

     Enable projection of irrelevant record fields (inconsistent). See
     :ref:`irrelevance`. Since Agda 2.6.1 is off by default.

.. option:: --no-irrelevant-projections

     .. versionadded:: 2.5.4

     Disable projection of irrelevant record fields. See
     :ref:`irrelevance`. Since Agda 2.6.1 is on by default.

.. option:: --no-auto-inline

     Disable automatic compile-time inlining.  Only definitions marked
     ``INLINE`` will be inlined.

.. option:: --no-print-pattern-synonyms

     Always expand :ref:`pattern-synonyms` during printing. With this
     option enabled you can use pattern synonyms freely, but Agda will
     not use any pattern synonyms when printing goal types or error
     messages, or when generating patterns for case splits.

.. option:: --double-check

     Enable double-checking of all terms using the internal
     typechecker.

.. option:: --no-syntactic-equality

     Disable the syntactic equality shortcut in the conversion
     checker.

.. option:: --no-fast-reduce

     Disable reduction using the Agda Abstract Machine.


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

     ``CATCHALL`` pragmas before a non-function clause.

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

     Deprecated ``BUILTIN`` pragmas.

.. option:: OverlappingTokensWarning

     Multi-line comments spanning one or more literate text blocks.

.. option:: PolarityPragmasButNotPostulates

     Polarity pragmas for non-postulates.

.. option:: PragmaCompiled

     ``COMPILE`` pragmas not allowed in safe mode.

.. option:: PragmaCompileErased

     ``COMPILE`` pragma targeting an erased symbol.

.. option:: PragmaNoTerminationCheck

     ``NO_TERMINATION_CHECK`` pragmas are deprecated.

.. option:: RewriteMaybeNonConfluent

     Failed confluence checks while computing overlap.

.. option:: RewriteNonConfluent

     Failed confluence checks while joining critical pairs.

.. option:: SafeFlagNonTerminating

     ``NON_TERMINATING`` pragmas with the safe flag.

.. option:: SafeFlagNoPositivityCheck

     ``NO_POSITIVITY_CHECK`` pragmas with the safe flag.

.. option:: SafeFlagNoUniverseCheck

     ``NO_UNIVERSE_CHECK`` pragmas with the safe flag.

.. option:: SafeFlagPolarity

     ``POLARITY`` pragmas with the safe flag.

.. option:: SafeFlagPostulate

     ``postulate`` blocks with the safe flag

.. option:: SafeFlagPragma

     Unsafe ``OPTIONS`` pragmas with the safe flag.

.. option:: SafeFlagTerminating

     ``TERMINATING`` pragmas with the safe flag.

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

     ``INLINE`` pragmas where they have no effect.

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

For example, the following command runs Agda with all warnings
enabled, except for warnings about empty ``abstract`` blocks:

.. code-block:: console

   agda -W all --warning=noEmptyAbstract file.agda


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


.. _Vim: https://www.vim.org/
.. _Dot: http://www.graphviz.org/content/dot-language
