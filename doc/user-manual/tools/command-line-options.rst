.. _command-line-options:

********************
Command-line options
********************

Command-line options
--------------------

Agda accepts the following options on the command line.
Where noted, these options can also serve as *pragma options*,
i.e., be supplied in a file via the ``{-# OPTIONS ... #-}`` pragma
or in the ``flags`` section of an ``.agda-lib`` file.

General options
~~~~~~~~~~~~~~~

.. option:: --help[={TOPIC}], -?[{TOPIC}]

     Show basically this help, or more help about ``TOPIC``.
     Available topics:

     - ``error``:
       List the names of Agda's errors.

     - ``warning``:
       List warning groups and individual warnings and their default status.
       Instruct how to toggle benign warnings.

.. option:: --interaction

     For use with the Emacs mode (no need to invoke yourself).

.. option:: --interaction-json

     .. versionadded:: 2.6.1

     For use with other editors such as Atom (no need to invoke
     yourself).

.. option:: --interaction-exit-on-error

     .. versionadded:: 2.6.3

     Makes Agda exit with a non-zero exit code if :option:`--interaction` or
     :option:`--interaction-json` are used and a type error is encountered. The
     option also makes Agda exit with exit code 113 if Agda fails to
     parse a command.

     This option might for instance be used if Agda is controlled from
     a script.

.. option:: --interactive, -I

     Start in interactive mode (not maintained).

.. option:: --trace-imports[=(0|1|2|3)]

     .. versionadded:: 2.6.4

     Configure printing of messages when an imported module is accessed during type-checking.

     .. list-table::

       * - ``0``
         - Do not print any messages about checking a module.
       * - ``1``
         - | Print only `Checking ...` when an access to an uncompiled module occurs.
           | This is the default behavior if ``--trace-imports`` is not specified.
       * - ``2``
         - | Use the effect of ``1``, but also print `Finished ...`
           | when a compilation of an uncompiled module is finished.
           | This is the behavior if ``--trace-imports`` is specified without a value.
       * - ``3``
         - | Use the effect of ``2``, but also print `Loading ...`
           | when a compiled module (interface) is accessed during the type-checking.

.. option:: --colour[=(auto|always|never)], --color[=(auto|always|never)]

    .. versionadded:: 2.6.4

      Configure whether or not Agda's standard output diagnostics should
      use ANSI terminal colours for syntax highlighting (e.g. error
      messages, warnings).

    .. list-table::

        * - ``always``
          - Always print diagnostic in colour.
        * - ``auto``
          - | Automatically determine whether or not it is safe for
            | standard output to include colours. Colours will be used
            | when writing directly to a terminal device on Linux and
            | macOS.
            |
            | This is the default value.
        * - ``never``
          - Never print output in colour.

    The American spelling, ``--color``, is also accepted.

    **Note:** Currently, the colour scheme for terminal output can not
    be configured. If the colours are not legible on your terminal,
    please use ``--colour=never`` for now.

.. option:: --only-scope-checking

     .. versionadded:: 2.5.3

     Only scope-check the top-level module, do not type-check it (see
     :ref:`quickLaTeX`).

.. option:: --version, -V

     Show version number and cabal flags used in this build of Agda.

.. option:: --numeric-version

     Show just the version number.

.. option:: --print-agda-app-dir

     .. versionadded:: 2.6.4.1

     Outputs the (:envvar:`AGDA_DIR`) directory containing Agda's
     application configuration files, such as the ``defaults`` and
     ``libraries`` files, as described in :ref:`package-system`.

.. option:: --print-agda-dir

     .. versionadded:: 2.6.2

     Alias of :option:`--print-agda-data-dir`.

.. option:: --print-agda-data-dir

     .. versionadded:: 2.6.4.1

     Outputs the root of the directory structure holding Agda's data
     files such as core libraries, style files for the backends, etc.

     While this location is usually determined at installation time, it
     can be controlled at runtime using the environment variable
     :envvar:`Agda_datadir`.

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

     Do not treat the requested/current module as the main module of a program
     when compiling.

     Pragma option since 2.5.3.

.. option:: --main

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-main`.

.. option:: --with-compiler={PATH}

     Set ``PATH`` as the executable to call to compile the backend's
     output (default: ``ghc`` for the GHC backend).

Generating highlighted source code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --count-clusters

     .. versionadded:: 2.5.3

     Count extended grapheme clusters when generating LaTeX code (see
     :ref:`grapheme-clusters`).
     Available only when Agda was built with Cabal flag :option:`enable-cluster-counting`.

     Pragma option since 2.5.4.

.. option:: --no-count-clusters

     .. versionadded:: 2.6.4

     Opposite of :option:`--count-clusters`. Default.

.. option:: --css={URL}

     Set URL of the CSS file used by the HTML files to ``URL`` (can be
     relative).

.. option:: --dependency-graph={FILE}

     .. versionadded:: 2.3.0

     Generate a Dot_ file ``FILE`` with a module dependency graph.

.. option:: --dependency-graph-include={LIBRARY}

     .. versionadded:: 2.6.3

     Include modules from the given library in the dependency graph.
     This option can be used multiple times to include modules from
     several libraries. If this option is not used at all, then all
     modules are included. (Note that the module given on the command
     line might not be included.)

     A module ``M`` is considered to be in the library ``L`` if ``L``
     is the ``name`` of an ``.agda-lib`` file
     :ref:`associated<The_agda-lib_files_associated_to_a_given_Agda_file>`
     to ``M`` (even if ``M``'s file cannot be found via the
     ``include`` paths given in the ``.agda-lib`` file).

.. option:: --highlight-occurrences

     .. versionadded:: 2.6.2

     When :ref:`generating HTML <generating-html>`,
     place the :file:`highlight-hover.js` script
     in the output directory (see :option:`--html-dir`).
     In the presence of the script,
     hovering over an identifier in the rendering of the HTML
     will highlight all occurrences of the same identifier on the page.

.. option:: --html

     .. versionadded:: 2.2.0

     Generate HTML files with highlighted source code (see
     :ref:`generating-html`).

.. option:: --html-dir={DIR}

     Set directory in which HTML files are placed to ``DIR`` (default:
     ``html``).

.. option:: --html-highlight=[code,all,auto]

     .. versionadded:: 2.6.0

     Whether to highlight non-Agda code as comments in generated HTML
     files (default: ``all``; see :ref:`generating-html`).

.. option:: --latex

     .. versionadded:: 2.3.2

     Generate LaTeX with highlighted source code (see
     :ref:`generating-latex`).

.. option:: --latex-dir={DIR}

     .. versionadded:: 2.5.2

     Set directory in which LaTeX files are placed to ``DIR``
     (default: ``latex``).

.. option:: --vim

     Generate Vim_ highlighting files.

Imports and libraries
~~~~~~~~~~~~~~~~~~~~~

(see :ref:`package-system`)

.. option:: --ignore-all-interfaces

     .. versionadded:: 2.6.0

     Ignore *all* interface files, including builtin and primitive
     modules; only use this if you know what you are doing!

.. option:: --ignore-interfaces

     Ignore interface files (re-type check everything, except for
     builtin and primitive modules).

.. option:: --include-path={DIR}, -i={DIR}

     Look for imports in ``DIR``.
     This option can be given multiple times.

.. option:: --library={DIR}, -l={LIB}

     .. versionadded:: 2.5.1

     Use library ``LIB``.

.. option:: --library-file={FILE}

     .. versionadded:: 2.5.1

     Use ``FILE`` instead of the standard ``libraries`` file.

.. option:: --local-interfaces

     .. versionadded:: 2.6.1

     Prefer to read and write interface files next to the Agda files they
     correspond to (i.e. do not attempt to regroup them in a ``_build/``
     directory at the project's root, except if they already exist there).

.. option:: --no-default-libraries

     .. versionadded:: 2.5.1

     Don't use default library files.

.. option:: --no-libraries

     .. versionadded:: 2.5.2

     Don't use any library files.

.. _command-line-pragmas:

Command-line and pragma options
-------------------------------

The following options can also be given in Agda files using the
:ref:`OPTIONS<options-pragma>` pragma.

Performance
~~~~~~~~~~~

.. option:: --auto-inline

     .. versionadded:: 2.6.2

     Turn on automatic compile-time inlining. See :ref:`inline-pragma` for more information.

.. option:: --no-auto-inline

     .. versionadded:: 2.5.4

     Disable automatic compile-time inlining (default). Only definitions marked
     ``INLINE`` will be inlined.
     Default since 2.6.2.

.. option:: --caching, --no-caching

     .. versionadded:: 2.5.4

     Enable or disable caching of typechecking.

     Default: ``--caching``.

.. option:: --call-by-name

     .. versionadded:: 2.6.2

     Disable call-by-need evaluation in the Agda Abstract Machine.

.. option:: --no-call-by-name

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--call-by-name`.

.. option:: --no-fast-reduce

     .. versionadded:: 2.6.0

     Disable reduction using the Agda Abstract Machine.

.. option:: --fast-reduce

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-fast-reduce`.

.. option:: --no-forcing

     .. versionadded:: 2.2.10

     Disable the forcing optimisation. Since Agda 2.6.1 it is a pragma
     option.

.. option:: --forcing

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-forcing`.

.. option:: --no-projection-like

     .. versionadded:: 2.6.1

     Turn off the analysis whether a type signature likens that of a
     projection.

     Projection-likeness is an optimization that reduces the size of
     terms by dropping parameter-like reconstructible function
     arguments. Thus, it is advisable to leave this optimization on,
     the flag is meant for debugging Agda.

     See also the :ref:`NOT_PROJECTION_LIKE<not_projection_like-pragma>` pragma.

.. option:: --projection-like

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-projection-like`.

Printing and debugging
~~~~~~~~~~~~~~~~~~~~~~

.. option:: --no-unicode

     .. versionadded:: 2.5.4

     Do not use unicode characters to print terms.

.. option:: --unicode

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-unicode`.

.. option:: --show-identity-substitutions

     .. versionadded:: 2.6.2

     Show all arguments of metavariables when pretty-printing a term,
     even if they amount to just applying all the variables in the context.

.. option:: --no-show-identity-substitutions

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--show-identity-substitutions`.

.. option:: --show-implicit

     Show implicit arguments when printing.

.. option:: --no-show-implicit

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--show-implicit`.

.. option:: --show-irrelevant

     .. versionadded:: 2.3.2

     Show irrelevant arguments when printing.

.. option:: --no-show-irrelevant

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--show-irrelevant`.

.. option:: --verbose={N}, -v={N}

     Set verbosity level to ``N``. This only has an effect if
     Agda was installed with the :option:`debug` flag.

.. option:: --profile={PROF}

     .. versionadded:: 2.6.3

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
       * - ``conversion``
         - Count number of times various steps of the conversion algorithm are
           used (reduction, eta-expansion, syntactic equality, etc)


    Only one of ``internal``, ``modules``, and ``definitions`` can be turned on
    at a time. You can also give ``--profile=all`` to turn on all profiling
    options (choosing ``internal`` over ``modules`` and ``definitions``, use
    ``--profile=modules --profile=all`` to pick ``modules`` instead).

Copatterns and projections
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --copatterns, --no-copatterns

     .. versionadded:: 2.4.0

     Enable or disable definitions by copattern matching (see
     :ref:`copatterns`).

     Default: ``--copatterns`` (since 2.4.2.4).

.. option:: --postfix-projections

     .. versionadded:: 2.5.2

     Make postfix projection notation the default.
     On by default since 2.7.0.

.. option:: --no-postfix-projections

     .. versionadded:: 2.6.4

     Opposite of :option:`--postfix-projections`.

Experimental features
~~~~~~~~~~~~~~~~~~~~~

.. option:: --allow-exec

     .. versionadded:: 2.6.2

     Enable system calls during type checking (see :ref:`reflection`).

.. option:: --no-allow-exec

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--allow-exec`.

.. option:: --confluence-check, --local-confluence-check, --no-confluence-check

     .. versionadded:: 2.6.1

     Enable optional (global or local) confluence checking of REWRITE
     rules (see :ref:`confluence-check`).

     Default is :option:`--no-confluence-check`.

.. option:: --cubical

     .. versionadded:: 2.6.0

     Enable cubical features. Turns on :option:`--cubical-compatible`
     and :option:`--without-K` (see :ref:`cubical`).

.. option:: --erased-cubical

     .. versionadded:: 2.6.3

     Enable a :ref:`variant<erased-cubical>` of Cubical Agda, and turn
     on :option:`--without-K`.

.. option:: --experimental-irrelevance

     .. versionadded:: 2.3.0

     Enable potentially unsound irrelevance features (irrelevant
     levels, irrelevant data matching) (see :ref:`irrelevance`).

.. option:: --no-experimental-irrelevance

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--experimental-irrelevance`.

.. option:: --guarded

     .. versionadded:: 2.6.2

     Enable locks and ticks for guarded recursion
     (see :ref:`Guarded Type Theory <guarded>`).

.. option:: --no-guarded

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--guarded`.

.. option:: --injective-type-constructors

     .. versionadded:: 2.2.8

     Enable injective type constructors (makes Agda anti-classical and
     possibly inconsistent).

.. option:: --no-injective-type-constructors

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--injective-type-constructors`.

.. option:: --irrelevant-projections, --no-irrelevant-projections

     .. versionadded:: 2.5.4

     Enable [disable] projection of irrelevant record fields (see
     :ref:`irrelevance`). The option ``--irrelevant-projections``
     makes Agda inconsistent.

     Default (since version 2.6.1): ``--no-irrelevant-projections``.

.. option:: --lossy-unification, --no-lossy-unification

     .. versionadded:: 2.6.2

     Enable a constraint-solving heuristic akin to first-order unification, see :ref:`lossy-unification`.
     Implies :option:`--no-require-unique-meta-solutions`.

.. option:: --no-lossy-unification

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--lossy-unification`.

.. option:: --require-unique-meta-solutions, --no-require-unique-meta-solutions

      .. versionadded:: 2.7.0

    When turned off, type checking is allowed to use heuristics to solve meta
    variables that do not necessarily guarantee unique solutions. In
    particular, it can make use of :ref:`INJECTIVE_FOR_INFERENCE <injective-for-inference-pragma>`
    pragmas.

    ``--no-require-unique-meta-solutions`` is implied by the :option:`--lossy-unification` flag.

    Default: ``--require-unique-meta-solutions``

.. option:: --prop, --no-prop

     .. versionadded:: 2.6.0

     Enable or disable declaration and use of
     definitionally proof-irrelevant propositions
     (see :ref:`proof-irrelevant propositions <prop>`).

     Default: ``--no-prop``.
     In this case, ``Prop`` is since 2.6.4 not in scope
     by default (:option:`--import-sorts`).

.. option:: --rewriting

     .. versionadded:: 2.4.2.4

     Enable declaration and use of REWRITE rules (see
     :ref:`rewriting`).

.. option:: --no-rewriting

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--rewriting`.

.. option:: --two-level

     .. versionadded:: 2.6.2

     Enable the use of strict (non-fibrant) type universes ``SSet``
     *(two-level type theory)*.
     Since 2.6.4, brings ``SSet`` into scope unless :option:`--no-import-sorts`.

.. option:: --no-two-level

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--two-level`.



Errors and warnings
~~~~~~~~~~~~~~~~~~~

.. option:: --allow-incomplete-matches

     .. versionadded:: 2.6.1

     Succeed and create interface file regardless of incomplete
     pattern-matching definitions. See also the
     :ref:`NON_COVERING<non_covering-pragma>` pragma.

.. option:: --no-allow-incomplete-matches

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--allow-incomplete-matches`.

.. option:: --allow-unsolved-metas

     Succeed and create interface file regardless of unsolved meta
     variables (see :ref:`metavariables`).

.. option:: --no-allow-unsolved-metas

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--allow-unsolved-metas`.

.. option:: --no-positivity-check

     Do not warn about not strictly positive data types (see
     :ref:`positivity-checking`).

.. option:: --positivity-check

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-positivity-check`.

.. option:: --no-termination-check

     Do not warn about possibly nonterminating code (see
     :ref:`termination-checking`).

.. option:: --termination-check

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-termination-check`.

.. option:: --warning={GROUP|FLAG}, -W {GROUP|FLAG}

     .. versionadded:: 2.5.3

     Set warning group or flag (see :ref:`warnings`).

Pattern matching and equality
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --exact-split, --no-exact-split

     .. versionadded:: 2.5.1

     Require [do not require] all clauses in a definition to hold as
     definitional equalities unless marked ``CATCHALL`` (see
     :ref:`case-trees`).

     Default: ``--no-exact-split``.

.. option:: --hidden-argument-puns, --no-hidden-argument-puns

     .. versionadded:: 2.6.4

     Enable [disable] :ref:`hidden argument puns
     <hidden_argument_puns>`.

     Default: ``--no-hidden-argument-puns``.

.. option:: --no-eta-equality

     .. versionadded:: 2.5.1

     Default records to ``no-eta-equality`` (see :ref:`eta-expansion`).

.. option:: --eta-equality

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-eta-equality`.

.. option:: --cohesion

     .. versionadded:: 2.6.3

     Enable the cohesion modalities, in particular ``@♭`` (see
     :ref:`flat`).

.. option:: --no-cohesion

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--cohesion`.

.. option:: --flat-split

     .. versionadded:: 2.6.1

     Enable pattern matching on ``@♭`` arguments (see
     :ref:`pattern-matching-on-flat`).
     Implies :option:`--cohesion`.

.. option:: --no-flat-split

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--flat-split`.

.. option:: --polarity, --no-polarity

     .. versionadded:: 2.6.5

     Enables the use of modal polarity annotations, and their interaction with
     the positivity checker. See :ref:`polarity`.

     Default: :option:`--no-polarity`.

.. option:: --no-pattern-matching

     .. versionadded:: 2.4.0

     Disable pattern matching completely.

.. option:: --pattern-matching

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-pattern-matching`.

.. option:: --with-K

     .. versionadded:: 2.4.2

     Overrides a global :option:`--without-K` in a file (see
     :ref:`without-K`).

.. option:: --without-K

     .. versionadded:: 2.2.10

     Disables reasoning principles incompatible with univalent type
     theory, most importantly Streicher's K axiom (see
     :ref:`without-K`).

.. option:: --cubical-compatible

     .. versionadded:: 2.6.3

     Generate internal support code necessary for use from Cubical Agda
     (see :ref:`cubical-compatible`). Implies :option:`--without-K`.

.. option:: --keep-pattern-variables

     .. versionadded:: 2.6.1

     Prevent interactive case splitting from replacing variables with
     dot patterns (see :ref:`dot-patterns`).

     Default since 2.7.0.

.. option:: --no-keep-pattern-variables

     .. versionadded:: 2.6.4

     Opposite of :option:`--keep-pattern-variables`.

.. option:: --infer-absurd-clauses, --no-infer-absurd-clauses

     .. versionadded:: 2.6.4

     ``--no-infer-absurd-clauses`` prevents interactive case splitting and coverage checking from automatically filtering out absurd clauses.
     This means that these absurd clauses have to be written out in the Agda text.
     Try this option if you experience type checking performance degradation with omitted absurd clauses.

     Default: ``--infer-absurd-clauses``.

.. option:: --large-indices, --no-large-indices

     .. versionadded:: 2.6.4

     Allow constructors to store values of types whose sort is larger
     than that being defined, when these arguments are forced by the
     constructor's type.

     When :option:`--safe` is given, this flag can not be combined with
     :option:`--without-K` or :option:`--forced-argument-recursion`,
     since both of these combinations are known to be inconsistent.

     When :option:`--no-forcing` is given, this option is redundant.

     Default: ``--no-large-indices``.

Recursion
~~~~~~~~~

.. option:: --forced-argument-recursion, --no-forced-argument-recursion

     .. versionadded:: 2.6.4

     Allow the use of forced constructor arguments as termination
     metrics. This flag may be necessary for Agda to accept nontrivial
     uses of induction-induction.

     Default: ``--forced-argument-recursion``.

.. option:: --guardedness, --no-guardedness

     .. versionadded:: 2.6.0

     Enable [disable] constructor-based guarded corecursion (see
     :ref:`coinduction`).

     The option ``--guardedness`` is inconsistent with sized types,
     thus, it cannot be used with both :option:`--safe` and
     :option:`--sized-types`.

     Default: ``--no-guardedness`` (since 2.6.2).

.. option:: --sized-types, --no-sized-types

     .. versionadded:: 2.2.0

     Enable [disable] sized types (see :ref:`sized-types`).

     The option ``--sized-types`` is inconsistent with
     constructor-based guarded corecursion,
     thus, it cannot be used with both :option:`--safe`
     and :option:`--guardedness`.

     Default: ``--no-sized-types`` (since 2.6.2).

.. option:: --termination-depth={N}

     .. versionadded:: 2.2.8

     Allow termination checker to count decrease/increase upto ``N``
     (default: 1; see :ref:`termination-checking`).

Sorts and universes
~~~~~~~~~~~~~~~~~~~

.. option:: --type-in-type

     Ignore universe levels (this makes Agda inconsistent; see
     :ref:`type-in-type <type-in-type>`).

.. option:: --no-type-in-type

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--type-in-type`.

.. option:: --omega-in-omega

     .. versionadded:: 2.6.0

     Enable typing rule ``Setω : Setω`` (this makes Agda inconsistent;
     see :ref:`omega-in-omega <omega-in-omega>`).

.. option:: --no-omega-in-omega

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--omega-in-omega`.

.. option:: --level-universe, --no-level-universe

     .. versionadded:: 2.6.4

     Makes ``Level`` live in its own universe ``LevelUniv`` and
     disallows having levels depend on terms that are not levels themselves.
     When this option is turned off, ``LevelUniv`` still exists,
     but reduces to ``Set`` (see :ref:`level-universe <level-universe>`).

     Note: While compatible with the :option:`--cubical` option, this option is
     currently not compatible with cubical builtin files.

     Default: :option:`--no-level-universe`.

.. option:: --universe-polymorphism, --no-universe-polymorphism

     .. versionadded:: 2.3.0

     Enable [disable] universe polymorphism (see
     :ref:`universe-levels`).

     Default: ``--universe-polymorphism``.

.. option:: --cumulativity, --no-cumulativity

     .. versionadded:: 2.6.1

     Enable [disable] cumulative subtyping of universes, i.e.,
     if ``A : Set i`` then also ``A : Set j`` for all ``j >= i``.

     Default: ``--no-cumulativity``.

Search depth and instances
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. option:: --instance-search-depth={N}

     .. versionadded:: 2.5.2

     Set instance search depth to ``N`` (default: 500; see
     :ref:`instance-arguments`).

.. option:: --inversion-max-depth={N}

     .. versionadded:: 2.5.4

     Set maximum depth for pattern match inversion to ``N`` (default:
     50). Should only be needed in pathological cases.

.. option:: --backtracking-instance-search, --no-backtracking-instance-search

     .. versionadded:: 2.6.5

     Consider [do not consider] recursive instance arguments during
     pruning of instance candidates, see :ref:`backtracking-instances`

     Default: ``--no-backtracking-instance-search``.

     This option used to be called ``--overlapping-instances``.

.. option:: --qualified-instances, --no-qualified-instances

     .. versionadded:: 2.6.2

     Consider [do not consider] instances that are (only) in scope
     under a qualified name.

     Default: ``--qualified-instances``.


Other features
~~~~~~~~~~~~~~

.. option:: --double-check

     Enable double-checking of all terms using the internal
     typechecker.
     Off by default.

.. option:: --no-double-check

     .. versionadded:: 2.6.2

     Opposite of :option:`--double-check`.  On by default.

.. option:: --keep-covering-clauses

     .. versionadded:: 2.6.3

     Save function clauses computed by the coverage checker to the interface file.
     Required by some external backends.

.. option:: --no-keep-covering-clauses

     .. versionadded:: 2.6.4

     Opposite of :option:`--keep-covering-clauses`, default.

.. option:: --no-print-pattern-synonyms

     .. versionadded:: 2.5.4

     Always expand :ref:`pattern-synonyms` during printing. With this
     option enabled you can use pattern synonyms freely, but Agda will
     not use any pattern synonyms when printing goal types or error
     messages, or when generating patterns for case splits.

.. option:: --print-pattern-synonyms

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-print-pattern-synonyms`.

.. option:: --no-syntactic-equality

     .. versionadded:: 2.6.0

     Disable the syntactic equality shortcut in the conversion
     checker.

.. option:: --syntactic-equality={N}

     .. versionadded:: 2.6.3

     Give the syntactic equality shortcut ``N`` units of fuel (``N``
     must be a natural number).

     If ``N`` is omitted, then the syntactic equality shortcut is
     enabled without any restrictions. (This is the default.)

     If ``N`` is given, then the syntactic equality shortcut is given
     ``N`` units of fuel. The exact meaning of this is
     implementation-dependent, but successful uses of the shortcut do
     not affect the amount of fuel.

     Note that this option is experimental and subject to change.

.. option:: --safe

     .. versionadded:: 2.3.0

     Disable postulates, unsafe :ref:`OPTIONS<options-pragma>` pragmas
     and ``primTrustMe``. Prevents to have both :option:`--sized-types` and
     :option:`--guardedness` on.
     Further reading: :ref:`safe-agda`.

.. option:: --no-import-sorts

     .. versionadded:: 2.6.2

     Disable the implicit statement
     ``open import Agda.Primitive using (Set; ...)``
     at the start of each top-level Agda module.

.. option:: --import-sorts

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-import-sorts`.

     Brings ``Set`` into scope, and if :option:`--prop` is active,
     also ``Prop``, and if :option:`--two-level` is active, even ``SSet``.

.. option:: --no-load-primitives

     .. versionadded:: 2.6.3

     Do not load the primitive modules (``Agda.Primitive``,
     ``Agda.Primitive.Cubical``) when type-checking this program. This is
     useful if you want to declare Agda's very magical primitives in a
     Literate Agda file of your choice.

     If you are using this option, it is your responsibility to ensure
     that all of the ``BUILTIN`` things defined in those modules are
     loaded. Agda will not work otherwise.

     Implies :option:`--no-import-sorts`.

     Incompatible with :option:`--safe`.

.. option:: --load-primitives

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--no-load-primitives`.

.. option:: --save-metas, --no-save-metas

     .. versionadded:: 2.6.3

     Save [or do not save] meta-variables in ``.agdai`` files. Not saving means
     that all meta-variable solutions are inlined into the interface. Currently,
     even if :option:`--save-metas` is used, very few meta-variables are
     actually saved, and this option is more like an anticipation of possible
     future optimizations.

     Default: :option:`--no-save-metas`.

Erasure
~~~~~~~

.. option:: --erasure, --no-erasure

     .. versionadded:: 2.6.4

     Allow use of the annotations ``@0`` and ``@erased``; allow use of
     names defined in Cubical Agda in Erased Cubical Agda; and mark
     parameters as erased in the type signatures of constructors and
     record fields (if :option:`--with-K` is not active this is not
     done for indexed data types).

     Default: :option:`--no-erasure`.

.. option:: --erased-matches, --no-erased-matches

     .. versionadded:: 2.6.4

     Allow matching in erased positions for single-constructor,
     non-indexed data/record types. (This kind of matching is always
     allowed for record types with η-equality.)

     Default: :option:`--erased-matches` when :option:`--with-K` is active,
     either by explicit activation or the absence of options like :option:`--without-K`;
     otherwise :option:`--no-erased-matches`.

     If :option:`--erased-matches` is given explicitly, it implies :option:`--erasure`.

.. option:: --erase-record-parameters

     .. versionadded:: 2.6.3

     Mark parameters as erased in record module telescopes.

     Implies :option:`--erasure`.

.. option:: --no-erase-record-parameters

     .. versionadded:: 2.6.4

     Default, opposite of :option:`--erase-record-parameters`.

.. option:: --lossy-unification

     .. versionadded:: 2.6.4

     Enable lossy unification, see :ref:`lossy-unification`.

.. _warnings:

Warnings
--------

The :option:`-W` or :option:`--warning` option can be used to disable
or enable different warnings. The flag ``-W error`` (or
``--warning=error``) can be used to turn all warnings into errors,
while ``-W noerror`` turns this off again.

A group of warnings can be enabled by ``-W {GROUP}``, where ``GROUP``
is one of the following:

.. option:: all

     All of the existing warnings.

.. option:: warn

     Default warning level.

.. option:: ignore

     Ignore all warnings.

The command ``agda --help=warning`` provides information about which
warnings are turned on by default.

Benign warnings
~~~~~~~~~~~~~~~

Individual non-fatal warnings can be turned on and off by ``-W {NAME}`` and ``-W no{NAME}`` respectively.
The list containing any warning ``NAME`` can be produced by ``agda --help=warning``:

.. option:: AbsurdPatternRequiresAbsentRHS

     RHS given despite an absurd pattern in the LHS.

.. option:: BuiltinDeclaresIdentifier

     A ``BUILTIN`` pragma that declares an identifier, but has been given an existing one.

.. option:: AsPatternShadowsConstructorOrPatternSynonym

     ``@``-patterns that shadow constructors or pattern synonyms.

.. option:: CantGeneralizeOverSorts

     Attempts to generalize over sort metas in ``variable`` declaration.

.. option:: ClashesViaRenaming

     Clashes introduced by ``renaming``.

.. option:: ConflictingPragmaOptions

     Conflicting pragma options. For instance, both ``--this`` and ``--no-that`` when
     ``--this`` implies ``--that``.

.. option:: ConfluenceCheckingIncompleteBecauseOfMeta

     Incomplete confluence checks because of unsolved metas.

.. option:: ConfluenceForCubicalNotSupported

     Attempts to check confluence with :option:`--cubical`.

.. option:: CoverageNoExactSplit

     Failed exact split checks.

.. option:: DeprecationWarning

     Deprecated features.

.. option:: DuplicateFields

     ``record`` expression with duplicate field names.

.. option:: DuplicateInterfaceFiles

     There exists both a local interface file and an interface file in ``_build``.

.. option:: DuplicateRecordDirective

     Conflicting directives in a record declaration.

.. option:: DuplicateRewriteRule

     Duplicate declaration of a name as :ref:`REWRITE<rewriting>` rule.

.. option:: DuplicateUsing

     Repeated names in ``using`` directive.

.. option:: EmptyAbstract

     Empty ``abstract`` blocks.

.. option:: EmptyConstructor

     Empty ``constructor`` blocks.

.. option:: EmptyField

     Empty ``field`` blocks.

.. option:: EmptyGeneralize

     Empty ``variable`` blocks.

.. option:: EmptyInstance

     Empty ``instance`` blocks.

.. option:: EmptyMacro

     Empty ``macro`` blocks.

.. option:: EmptyMutual

     Empty ``mutual`` blocks.

.. option:: EmptyPolarityPragma

     :ref:`POLARITY pragmas <polarity-pragma>` not giving any polarities.

.. option:: EmptyPostulate

     Empty ``postulate`` blocks.

.. option:: EmptyPrimitive

     Empty ``primitive`` blocks.

.. option:: EmptyPrivate

     Empty ``private`` blocks.

.. option:: EmptyRewritePragma

     Empty ``REWRITE`` pragmas.

.. option:: EmptyWhere

     Empty ``where`` blocks.

.. option:: FaceConstraintCannotBeHidden

     Face constraint patterns that are given as implicit arguments.

.. option:: FaceConstraintCannotBeNamed

     Face constraint patterns that are given as named arguments.

.. option:: FixingRelevance

     Invalid relevance annotations, automatically corrected.

.. option:: FixityInRenamingModule

     Fixity annotations in ``renaming`` directives for a ``module``.

.. option:: HiddenGeneralize

     Hidden identifiers in ``variable`` blocks.

.. option:: IllformedAsClause

     Illformed ``as``-clauses in ``import`` statements.

.. option:: InlineNoExactSplit

     Failed exact splits after inlining a constructor, see :ref:`inline-pragma`.

.. option:: InstanceNoOutputTypeName

     Instance arguments whose type does not end in a named or variable type;
     such are never considered by instance search.

.. option:: InstanceArgWithExplicitArg

     Instance arguments with explicit arguments;
     such are never considered by instance search.

.. option:: InstanceWithExplicitArg

     Instance declarations with explicit arguments;
     such are never considered by instance search.

.. option:: InteractionMetaBoundaries

     Interaction meta variables that have unsolved boundary constraints.

.. option:: InvalidCatchallPragma

     :ref:`CATCHALL<catchall-pragma>` pragmas before a non-function clause.

.. option:: InvalidCharacterLiteral

     Illegal character literals such as surrogate code points.

.. option:: InvalidConstructorBlock

     ``constructor`` blocks outside of ``interleaved mutual`` blocks.

.. option:: InvalidCoverageCheckPragma

     :ref:`NON_COVERING <non_covering-pragma>` pragmas before non-function or ``mutual`` blocks.

.. option:: InvalidNoPositivityCheckPragma

     :ref:`NO_POSITIVITY_CHECK <no_positivity_check-pragma>` pragmas before something
     that is neither a ``data`` nor ``record`` declaration nor a ``mutual`` block.

.. option:: InvalidNoUniverseCheckPragma

     :ref:`NO_UNIVERSE_CHECK <no_universe_check-pragma>` pragmas before declarations other than ``data`` or ``record`` declarations.

.. option:: InvalidTerminationCheckPragma

     :ref:`Termination checking pragmas <terminating-pragma>` before non-function or ``mutual`` blocks.

.. option:: InversionDepthReached

     Inversions of pattern-matching failed due to exhausted inversion depth.

.. option:: LibUnknownField

     Unknown fields in library files.

.. option:: MissingTypeSignatureForOpaque

     ``abstract`` or ``opaque`` definitions that lack a type signature.

.. option:: ModuleDoesntExport

     Names mentioned in an import statement which are not exported by
     the module in question.

.. option:: MultipleAttributes

     Multiple attributes given where only erasure is accepted.

.. option:: NoGuardednessFlag

     Coinductive record but no :option:`--guardedness` flag.

.. option:: NoMain

     Invoking the compiler on a module without a ``main`` function.
     See also :option:`--no-main`.

.. option:: NotAffectedByOpaque

     Declarations that should not be inside ``opaque`` blocks.

.. option:: NotARewriteRule

     ``REWRITE`` pragmas referring to identifiers that are neither definitions nor constructors.

.. option:: NotInScope

     Out of scope names.

.. option:: OldBuiltin

     Deprecated :ref:`BUILTIN<built-ins>` pragmas.

.. option:: OpenPublicAbstract

     ``open public`` directives in ``abstract`` blocks.

.. option:: OpenPublicPrivate

     ``open public`` directives in ``private`` blocks.

.. option:: OptionRenamed

     Renamed options.

.. option:: PatternShadowsConstructor

     Pattern variables that shadow constructors.

.. option:: PlentyInHardCompileTimeMode

     Use of attributes ``@ω`` or ``@plenty`` in hard compile-time mode.

.. option:: PolarityPragmasButNotPostulates

     Polarity pragmas for non-postulates.

.. option:: PragmaCompileErased

     :ref:`COMPILE<foreign-function-interface>` pragma targeting an erased symbol.

.. option:: PragmaCompileList

     :ref:`COMPILE<foreign-function-interface>` pragma for GHC backend targeting lists.

.. option:: PragmaCompileMaybe

     :ref:`COMPILE<foreign-function-interface>` pragma for GHC backend targeting ``MAYBE``.

.. option:: PragmaCompileUnparsable

     Unparsable :ref:`COMPILE<foreign-function-interface>` GHC pragmas.

.. option:: PragmaCompileWrong

     Ill-formed :ref:`COMPILE<foreign-function-interface>` GHC pragmas.

.. option:: PragmaCompileWrongName

     :ref:`COMPILE<foreign-function-interface>` pragmas referring to identifiers that are neither definitions nor constructors.

.. option:: PragmaExpectsDefinedSymbol

     Pragmas referring to identifiers that are not defined symbols.

.. option:: PragmaExpectsUnambiguousConstructorOrFunction

     Pragmas referring to identifiers that are not unambiguous constructors or functions.

.. option:: PragmaExpectsUnambiguousProjectionOrFunction

     Pragmas referring to identifiers that are not unambiguous projections or functions.

.. option:: PragmaNoTerminationCheck

     :ref:`NO_TERMINATION_CHECK<terminating-pragma>` pragmas; such are deprecated.

.. option:: InvalidDisplayForm

     An illegal :ref:`DISPLAY <display-pragma>` form; it will be ignored.

.. option:: RewriteLHSNotDefinitionOrConstructor

     Rewrite rule head symbol is not a defined symbol or constructor.

.. option:: RewriteVariablesNotBoundByLHS

     Rewrite rule does not bind all of its variables.

.. option:: RewriteVariablesBoundMoreThanOnce

     Constructor-headed rewrite rule has non-linear parameters.

.. option:: RewriteLHSReduces

     Rewrite rule LHS is not in weak-head normal form.

.. option:: RewriteHeadSymbolIsProjectionLikeFunction

     Rewrite rule head symbol is a projection-like function.

.. option:: RewriteHeadSymbolIsTypeConstructor

     Rewrite rule head symbol is a type constructor.

.. option:: RewriteHeadSymbolContainsMetas

     Definition of rewrite rule head symbol contains unsolved metas.

.. option:: RewriteConstructorParametersNotGeneral

     Constructor-headed rewrite rule parameters are not fully general.

.. option:: RewriteContainsUnsolvedMetaVariables

     Rewrite rule contains unsolved metas.

.. option:: RewriteBlockedOnProblems

     Checking rewrite rule blocked by unsolved constraint.

.. option:: RewriteRequiresDefinitions

     Checking rewrite rule blocked by missing definition.

.. option:: RewriteDoesNotTargetRewriteRelation

     Rewrite rule does not target the rewrite relation.

.. option:: RewriteBeforeFunctionDefinition

     Rewrite rule is not yet defined.

.. option:: RewriteBeforeMutualFunctionDefinition

     Mutually declaration with the rewrite rule is not yet defined.

.. option:: ShadowingInTelescope

     Repeated variable name in telescope.

.. option:: TooManyArgumentsToSort

     E.g. `Set` used with more than one argument.

.. option:: TooManyFields

     Record expression with invalid field names.

.. option:: UnfoldingWrongName

     Names in an ``unfolding`` clause that are not unambiguous definitions.

.. option:: UnfoldTransparentName

     Non-``opaque`` names mentioned in an ``unfolding`` clause.

.. option:: UnknownFixityInMixfixDecl

     Mixfix names without an associated fixity declaration.

.. option:: UnknownNamesInFixityDecl

     Names not declared in the same scope as their syntax or fixity
     declaration.

.. option:: UnknownNamesInPolarityPragmas

     Names not declared in the same scope as their polarity pragmas.

.. option:: UnreachableClauses

     Unreachable function clauses.

.. option:: UnsupportedAttribute

     Unsupported attributes.

.. option:: UnsupportedIndexedMatch

     Failures to compute full equivalence when splitting on indexed family.

.. option:: UnusedVariablesInDisplayForm

     :ref:`DISPLAY <display-pragma>` forms that bind variables they do not use.

.. option:: UselessAbstract

     ``abstract`` blocks where they have no effect.

.. option:: UselessHiding

     Names in ``hiding`` directive that are anyway not imported.

.. option:: UselessInline

     :ref:`INLINE<inline-pragma>` pragmas where they have no effect.

.. option:: UselessInstance

     ``instance`` blocks where they have no effect.

.. option:: UselessMacro

     ``macro`` blocks where they have no effect.

.. option:: UselessOpaque

     ``opaque`` blocks that have no effect.

.. option:: UselessPatternDeclarationForRecord

     ``pattern`` directives where they have no effect.

.. option:: UselessPragma

     Pragmas that get ignored.

.. option:: UselessPrivate

     ``private`` blocks where they have no effect.

.. option:: UselessPublic

     ``public`` directives where they have no effect.

.. option:: UserWarning

     User-defined warnings added using one of the ``WARNING_ON_*`` pragmas.

.. option:: WarningProblem

     Problem encountered with option :option:`-W`,
     like an unknown warning or the attempt to switch off a non-benign warning.

.. option:: WithClauseProjectionFixityMismatch

     Projection fixity different in with-clause compared to its parent clause.

.. option:: WithoutKFlagPrimEraseEquality

     ``primEraseEquality`` used with the without-K flags.

.. option:: WrongInstanceDeclaration

     Terms marked as eligible for instance search whose type does not end with a name.

.. option:: CustomBackendWarning

     Warnings from custom backends.

Error warnings
~~~~~~~~~~~~~~

Some warnings are fatal; those are errors Agda first ignores but eventually raises.
Such *error warnings* are always on, they cannot be toggled by :option:`-W`.

.. option:: CoinductiveEtaRecord

     Declaring a ``record`` type as both ``coinductive`` and having ``eta-equality``.

.. option:: CoInfectiveImport

     Importing a file not using e.g. :option:`--safe` from one which does.

.. option:: ConstructorDoesNotFitInData

     Constructor with arguments in a universe higher than the one of its data type.

.. option:: CoverageIssue

     Failed coverage checks.

.. option:: InfectiveImport

     Importing a file using e.g. :option:`--cubical` into one which does not.

.. option:: MissingDataDeclaration

     Constructor definitions not associated to a data declaration.

.. option:: MissingDefinitions

     Names declared without an accompanying definition.

.. option:: NotAllowedInMutual

     Declarations that are not allowed in a mutual block.

.. option:: NotStrictlyPositive

     Failed strict positivity checks.

.. option:: OverlappingTokensWarning

     Multi-line comments spanning one or more literate text blocks.

.. option:: PragmaCompiled

     :ref:`COMPILE<foreign-function-interface>` pragmas not allowed in safe mode.

.. option:: RewriteAmbiguousRules

     Failed global confluence checks because of overlapping rules.

.. option:: RewriteMaybeNonConfluent

     Failed confluence checks while computing overlap.

.. option:: RewriteMissingRule

     Failed global confluence checks because of missing rules.

.. option:: RewriteNonConfluent

     Failed confluence checks while joining critical pairs.

.. option:: SafeFlagEta

     :ref:`ETA <eta-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagInjective

     :ref:`INJECTIVE <injective-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagNoCoverageCheck

     :ref:`NON_COVERING <non_covering-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagNonTerminating

     :ref:`NON_TERMINATING <non_terminating-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagNoPositivityCheck

     :ref:`NO_POSITIVITY_CHECK <no_positivity_check-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagNoUniverseCheck

     :ref:`NO_UNIVERSE_CHECK <no_universe_check-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagPolarity

     :ref:`POLARITY <polarity-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagPostulate

     ``postulate`` blocks with the :option:`--safe` flag.

.. option:: SafeFlagPragma

     Unsafe :ref:`OPTIONS <options-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagTerminating

     :ref:`TERMINATING <terminating-pragma>` pragmas with the :option:`--safe` flag.

.. option:: SafeFlagWithoutKFlagPrimEraseEquality

     ``primEraseEquality`` used with the :option:`--safe` and :option:`--without-K` flags.

.. option:: TerminationIssue

     Failed termination checks.

.. option:: UnsolvedConstraints

     Unsolved constraints.

.. option:: UnsolvedInteractionMetas

     Unsolved interaction meta variables.

.. option:: UnsolvedMetaVariables

     Unsolved meta variables.

.. option:: HiddenNotInArgumentPosition

     Hidden arguments ``{ x }`` can only appear as arguments to
     functions, not as expressions by themselves.

.. option:: InstanceNotInArgumentPosition

     Instance arguments ``⦃ x ⦄`` can only appear as arguments to
     functions, not as expressions by themselves.


Command-line examples
---------------------

Run Agda with all warnings enabled, except for warnings about empty ``abstract`` blocks:

.. code-block:: console

   agda -W all --warning=noEmptyAbstract file.agda

Run Agda on a file which uses the standard library.
Note that you must have already created a ``libraries`` file
as described in :ref:`package-system`.

.. code-block:: console

   agda -l standard-library -i. file.agda

(Or if you have added ``standard-library`` to your ``defaults`` file, simply ``agda file.agda``.)


.. _consistency-checking-options:

Checking options for consistency
--------------------------------

Agda checks that options used in imported modules are consistent with
each other.

An *infective* option is an option that if used in one module, must be
used in all modules that depend on this module. The following options
are infective:

* :option:`--cohesion`
* :option:`--erased-matches`
* :option:`--erasure`
* :option:`--flat-split`
* :option:`--guarded`
* :option:`--polarity`
* :option:`--prop`
* :option:`--rewriting`
* :option:`--two-level`

Furthermore :option:`--cubical` and :option:`--erased-cubical` are
*jointly infective*: if one of them is used in one module, then one or
the other must be used in all modules that depend on this module.

A *coinfective* option is an option that if used in one module, must
be used in all modules that this module depends on. The following
options are coinfective:

* :option:`--safe`
* :option:`--without-K`
* :option:`--no-universe-polymorphism`
* :option:`--no-sized-types`
* :option:`--no-guardedness`
* :option:`--level-universe`

Furthermore the option :option:`--cubical-compatible` is mostly
coinfective. If a module uses :option:`--cubical-compatible` then all
modules that this module imports (directly) must also use
:option:`--cubical-compatible`, with the following exception: if a
module uses both :option:`--cubical-compatible` and
:option:`--with-K`, then it is not required to use
:option:`--cubical-compatible` in (directly) imported modules that use
:option:`--with-K`. (Note that one cannot use
:option:`--cubical-compatible` and :option:`--with-K` at the same time
if :option:`--safe` is used.)

Agda records the options used when generating an interface file. If
any of the following options differ when trying to load the interface
again, the source file is re-typechecked instead:

* :option:`--allow-exec`
* :option:`--allow-incomplete-matches`
* :option:`--allow-unsolved-metas`
* :option:`--call-by-name`
* :option:`--cohesion`
* :option:`--confluence-check`
* :option:`--copatterns`
* :option:`--cubical-compatible`
* :option:`--cubical`
* :option:`--cumulativity`
* :option:`--double-check`
* :option:`--erase-record-parameters`
* :option:`--erased-cubical`
* :option:`--erased-matches`
* :option:`--erasure`
* :option:`--exact-split`
* :option:`--experimental-irrelevance`
* :option:`--flat-split`
* :option:`--guarded`
* :option:`--hidden-argument-puns`
* :option:`--infer-absurd-clauses`
* :option:`--injective-type-constructors`
* :option:`--instance-search-depth`
* :option:`--inversion-max-depth`
* :option:`--irrelevant-projections`
* :option:`--keep-covering-clauses`
* :option:`--local-confluence-check`
* :option:`--lossy-unification`
* :option:`--no-auto-inline`
* :option:`--no-eta-equality`
* :option:`--no-fast-reduce`
* :option:`--no-forcing`
* :option:`--no-guardedness`
* :option:`--no-import-sorts`
* :option:`--no-load-primitives`
* :option:`--no-pattern-matching`
* :option:`--no-positivity-check`
* :option:`--no-projection-like`
* :option:`--no-sized-types`
* :option:`--no-termination-check`
* :option:`--no-unicode`
* :option:`--no-universe-polymorphism`
* :option:`--omega-in-omega`
* :option:`--backtracking-instance-search`
* :option:`--polarity`
* :option:`--prop`
* :option:`--qualified-instances`
* :option:`--rewriting`
* :option:`--safe`
* :option:`--save-metas`
* :option:`--syntactic-equality`
* :option:`--termination-depth`
* :option:`--two-level`
* :option:`--type-in-type`
* :option:`--warning`
* :option:`--without-K`


.. _Vim: https://www.vim.org/
.. _Dot: http://www.graphviz.org/content/dot-language
