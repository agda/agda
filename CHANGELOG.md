Release notes for Agda version 2.9.0
====================================

Installation
------------

* Dropped support for GHC 8.8, 8.10, and 9.0.

* Agda supports GHC versions 9.2.8 to 9.12.2.

Pragmas and options
-------------------

* New option `--print-options` to print a simple list of all options.
  This list can e.g. be used to implement bash completion.

* The flavor of Cubical Agda can now be chosen by an argument to the `--cubical` option:

  | Old                    | New                                               |
  | ---------------------- | ------------------------------------------------- |
  | `--cubical`            | `--cubical`, or `--cubical=full`                  |
  | `--erased-cubical`     | `--erased-cubical`, or `--cubical=erased`         |
  | `--cubical-compatible` | `--cubical-compatible`, or `--cubical=compatible` |
  | -                      | `--cubical=no-glue`                               |

  For compatibility between modules using different variants of Cubical Agda, see
  [the documentation](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).

* New flag `--no-write-interfaces`.

* New command-line option `--literate-markdown-only-agda-blocks` (off by default).
  When enabled, only code blocks explicitly marked with ` ```agda ` are treated as
  Agda code in literate Markdown (`.lagda.md`) and Typst (`.lagda.typ`) files.
  Unmarked code blocks (` ``` `) are treated as verbatim text and not type-checked.
  This option must be set via command line since it affects parsing.
  (See [#7971](https://github.com/agda/agda/issues/7971).)

* The flag `--termination-depth=N` now means _maximum_ termination depth and
  the termination checker now performs iterative deepening,
  starting with depth `1` and increasing it up to the given `N`, stopping early
  as soon as the termination check succeeds.
  Increasing `N` can thus slow down things only for failing termination checks.

  The default value of `N` has been increased from `1` to `3`, yet not higher,
  because cases requiring a termination depth `> 1` are already very rare in practice.

  There is also an internal change to the termination checker.
  Dot patterns are now taken into account from the beginning and not only when
  the termination check fails without taking them into account.
  The overhead to also mine dot patterns for structural descent was already
  negligible so it made sense to simplify the termination checking algorithm.

* The new flag `--no-occurrence-analysis` can be used to turn off the
  automated occurrence analysis for functions.

  By default Agda analyses how functions use their arguments. For
  instance, Agda can tell that `D` in the following code is strictly
  positive, because `Vec` uses its `Set` argument in a strictly
  positive way:
  ```agda
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  Vec : Set → Nat → Set
  Vec A zero    = ⊤
  Vec A (suc n) = A × Vec A n

  data D : Set where
    c : ∀ n → Vec D n → D
  ```
  However, this analysis can be slow, especially for big mutual
  blocks. Now it is possible to turn it off.

  The analysis is also used to detect unused function arguments. The
  following code is by default accepted, but it is rejected if the
  occurrence analysis is turned off:
  ```agda
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Unit

  F : Bool → Set → Set
  F true  _ = Bool
  F false _ = ⊤

  _ : {b : Bool} → F b Bool ≡ F b ⊤
  _ = refl
  ```

  Note that an alternative to the analysis is to use polarities. The
  following code is accepted:
  ```agda
  {-# OPTIONS --polarity --no-occurrence-analysis #-}

  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit

  data _×_ (@++ A B : Set) : Set where
    _,_ : A → B → A × B

  Vec : @++ Set → Nat → Set
  Vec A zero    = ⊤
  Vec A (suc n) = A × Vec A n

  data D : Set where
    c : ∀ n → Vec D n → D

  F : Bool → @unused Set → Set
  F true  _ = Bool
  F false _ = ⊤

  _ : {b : Bool} → F b Bool ≡ F b ⊤
  _ = refl
  ```

* Setting environment variable `NO_COLOR` now turns off coloring in the default `--color=auto` mode.
  It can be overwritten by `--color=always`.
  See also https://no-color.org/ .

Errors
------

* Error `ClashingDefinition` now gives the lineage of the previous definition of the same name.
  This helps when it is unclear how this name was imported.  Example:
  ```
    error: [ClashingDefinition]
    Multiple definitions of A. Previous definition
    A is in scope as
      * a postulate Imports.A.A brought into scope by
        - the opening of Imports.A at ...
        - its definition at ...
  ```

* Errors `GenericError` and `GenericDocError` have been replaced by more specific errors.
  (Issue [#7225](https://github.com/agda/agda/issues/7225).)

* Generalisation failures due to unresolvable dependencies between a
  generalized variable and unsolved metavariables have new, specific
  errors.
  * `GeneralizationPrepruneErrorRefinedContext`, reproduced by Amélia Liao
    (see Issue [#8161](https://github.com/agda/agda/issues/8161#issuecomment-3696949816)).
  * `GeneralizationPrepruneErrorCyclicDependencies`, reproduced by Nils Anders Danielsson
    (see Issue [#3672](https://github.com/agda/agda/issues/3672#issuecomment-482715807)).

Warnings
--------

* New warning `UnusedImports` when `open` brings identifiers into scope
  that are definitely not used subsequently.

  If `using` or `renaming` directives are given, or in flavor `-WUnusedImports=all`,
  Agda warns about each name that is unused.
  If no directive or only a `hiding` directive is given,
  and unless the flavor is `all`,
  Agda only warns if none of the imported names are used.

  Agda also warns about instances brought into scope
  unless `--no-qualified-instances` is on
  (which requires bringing instances into scope if they should be found by instance search).

* `UselessImport` warning instead of parse error when an module is instantiated
  but not opened during `import`, for instance:
  ```agda
  import Structures.IsMonoid Carrier Eq
  ```
  This does not bring module `Structures.IsMonoid` into scope and
  neither any of its exports.
  It either needs an `open` or an `as`-clause such as `as MyMonoid`.

* `UselessPragma` warning instead of hard error `NeedOptionRewriting` when a
  `REWRITE` or `BUILTIN REWRITE` pragma is encountered but `--rewriting` is off.

* Error warning `IllegalDeclarationInDataDefinition` instead of hard error
  when `data` definition contains declarations other than type signatures of
  constructors.

* New warning `DivergentModalityInClause` when modality of a clause diverges
  from that of the function.  Example:
  ```agda
  A : Set₁
  @0 A = Set
  ```

* New warning `InvalidDataOrRecDefParameter` for information (e.g. type, attributes)
  attached to parameters in a `data` or `record` definition (that is separate of its
  data or record signature).
  This replaces errors:
  - `UnexpectedModalityAnnotationInParameter`
  - `UnexpectedTypeSignatureForParameter`

* New warning `InvalidTacticAttribute` for misplaced `@(tactic ...)` attributes.
  This was silently accepted up to Agda 2.8.0 but raises now the new warning:
  ```agda
  postulate
    @(tactic not-in-scope) _ : Set
  ```

Syntax
------

Changes to the Agda syntax.

* **Breaking:** The parser will reject ASCII opening delimiters which
  are closed by a Unicode delimiter, and vice-versa. Concretely, this
  means the mismatched pairs `⦃ ... }}`/`{{ ...  ⦄` and
  `⦇ … |)`/`(| … ⦈` are now parse errors.


* Records can now be created using module-like syntax in place of curly braces
  and semicolons.

  ```agda
  p : Pair Nat Nat
  p = record where
    fst = 2
    snd = 3
  ```

  See [#4275](https://github.com/agda/agda/issues/4275) for the proposal.

* Modality annotations in aliases and let-bindings are now supported
  (PR [#7990](https://github.com/agda/agda/pull/7990)).
  Example:
  ```agda
    split : {A B C : Set} (@0 p : A × B) (k : @0 A → @0 B → C) → C
    split p k = let @0 (x , y) = q in k x y
      where
      @0 q = p
  ```

* Postfix projections cannot be surrounded by parentheses anymore.
  E.g. these postfix projection applications are now illegal in expressions:
  ```agda
    r (.proj)
    r .(proj)
  ```

* Idiom brackets and `do` notation may now appear *qualified*, as in
  `M.do` or `M.(| f x y z |)`, in which case the functions needed for
  desugaring these are looked up in `M` rather than in the surrounding
  scope.

Language
--------

Changes to type checker and other components defining the Agda language.

* Added support for [Cubical Agda without Glue Types](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#cubical-agda-without-glue)
  by using the flag `--cubical=no-glue`,
  a variant of Cubical Agda which disables the Glue types.
  For compatibility with modules using `--cubical[=full]` and `--cubical=erased`, see
  [variants](https://agda.readthedocs.io/en/v2.9.0/language/cubical.html#variants).

* (**BREAKING**): In the presence of `--erasure`, types of lambdas expressions
  are not inferred unless every lambda-bound variable has been given its erasure
  status (`@0` or `@ω`) explicitely.
  The reason is that otherwise Agda might infer the wrong erasure status, see, e.g.,
  [Issue #7001](https://github.com/agda/agda/issues/7001).

  Now we have the following behavior:
  ```agda
    fails    = λ x → x + x
    succeeds = λ (@ω x) → x + x
    alsoOK   = λ (@ω A : Set) (@0 B : Set) → A
  ```
  With that change `--erasure` gets more akin to Cubical Agda that categorically
  refuses to infer lambdas (since they could construct either functions or paths).

* Functions defined using with-abstraction equality (`with … in eq`) can now be
  reasoned about using the same with-abstraction equality: the equality proof
  is correctly generalised over. This should make most (if not all) uses of the
  old-style `inspect` idioms for the built-in equality type unnecessary.


Reflection
----------

* `tcTypeError` now throws `UserError` instead of `GenericDocError`.

Library management
------------------

* Suppport for version-specific `defaults` files: a file whose name is
of the form `defaults-X.Y.Z` will take precedence over the standard
`defaults` one for the `X.Y.Z` version of the compiler. This can be
used to have default libraries that are only compatible with a given
version of the compiler.

Interaction and emacs mode
--------------------------

* Syntax highlighting and go-to-definition now also works in the Agda
  information buffer in Emacs where goals etc. are displayed.
  This fixes long-standing [Issue #706](https://github.com/agda/agda/issues/706).

* By temporarily turning on printing of hidden arguments
  (`OPTION --show-implicit`, `C-c C-x C-h` in Emacs)
  and then splitting on result in a hole
  (`C-c C-c RET` in Emacs, the whole sequence being `C-c C-x C-h C-c C-c RET`),
  hidden arguments can be introduced in the left hand side of a clause.
  In the presence of generalized variables, this used to introduce unparsable names.
  For instance:
  ```agda
    variable
      l : Level
      A : Set l

    id : A → A
    id = {!!}
  ```
  Here, `id {A.l} {A} x = ?` was produced, triggering an error.
  Now, the correct `id {A = A} x = ?` is produced
  (Issue [#8153](https://github.com/agda/agda/issue/8153)).

* Catch-all copattern clauses are now tolerated as unreachable clauses
  rather than being outright rejected with a `CosplitCatchall` error.
  They can be used as jumpboard for further result splitting.
  (A scenario is a record type that got extended with new fields,
  and definitions producing record values need to be extended as well.)
  Example:
  ```agda
    test : Σ A B
    test .fst = a
    test = {!!}  -- C-c C-c RET
  ```
  This split produces the clause `test .snd = ?`.
  (Issue [#8139](https://github.com/agda/agda/issue/8139)).


* A normalization level can now also passed to command `Cmd_constraints`
  ("show constraints", `C-c C-=` in Emacs).
  In Emacs, the normalization level is given as usual by `C-u` prefixes.

  This interface change is **breaking** for frontends to `agda --interaction`
  such as the VSCode `agda-mode`, which need updating.

* Fixed an internal error in `Cmd_helper_function` (`C-c C-h` in Emacs)
  (Issue [#8103](https://github.com/agda/agda/issue/8103)).
  Changed the type of `Goal_HelperFunction` which might be **breaking**
  3rd-party interaction frontends.

* `NON_TERMINATING` functions now only reduce in `IgnoreAbstract` mode of
  commands `Cmd_compute(_toplevel)` (`C-u C-c C-n` in Emacs)
  regardless of whether invoked at toplevel or in a hole
  (Issue [#2410](https://github.com/agda/agda/issue/2410)).

Backends
--------

* New option `--ghc-trace` for GHC Backend to instrument code
  such that the Agda name of the function is printed to `stderr`
  whenever a function is entered.

Issues closed
-------------

For 2.9.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.9.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

### Issues closed for milestone 2.9.0

### PRs closed for milestone 2.9.0
