Release notes for Agda version 2.6.1
====================================

General
-------

* Agda now has an official logo: ![The official Agda
  logo](doc/user-manual/agda.svg)
  (https://github.com/agda/agda/blob/master/doc/user-manual/agda.svg). The
  logo was chosen by the Agda community from a list of candidates. The winning design was submitted by Miëtek Bak. The list of candidates and the outcome of the poll can be consulted [here](https://civs.cs.cornell.edu/cgi-bin/results.pl?id=E_ce6fe5e2a518ac98).

Installation and infrastructure
-------------------------------

* Added support for GHC 8.8.1
  [Issue [#3725](https://github.com/agda/agda/issues/3725)].

* Removed support for GHC 7.10.3.

* Interface files are now written in directory `_build/VERSION/agda/` at
  the project root (the closest enclosing directory where an `.agda-lib`
  file is present). If there is no project root then the interface file
  is written alongside the module it corresponds to.
  The flag `--local-interfaces` forces Agda to revert back to storing
  interface files alongside module files no matter what.

* Agda now uses the default RTS options `-H3.5G -M3.5G -A128M`.  If
  you run Agda on a 32-bit system or a system with less than 8GB of
  RAM, it is recommended to set the RTS options explicitly to a lower
  value by running `agda` with option `+RTS -H0.6G -M1.2G -A64M -RTS`
  (for example) or by setting the GHCRTS enviroment variable. See the
  [GHC User's Guide](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/runtime_control.html#setting-rts-options)
  for more information.

* The `CHANGELOG.md` was split. Changes to previous versions of Agda
  are in the directory `doc/release-notes`.

Pragmas and options
-------------------

* New pragma `WARNING_ON_IMPORT` to let module authors raise a warning
  when a module is imported. This can be use to tell users deprecations.

* New option `--confluence-check` (off by default) enables confluence
  checking of user-defined rewrite rules (this only has an effect when
  `--rewriting` is also enabled).

* New option `--no-projection-like` to turn off the analysis whether a
  type signature likens that of a projection.
  Projection-likeness is an optimization that reduces the size of
  terms by dropping parameter-like reconstructible function arguments.
  Thus, it is advisable to leave this optimization on, the flag is
  meant for debugging Agda.

* Option `--no-forcing` is now a pragma option, i.e., the forcing analysis
  can be switched off on a per-file basis via

  ```agda
  {-# OPTIONS --no-forcing #-}
  ```

  at the beginning of the file
  [Issue [#3872](https://github.com/agda/agda/issues/3872)].

* New pragma option `--no-flat-split` disables pattern matching on `@♭` arguments.

* New pragma option `--allow-incomplete-matches`. It is similar to
  `--allow-unsolved-metas`: modules containing partial function definitions
  can be imported. Its local equivalent is the `NON_COVERING` pragma to
  be placed before the function (or the block of mutually defined functions)
  which the user knows to be partial.

* Option `--interaction-json` now brings more information about goals,
  unsolved metas, warnings, errors.
  It also displays pretty-printed terms.

* New pragma option `--keep-pattern-variables` to prevent case
  splitting from replacing variables with dot patterns.

Language
--------

### Syntax

* Fractional precedence levels are now supported, see
  Issue [#3991](https://github.com/agda/agda/issues/3991). Example:

  ```agda
  infix 3.14 _<_
  ```
  Note that this includes a respective change in the reflected Agda syntax.

* Fixities can now be changed during import in a `renaming` directive,
  see
  Issue [#1346](https://github.com/agda/agda/issues/1346). Example:

  ```agda
  open M using (_∙_)
  open M renaming (_∙_ to infixl 10 _*_)
  ```
  After this, `_∙_` is in scope with its original fixity, and as `_*_` as left
  associative operator of precedence 10.

* Implicit non-dependent function spaces `{A} → B` and `{{A}} → B` are now supported.

* Idiom brackets

  Idiom brackets can accommodate none or multiple applications separated by a vertical bar `|`
  if there are two additional operations
  ```agda
  empty : ∀ {A} → F A
  _<|>_ : ∀ {A} → F A → F A → F A
  ```
  i.e. an Alternative type class in Haskell.
  As usual, the new idiom brackets desugar before scope checking.

  Idiom brackets with multiple applications
  ```agda
  (| e₁ a₁ .. aₙ | e₂ a₁ .. aₘ | .. | eₖ a₁ .. aₗ |)
  ```
  expand to (assuming right associative `_<|>_`)
  ```agda
  (pure e₁ <*> a₁ <*> .. <*> aₙ) <|> ((pure e₂ <*> a₁ <*> .. <*> aₘ) <|> (pure eₖ <*> a₁ <*> .. <*> aₗ))
  ```
  Idiom brackets with no application `(|)` or `⦇⦈` are equivalent to `empty`.


* Irrefutable With

  Users can now match on irrefutable patterns on the LHS using a
  pattern-matching `with`. An expression of the form:

  ```agda
  f xs with p1 <- e1 | ... | pn <- en
       with q1 <- f1 | ... | qm <- fm = rhs
  ```

  is translated to nested `with` clauses, essentially equivalent to:

  ```agda
  f xs with e1 | ... | en
  ... | p1 | ... | pn
       with f1 | ... | fm
  ... | q1 | ... | qm = rhs
  ```

* Record patterns in telescopes

  Users can now use record patterns in telescope and lambda abstractions.
  The type of the second projection from a dependent pair is the prototypical
  example It can be defined as follows:

  ```agda
  snd : ((a , _) : Σ A B) → B a
  ```

  And this second projection can be implemented with a lamba-abstraction using
  one of these irrefutable patterns:

  ```agda
  snd = λ (a , b) → b
  ```

  Using an as-pattern, users can get a name for the value as well as for its
  subparts. We can for instance prove that any pair is equal to the pairing
  of its first and second projections:

  ```agda
  eta : (p@(a , b) : Σ A B) → p ≡ (a , b)
  eta p = refl
  ```

* Absurd match in a do block
  The last expression in a do block can now also be an absurd match `() <- f`.

* Named `where` modules are now in scope in the rhs of the clause (see
  Issue [#4050](https://github.com/agda/agda/issues/4050)).  Example:

  ```agda
  record Wrap : Set₂ where
    field wrapped : Set₁

  test : Wrap
  test = record { M }
    module M where
      wrapped : Set₁
      wrapped = Set
  ```

* `{{-` is now lexed as `{ {-` rather than `{{ -`,
  see Issue [#3962](https://github.com/agda/agda/issues/3962).

* Syntax for large numbers: you can now separate groups of 3 digits using `_`.
  e.g. write `1_000_000` instead of `1000000`.

* `quoteGoal` and `quoteContext` are no longer keywords.

* Record constructors can no longer be qualified by the record module.
  (See Issue [#4189](https://github.com/agda/agda/issues/4189).)

  ```agda
  record Foo : Set where
    constructor foo

  works = foo
  fails = Foo.foo
  ```

* `codata` definitions have been removed from the concrete syntax
  Previously they got accepted syntactically, but resulted in errors.

* Imports can now be anonymous.
  (See Issue_[#3727](https://github.com/agda/agda/issues/3727).)
  For example, the following will **not** bring `Agda.Builtin.Unit` into scope:
  ```agda
  open import Agda.Builtin.Unit as _
  blah :: ⊤
  blah = tt
  ```

### Modalities

* New Flat Modality

  New modality `@♭/@flat` (previously only available in the branch "flat").
  An idempotent comonadic modality modeled after spatial/crisp type theory.
  See "Flat Modality" in the documentation for more.

### Universe levels

* New (experimental) option `--cumulativity`

  When the ``--cumulativity`` flag is enabled, Agda uses the subtyping
  rule ``Set i =< Set j`` whenever ``i =< j``. For example, in
  addition to its usual type ``Set``, ``Nat`` also has the type
  ``Set₁`` and even ``Set i`` for any ``i : Level``. More information
  about this new option can be found in the [user
  manual](https://agda.readthedocs.io/en/latest/language/cumulativity.html).

### Termination checking

* The "with inlining" feature of the termination checker has been
  removed. As a consequence, some functions defined using `with` are
  no longer accepted as terminating. See
  Issue [#59](https://github.com/agda/agda/issues/59) for why this
  feature was originally introduced and
  [#3604](https://github.com/agda/agda/issues/3604) for why it had to
  be removed.

### Irrelevance and Prop

* Agda will no longer reduce irrelevant definitions and definitions
  with a type in `Prop`. This does not have an effect on the
  semantics, but should lead to improved performance (see Issues
  [#4115](https://github.com/agda/agda/issues/4115),
  [#4118](https://github.com/agda/agda/issues/4118),
  [#4120](https://github.com/agda/agda/issues/4120),
  [#4122](https://github.com/agda/agda/issues/4122)).

* Terms of a type in `Prop` are now printed as `_`. To show the actual
  term, you can use the `--show-irrelevant` flag (see
  Issue [#3337](https://github.com/agda/agda/issues/3337).

### Rewrite rules

* Rewrite rules (option `--rewriting`) with data or record types as
  the head symbol are no longer allowed (see
  Issue [#3846](https://github.com/agda/agda/issues/3846)).

### Tactics & Reflection

* Implicit arguments solved by user-defined tactics

  You can declare tactics to be used to solve a particular implicit argument
  using the following syntax:

  ```agda
  example : {@(tactic f) x : A} → B
  ```

  where `f : Term → TC ⊤`. At calls to `example`, `f` is called on the
  metavariable inserted for `x`. `f` can be an arbitrary term and may depend on
  previous arguments to the function. For instance,

  ```agda
  example₂ : (depth : Nat) {@(tactic search depth) x : A} → B
  ```

  Record fields can also be annotated with a tactic, allowing them to be
  omitted in constructor applications, record constructions and co-pattern
  matches:

  ```agda
  record Example : Set where
    constructor mkExample
    field x : A
          @(tactic solveP x) {y} : P x
  ```

  where `solveP : (x : A) → Term → TC ⊤` is a tactic that tries to
  prove `P x`
  [Issue [#4124](https://github.com/agda/agda/issues/4124)].

* The legacy reflection framework using `quoteGoal` and `quoteContext` has been
  removed.

### Builtins

* New primitives

  ```agda
  primWord64ToNatInjective    : ∀ a b → primWord64ToNat a ≡ primWord64ToNat b → a ≡ b

  primFloatToWord64           : Float → Word64
  primFloatToWord64Injective  : ∀ a b → primFloatToWord64 a ≡ primFloatToWord64 b → a ≡ b

  primMetaToNat               : Meta → Nat
  primMetaToNatInjective      : ∀ a b → primMetaToNat a ≡ primMetaToNat b → a ≡ b

  primQNameToWord64s          : Name → Word64 × Word64
  primQNameToWord64sInjective : ∀ a b → primQNameToWord64s a ≡ primQNameToWord64s b → a ≡ b
  ```

  These can be used to define safe decidable propositional equality, see Issue [agda-stdlib#698](https://github.com/agda/agda-stdlib/issues/698).

* New Primitive for showing Natural numbers:

  ```agda
  primShowNat : Nat → String
  ```

  placed in Agda.Builtin.String.

* The builtin `IO` has been declared strictly positive in both its
  level and type argument.

### Warnings

* New warning for a variable shadowing another in a telescope. If the two
  variables are introduced in different telescopes then the warning is not
  raised.

  ```agda
  f : {a : Level} {A : Set a} (a : A) → A   -- warning raised: repeated a
  g : {a : Level} {A : Set a} → (a : A) → A -- warning not raised: two distinct telescopes
  ```

  Note that this warning is turned off by default (you can use
  `-WShadowingInTelescope` or `--warning ShadowingInTelescope` to turn
  it on, `-Wall` would also naturally work).


Emacs mode
----------

* Agda input method: new key bindings `\ G h` and `\ G H` for `η` and
  `H` (capital η)
  [Issue [#3856](https://github.com/agda/agda/issues/3856)].

* Syntax highlighting: in literate modes, the pure texts
  (other than Agda code and the code-text separators) are no longer highlighted
  (it was highlighted as comments before).
  This somehow provides more information about how Agda lexes literate files.

* Agda now also displays the values of let-bound variables in the
  context instead of just their types
  [Issue [#4199](https://github.com/agda/agda/issues/4199)].

* Agda will now try to preserve the ellipsis (`...`) during case
  splitting when possible. To manually expand the ellipsis, you may
  ask Agda to case split on the special identifier `.`.

* Agda will now also show variables named `_` in the context if they
  are instance arguments (see
  [#4307](https://github.com/agda/agda/issues/4307)). Instance
  arguments are now also marked as `(instance)` in the context. Example:

  ```agda
  f : {{_ : A}} → A
  f = ?
  ```

  Agda will now display the goal as follows:

  ```
  Goal: A
  ————————————————————————————————————————————————————————————
  _ : A   (instance)
  ```


GHC Backend
-----------

* Types which have a COMPILE GHC pragma are no longer erased
  [Issue [#3732](https://github.com/agda/agda/issues/3732)].

  ```agda
  data I : Set where
    bar : I

  {-# FOREIGN GHC data I = Bar     #-}
  {-# COMPILE GHC I = data I (Bar) #-}

  data S : Set where
    foo :  I → S

  {-# FOREIGN GHC data S = Foo I #-}
  {-# COMPILE GHC S = data S (Foo) #-}
  ```
  Previously [Issue [#2921](https://github.com/agda/agda/issues/2921)],
  the last binding was incorrect, since the argument of
  singleton type `I` was erased from the constructor `foo` during
  compilation.  The required shape of `S` was previously
  ```
  {-# FOREIGN GHC data S = Foo #-}
  ```
  i.e., constructor `Foo` had to have no arguments.

  For the sake of transparency, Haskell constructors bound to
  Agda constructors now take the same arguments.
  This is especially important if Haskell bindings are to be
  produced automatically by third party tool.

LaTeX backend
-------------

* Now the code environment complains if it is given unrecognised options.

  It is also possible to write, say, `hide=true` instead of `hide`,
  and `hide=false` means that the `hide` option should not be used.
  Furthermore the same option can be given multiple times, in which
  case later choices take precedence over earlier ones.

* The code environment has a new option, `number`.

  When the option `number` is used an equation number is generated for
  the code listing. The number is set to the right, centered
  vertically. By default the number is set in parentheses, but this
  can be changed by redefining `\AgdaFormatCodeNumber`.

  The option can optionally be given an argument: when `number=l` is
  used a label `l`, referring to the code listing, is generated. It is
  possible to use this option several times with different labels.

  The option has no effect if used together with `hide`, `inline` or
  `inline*`.

API
----
* Removed module `Agda.Utils.HashMap`. It only re-exported `Data.HashMap.Strict`
  from the package `unordered-containers`. Use `Data.HashMap.Strict` instead.

* Removed module `Agda.Utils.Char`. It used to provide functions converting a
  `Char` in base 8, 10, and 16 to the corresponding `Int`. Use `digitToInt` in
  `Data.Char` instead. The rest of module was about Unicode test which was not
  used.

* `Agda.Utils.List` no longer provides `headMaybe`.
  Use `listToMaybe` in `Data.Maybe` instead.

* `Agda.Utils.Either` no longer provides `mapEither`. Use `bimap` in
  `Data.Bifunctor` instead.

* `Agda.Utils.Map` no longer provides `unionWithM`, `insertWithKeyM`,
  `allWithKey`, `unzip`, and `unzip3`.

Other closed issues
-------------------

For 2.6.1, the following issues were also closed (see [bug
tracker](https://github.com/agda/agda/issues)):

  -  [#470](https://github.com/agda/agda/issues/470): Constraint solving in heterogenous situations
  -  [#471](https://github.com/agda/agda/issues/471): Emacs command to show goal with constraints on it
  -  [#500](https://github.com/agda/agda/issues/500): Allow creation of implicit parameters in with blocks
  -  [#543](https://github.com/agda/agda/issues/543): Irrelevant projections are inconsistent
  -  [#760](https://github.com/agda/agda/issues/760): Warning for open public in an abstract block
  -  [#1073](https://github.com/agda/agda/issues/1073): Solve C-c C-s inserts variables that are not in scope
  -  [#1097](https://github.com/agda/agda/issues/1097): Allow record patterns in lambda-bound positions
  -  [#1182](https://github.com/agda/agda/issues/1182): Request: allowing the use of patterns in syntax-bound variables
  -  [#1381](https://github.com/agda/agda/issues/1381): Termination checker rejects function with with-clause
  -  [#1445](https://github.com/agda/agda/issues/1445): Lack of subject reduction with REWRITE
  -  [#1820](https://github.com/agda/agda/issues/1820): Case splitting should preserve existing names
  -  [#2148](https://github.com/agda/agda/issues/2148): Option to use use `stack exec` for GHC backend
  -  [#2170](https://github.com/agda/agda/issues/2170): Two equal irrelevant definitions: one is type checked, the other is not
  -  [#2284](https://github.com/agda/agda/issues/2284): Disallow duplicate bound variable in lambda and pi
  -  [#2414](https://github.com/agda/agda/issues/2414): Case splitting loses as-patterns
  -  [#2498](https://github.com/agda/agda/issues/2498): Resolution of unnamed instances
  -  [#2512](https://github.com/agda/agda/issues/2512): Propose: Split the changelog
  -  [#2530](https://github.com/agda/agda/issues/2530): --ignore-interfaces should not recompile Primitive.agda
  -  [#2535](https://github.com/agda/agda/issues/2535): Expose name id in reflection API
  -  [#2589](https://github.com/agda/agda/issues/2589): Preserve the ellipsis (dots) when case splitting "with" arguments
  -  [#2610](https://github.com/agda/agda/issues/2610): Avoid rechecking by storing interfaces in separate directories?
  -  [#2902](https://github.com/agda/agda/issues/2902): Case-splitting should not generate patterns containing pattern synonyms
  -  [#3073](https://github.com/agda/agda/issues/3073): type-in-type and spurious levels
  -  [#3089](https://github.com/agda/agda/issues/3089): Nicer syntax for implicit @-patterns
  -  [#3095](https://github.com/agda/agda/issues/3095): Would like to make hidden variable visible but it is created ambiguous
  -  [#3233](https://github.com/agda/agda/issues/3233): Type declarations not accompanied by a definition should be highlighted in the emacs mode
  -  [#3238](https://github.com/agda/agda/issues/3238): Printing of inserted hidden lambdas
  -  [#3293](https://github.com/agda/agda/issues/3293): Absurd match in a do block
  -  [#3295](https://github.com/agda/agda/issues/3295): Allow import of files with incomplete pattern matching
  -  [#3353](https://github.com/agda/agda/issues/3353): Case splitting turns named arguments into positional arguments
  -  [#3383](https://github.com/agda/agda/issues/3383): Document the DISPLAY pragma
  -  [#3423](https://github.com/agda/agda/issues/3423): Implicit arguments with custom macro for resolution
  -  [#3493](https://github.com/agda/agda/issues/3493): Impossible to normalize elements in a proposition
  -  [#3525](https://github.com/agda/agda/issues/3525): Rewrite rules with non-linear patterns do not work in presence of Prop
  -  [#3545](https://github.com/agda/agda/issues/3545): JavaScript backend: mapping a function that returns Set fails
  -  [#3574](https://github.com/agda/agda/issues/3574): Support precedent rebind / changing the precedents in builtin library
  -  [#3582](https://github.com/agda/agda/issues/3582): Error message referring to Set instead of Prop
  -  [#3594](https://github.com/agda/agda/issues/3594): Occurs check throws error when a solution is possible by eta expansion
  -  [#3599](https://github.com/agda/agda/issues/3599): Bad performance on pathToEquiv
  -  [#3606](https://github.com/agda/agda/issues/3606): Do not create/display superfluous metas and show constraints in a readable way
  -  [#3654](https://github.com/agda/agda/issues/3654): Show non-blocked constraints first in list of unsolved constraints
  -  [#3695](https://github.com/agda/agda/issues/3695): Generalisation introduces multiple explicit arguments for one generalisable variable
  -  [#3698](https://github.com/agda/agda/issues/3698): Remove primComp?
  -  [#3712](https://github.com/agda/agda/issues/3712): Sigma not listed in Built-ins documentation
  -  [#3724](https://github.com/agda/agda/issues/3724): Internal error with Prop and inductive-inductive type
  -  [#3730](https://github.com/agda/agda/issues/3730): Internal error resulting from unused implicit argument
  -  [#3735](https://github.com/agda/agda/issues/3735): Incorrect context when generalisable variable is used
  -  [#3736](https://github.com/agda/agda/issues/3736): Safe decidability equality support for Name and Meta
  -  [#3745](https://github.com/agda/agda/issues/3745): Update user manual on built-ins
  -  [#3749](https://github.com/agda/agda/issues/3749): Inconsistency: Rounding op differentiates NaNs
  -  [#3759](https://github.com/agda/agda/issues/3759): Change the default RTS options?
  -  [#3774](https://github.com/agda/agda/issues/3774): de Bruijn index out of scope with rewrite rules
  -  [#3776](https://github.com/agda/agda/issues/3776): Conversion check fails too quickly when type could be eta unit type
  -  [#3779](https://github.com/agda/agda/issues/3779): Incorrectly ordered generalised variables
  -  [#3785](https://github.com/agda/agda/issues/3785): Comparison of blocked terms doesn't respect eta
  -  [#3791](https://github.com/agda/agda/issues/3791): Asking Agda to solve a constraint inside a macro
  -  [#3803](https://github.com/agda/agda/issues/3803): Parse empty field lists
  -  [#3805](https://github.com/agda/agda/issues/3805): Agda prelude: Internal error at src/full/Agda/TypeChecking/Reduce/Fast.hs:1347
  -  [#3807](https://github.com/agda/agda/issues/3807): Internal error related to generalisable variables
  -  [#3812](https://github.com/agda/agda/issues/3812): Rewriting projected symbols leads to loss of subject reduction
  -  [#3813](https://github.com/agda/agda/issues/3813): Destructuring leads to invalid premises
  -  [#3818](https://github.com/agda/agda/issues/3818): For open import M, Agda should remember that M is an external module
  -  [#3824](https://github.com/agda/agda/issues/3824): rewrite drops named where module
  -  [#3825](https://github.com/agda/agda/issues/3825): record{M} syntax reports unsolved metas in module M instead of in record expression
  -  [#3828](https://github.com/agda/agda/issues/3828): Internal error in Agda/TypeChecking/Coverage.hs:467
  -  [#3829](https://github.com/agda/agda/issues/3829): Case-split: don't generate pattern covered by unreachable clause
  -  [#3830](https://github.com/agda/agda/issues/3830): primShow(Char/String) display spurious square brackets
  -  [#3831](https://github.com/agda/agda/issues/3831): Wrong de Bruijn indices for reflected variables inside an extended context
  -  [#3843](https://github.com/agda/agda/issues/3843): Internal error with-clause and unification
  -  [#3851](https://github.com/agda/agda/issues/3851): C-c C-h should default to AsIs rather than Simplified
  -  [#3866](https://github.com/agda/agda/issues/3866): `--no-unicode` option producing unicode variable names
  -  [#3878](https://github.com/agda/agda/issues/3878): Case splitting should respect existing input
  -  [#3879](https://github.com/agda/agda/issues/3879): Only unqualified pattern synonyms should be used for resugaring
  -  [#3882](https://github.com/agda/agda/issues/3882): de Bruijn index out of scope
  -  [#3892](https://github.com/agda/agda/issues/3892): Internal error with `data .. where` definitions
  -  [#3898](https://github.com/agda/agda/issues/3898): Forcing analysis sensitive to normalization
  -  [#3900](https://github.com/agda/agda/issues/3900): Abstract constructor not usable in function definition involving "with"
  -  [#3901](https://github.com/agda/agda/issues/3901): Unnamed implicit non-dependent function space {A} -> B and {{A}} -> B
  -  [#3903](https://github.com/agda/agda/issues/3903): Forcing translation produces segfaulting program
  -  [#3912](https://github.com/agda/agda/issues/3912): Generalisable variables generate unknown and explicit parameters
  -  [#3919](https://github.com/agda/agda/issues/3919): Case splitting fails in parameterized module
  -  [#3927](https://github.com/agda/agda/issues/3927): `import … hiding …` should be documented
  -  [#3928](https://github.com/agda/agda/issues/3928): The error message `Hiding … has no effect` should be improved
  -  [#3930](https://github.com/agda/agda/issues/3930): BUILTIN NATURAL internal error at Forcing.hs:232
  -  [#3932](https://github.com/agda/agda/issues/3932): Internal error when mixing implicit and explicit mutual blocks
  -  [#3937](https://github.com/agda/agda/issues/3937): Internal error at "ConcreteToAbstract:1372"
  -  [#3940](https://github.com/agda/agda/issues/3940): Weird error with piSort and generalization
  -  [#3943](https://github.com/agda/agda/issues/3943): Print also hidden problematic unification terms
  -  [#3955](https://github.com/agda/agda/issues/3955): Document module keyword in using/hiding/renaming
  -  [#3956](https://github.com/agda/agda/issues/3956): Duplicate name in environment buffer with @-pattern
  -  [#3964](https://github.com/agda/agda/issues/3964): Agda overwrites user-written dotted pattern
  -  [#3965](https://github.com/agda/agda/issues/3965): Wrong indication of unreachable clauses
  -  [#3966](https://github.com/agda/agda/issues/3966): All clauses marked when one clause has unification error
  -  [#3972](https://github.com/agda/agda/issues/3972): Unreachable clause leads to internal error at Serialise/Instances/Internal.hs:94 (MetaV)
  -  [#3974](https://github.com/agda/agda/issues/3974): Range for unexpected implicit argument on lhs too big
  -  [#3983](https://github.com/agda/agda/issues/3983): TERMINATING accepted with --safe if hidden in a block
  -  [#4000](https://github.com/agda/agda/issues/4000): How to get Agda to ignore `~/.agda`?
  -  [#4006](https://github.com/agda/agda/issues/4006): Internal error related to abstract and variable
  -  [#4007](https://github.com/agda/agda/issues/4007): Cannot give pattern-matching lambda in abstract setting
  -  [#4010](https://github.com/agda/agda/issues/4010): unquoteDef fails in abstract block
  -  [#4012](https://github.com/agda/agda/issues/4012): Internal error when accessing abstract definitions created by unquoteDef/Decl
  -  [#4020](https://github.com/agda/agda/issues/4020): Rewriting incorrectly considers level variables under lambdas as unbound in the LHS
  -  [#4032](https://github.com/agda/agda/issues/4032): Loss of subject reduction involving --rewriting even when --confluence-check is on and everything passes the confluence checker
  -  [#4038](https://github.com/agda/agda/issues/4038): Rewriting sometimes fails to rewrite in the presence of unsolved metas
  -  [#4044](https://github.com/agda/agda/issues/4044): Equality checking uses too much memory in 2.6.0 (compared to 2.5.4)
  -  [#4046](https://github.com/agda/agda/issues/4046): Remove (deprecated) codata keyword
  -  [#4048](https://github.com/agda/agda/issues/4048): Rewriting rule fails to trigger
  -  [#4049](https://github.com/agda/agda/issues/4049): Internal error with sized types if the target type of a constructor is an alias
  -  [#4051](https://github.com/agda/agda/issues/4051): Internal error when importing a module with a hole in a type
  -  [#4053](https://github.com/agda/agda/issues/4053): Emacs-mode: Case split leaves part of old line behind
  -  [#4059](https://github.com/agda/agda/issues/4059): Two variants of irrefutable with?
  -  [#4066](https://github.com/agda/agda/issues/4066): Regression related to instance resolution
  -  [#4116](https://github.com/agda/agda/issues/4116): Internal error Forcing.hs:232
  -  [#4121](https://github.com/agda/agda/issues/4121): Pattern synonyms cannot be made private
  -  [#4124](https://github.com/agda/agda/issues/4124): Tactic modality for record fields
  -  [#4125](https://github.com/agda/agda/issues/4125): Type checker normalizes too much
  -  [#4134](https://github.com/agda/agda/issues/4134): Internal error triggered by missing check for irrelevant meta dependencies
  -  [#4136](https://github.com/agda/agda/issues/4136): Overzealous pruning of metavariable with irrelevant argument
  -  [#4141](https://github.com/agda/agda/issues/4141): Printing of DontCare should not use dot syntax
  -  [#4142](https://github.com/agda/agda/issues/4142): defCopatternLHS needs to be set when record expression were translated to copatterns
  -  [#4148](https://github.com/agda/agda/issues/4148): Internal error related to records and type-level indices
  -  [#4152](https://github.com/agda/agda/issues/4152): Variables in Prop position should not raise hard error in occurs check
  -  [#4154](https://github.com/agda/agda/issues/4154): Renaming declarations within a module may cause name clash
  -  [#4158](https://github.com/agda/agda/issues/4158): Double check failure (unaware of rewrite rule)
  -  [#4170](https://github.com/agda/agda/issues/4170): Tactic causes Agda to enter into an infinite loop
  -  [#4179](https://github.com/agda/agda/issues/4179): Coverage check false positive
  -  [#4185](https://github.com/agda/agda/issues/4185): Agda uses η-equality for record types defined with no-eta-equality
  -  [#4199](https://github.com/agda/agda/issues/4199): Show values of let-bound variables when printing the context
  -  [#4205](https://github.com/agda/agda/issues/4205): Internal error in connection with with, copatterns, and open record
  -  [#4211](https://github.com/agda/agda/issues/4211): Cannot add as-pattern on literal pattern
  -  [#4215](https://github.com/agda/agda/issues/4215): Case splitting should respect Nat literals
  -  [#4261](https://github.com/agda/agda/issues/4261): Order of arguments affects lambda pattern matching
  -  [#4283](https://github.com/agda/agda/issues/4283): DeBruijn issue(?) in standard library tests
  -  [#4297](https://github.com/agda/agda/issues/4297): Missing documentation: NO_UNIVERSE_CHECK pragma
  -  [#4314](https://github.com/agda/agda/issues/4314): Internal error with generalize
  -  [#4323](https://github.com/agda/agda/issues/4323): Internal error (Rewriting.hs:395) with generalize and rewrite rules
