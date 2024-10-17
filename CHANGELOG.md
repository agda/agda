Release notes for Agda version 2.8.0
====================================

Highlights
----------

Installation
------------

* Dropped support for GHC 8.6.
* Agda supports GHC versions 8.8.4 to 9.10.1.

Pragmas and options
-------------------

* New warning `InvalidDisplayForm` instead of hard error
  when a display form is illegal (and thus ignored).

* New warning `UnusedVariablesInDisplayForm` when DISPLAY pragma
  binds variables that are not used.
  Example:
  ```agda
  {-# DISPLAY List (Fin n) = ListFin #-}
  ```
  Since pattern variable `n` is not used on the right hand side `ListFin`,
  Agda throws a warning and recommeds to rewrite it as:
  ```agda
  {-# DISPLAY List (Fin _) = ListFin #-}
  ```

* New warning `WithClauseProjectionFixityMismatch` instead of hard error
  when in a with-clause a projection is used in a different fixity
  (prefix vs. postfix) than in its parent clause.

* New error warning `TooManyArgumentsToSort` instead of hard error.

* New warning `EmptyPolarityPragma` for POLARITY pragma without polarities.
  E.g. triggered by `{-# POLARITY F #-}`.

* Warning `AbsurdPatternRequiresNoRHS` has been renamed to
  `AbsurdPatternRequiresAbsentRHS`.

* New option `--js-es6` for generating JavaScript with ES6 module syntax.

* DISPLAY pragmas can now define display forms that match on defined names
  beyond constructors ([issue #7533](https://github.com/agda/agda/issues/7533)).
  Example:
  ```agda
  {-# DISPLAY Irrelevant Empty = ⊥ #-}
  ```
  `Empty` used to be interpreted as a pattern variable, effectively installing
  the display form `Irrelevant _ = ⊥`.
  Now `Empty` is treated as a matchable name, as one would intuitively expect
  from a display form.
  As a consequence, only `Irrelevant Empty` is displayed as `⊥`, not just any
  `Irrelevant A`.

Syntax
------

Additions to the Agda syntax.

* Add new literate agda: forester, see [#7403](https://github.com/agda/agda/pull/7403)
* Records can now be created using module-like syntax in place of curly braces
  and semicolons.

  ```agda
  p : Pair Nat Nat
  p = record where
    fst = 2
    snd = 3
  ```

  In a `record where` block, definitions have the semantics of let-bindings: they
  can refer to earlier bindings and may include other definitions than the fields
  of the record, including opening of modules. For instance,

  ```agda
  p₁ : Pair Nat Nat
  p₁ = record where
    open Pair p using (fst)
    n   = fst * 2
    snd = n * n
  ```

  The syntax also works for record updates

  ```agda
  p₂ : Pair Nat Nat
  p₂ = record p₁ where
    snd = snd p₁ + 1
  ```

  See [#4275](https://github.com/agda/agda/issues/4275) for the proposal.

* Type-based termination checker

  Agda is now able to use signatures of polymorphic functions during termination checking:

  ```agda
   apply : {A B : Set} → (A → B) → A → B
   apply f x = f x

   fun : Nat → Nat
   fun zero = zero
   fun (suc x) = apply fun x
   ```

  Some non-polymoprphic functions may also be recognized as size preserving, which leads to acceptance of the following functions:

  ```agda
  div : Nat → Nat → Nat
  div zero    y = zero
  div (suc x) y = suc (div (minus x y) y)

  qsort : {A : Set} → (A → A → Bool) → List A → List A
  qsort _ nil = nil
  qsort cmp (cons x xs) = qsort cmp (filter (cmp x) xs) ++ cons x (qsort cmp (filter (λ y → cmp y x) xs))
  ```

  Type-based termination checking also works for coinduction, which improves the guardedness predicate.

  ```agda
  -- This function is size-preserving
  map : {A B : Set} → (A → B) → Stream A → Stream B
  map f s .hd = f (s .hd)
  map f s .tl = map f (s .tl)

  increaseByIndex : Stream Nat → Stream Nat
  increaseByIndex s .hd = s .hd
  -- the corecursive call is not guarded by constructors here,
  -- so the syntactic guardedness check fails
  increaseByIndex s .tl = map (_+_ 1) (increaseByIndex (s .tl))
  ```

  See [user manual](https://agda.readthedocs.io/en/v2.8.0/tools/type-based-termination-checking.html)
  for more.

* It is now always possible to refer to the name of a record type's
  constructor, even if a name was not explicitly specified. This is done
  using the new `(Record name).constructor` syntax; See [issue
  #6964](https://github.com/agda/agda/issues/6964) for the motivation.

Language
--------

Changes to type checker and other components defining the Agda language.

Reflection
----------

Changes to the meta-programming facilities.

* New reflection primitive: `checkFromStringTC : String → Type → TC Term`

  Parse and type check the given string against the given type, returning
  the resulting term (when successful).


Library management
------------------

Interaction and emacs mode
--------------------------

* Agda's error messages now follow the [GNU standard](https://www.gnu.org/prep/standards/html_node/Errors.html).
  To comply with this policy, line and column are now separated by a dot instead of comma.
  The format of regular errors and error warnings follows this template:

  > _sourcefile_:_line1_._column1_-_line2_._column2_: error: [_ErrorName_]
  > ...
  > _error message_
  > ...
  > when _error context_

  _line2_ or even _column2_ can be missing, in some cases even the entire error location.
  Internal errors might follow a different format.

  Warnings are printed in a similar format:

  > _sourcefile_:_line1_._column1_-_line2_._column2_: warning: -W[no]_WarningName_
  > ...
  > _warning text_
  > ...
  > when _warning context_

* Emacs: new face `agda2-highlight-cosmetic-problem-face`
  for highlighting the new aspect `CosmeticProblem`.

* Emacs: new face `agda2-highlight-instance-problem-face`
  for highlighting the new aspect `InstanceProblem`.


Backends
--------

Other issues closed
-------------------

For 2.8.0, the following issues were also
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.8.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

NOTE: This section will be filled by output produced with `closed-issues-for-milestone 2.8.0`.
