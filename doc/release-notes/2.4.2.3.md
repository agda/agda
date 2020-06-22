Release notes for Agda version 2.4.2.3
======================================

Installation and infrastructure
-------------------------------

* Added support for GHC 7.10.1.

* Removed support for GHC 7.0.4.

Language
--------

* `_ `is no longer a valid name for a definition.  The following fails
  now: [Issue [#1465](https://github.com/agda/agda/issues/1465)]

  ```agda
  postulate _ : Set
  ```

* Typed bindings can now contain hiding information
  [Issue [#1391](https://github.com/agda/agda/issues/1391)].  This
  means you can now write

  ```agda
  assoc : (xs {ys zs} : List A) → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  ```

  instead of the longer

  ```agda
  assoc : (xs : List A) {ys zs : List A} → ...
  ```

  It also works with irrelevance

  ```agda
  .(xs {ys zs} : List A) → ...
  ```

  but of course does not make sense if there is hiding information already.
  Thus, this is (still) a parse error:

  ```agda
  {xs {ys zs} : List A} → ...
  ```

* The builtins for sized types no longer need accompanying postulates.
  The BUILTIN pragmas for size stuff now also declare the identifiers
  they bind to.

  ```agda
  {-# BUILTIN SIZEUNIV SizeUniv #-}  --  SizeUniv : SizeUniv
  {-# BUILTIN SIZE     Size     #-}  --  Size     : SizeUniv
  {-# BUILTIN SIZELT   Size<_   #-}  --  Size<_   : ..Size → SizeUniv
  {-# BUILTIN SIZESUC  ↑_       #-}  --  ↑_       : Size → Size
  {-# BUILTIN SIZEINF  ∞        #-}  --  ∞       : Size
  ```

  `Size` and `Size<` now live in the new universe `SizeUniv`.  It is
  forbidden to build function spaces in this universe, in order to
  prevent the malicious assumption of a size predecessor

  ```agda
  pred : (i : Size) → Size< i
  ```

  [Issue [#1428](https://github.com/agda/agda/issues/1428)].

* Unambiguous notations (coming from syntax declarations) that resolve
  to ambiguous names are now parsed unambiguously
  [Issue [#1194](https://github.com/agda/agda/issues/1194)].

* If only some instances of an overloaded name have a given associated
  notation (coming from syntax declarations), then this name can only
  be resolved to the given instances of the name, not to other
  instances [Issue [#1194](https://github.com/agda/agda/issues/1194)].

  Previously, if different instances of an overloaded name had
  *different* associated notations, then none of the notations could
  be used. Now all of them can be used.

  Note that notation identity does not only involve the right-hand
  side of the syntax declaration. For instance, the following
  notations are not seen as identical, because the implicit argument
  names are different:

  ```agda
  module A where

    data D : Set where
      c : {x y : D} → D

    syntax c {x = a} {y = b} = a ∙ b

  module B where

    data D : Set where
      c : {y x : D} → D

    syntax c {y = a} {x = b} = a ∙ b
  ```

* If an overloaded operator is in scope with at least two distinct
  fixities, then it gets the default fixity
  [Issue [#1436](https://github.com/agda/agda/issues/1436)].

  Similarly, if two or more identical notations for a given overloaded
  name are in scope, and these notations do not all have the
  same fixity, then they get the default fixity.

Type checking
-------------

* Functions of varying arity can now have with-clauses and use rewrite.

  Example:

  ```agda
  NPred : Nat → Set
  NPred 0       = Bool
  NPred (suc n) = Nat → NPred n

  const : Bool → ∀{n} → NPred n
  const b {0}       = b
  const b {suc n} m = const b {n}

  allOdd : ∀ n → NPred n
  allOdd 0 = true
  allOdd (suc n) m with even m
  ... | true  = const false
  ... | false = allOdd n
  ```

* Function defined by copattern matching can now have `with`-clauses
  and use `rewrite`.

  Example:

  ```agda
  {-# OPTIONS --copatterns #-}

  record Stream (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : A × Stream A
  open Stream

  map : ∀{A B} → (A → B) → Stream A → Stream B
  force (map f s) with force s
  ... | a , as = f a , map f as

  record Bisim {A B} (R : A → B → Set) (s : Stream A) (t : Stream B) : Set where
    coinductive
    constructor ~delay
    field
      ~force : let a , as = force s
                   b , bs = force t
               in  R a b × Bisim R as bs
  open Bisim

  SEq : ∀{A} (s t : Stream A) → Set
  SEq = Bisim (_≡_)

  -- Slightly weird definition of symmetry to demonstrate rewrite.

  ~sym' : ∀{A} {s t : Stream A} → SEq s t → SEq t s
  ~force (~sym' {s = s} {t} p) with force s | force t | ~force p
  ... | a , as | b , bs | r , q rewrite r = refl , ~sym' q
  ```

* Instances can now be defined by copattern
  matching. [Issue [#1413](https://github.com/agda/agda/issues/1413)]
  The following example extends the one in
  [Abel, Pientka, Thibodeau, Setzer, POPL 2013, Section 2.2]:

  ```agda
  {-# OPTIONS --copatterns #-}

  -- The Monad type class

  record Monad (M : Set → Set) : Set1 where
    field
      return : {A : Set}   → A → M A
      _>>=_  : {A B : Set} → M A → (A → M B) → M B
  open Monad {{...}}

  -- The State newtype

  record State (S A : Set) : Set where
    field
      runState : S → A × S
  open State

  -- State is an instance of Monad

  instance
    stateMonad : {S : Set} → Monad (State S)
    runState (return {{stateMonad}} a  ) s  = a , s    -- NEW
    runState (_>>=_  {{stateMonad}} m k) s₀ =          -- NEW
      let a , s₁ = runState m s₀
      in  runState (k a) s₁

  -- stateMonad fulfills the monad laws

  leftId : {A B S : Set}(a : A)(k : A → State S B) →
    (return a >>= k) ≡ k a
  leftId a k = refl

  rightId : {A B S : Set}(m : State S A) →
    (m >>= return) ≡ m
  rightId m = refl

  assoc : {A B C S : Set}(m : State S A)(k : A → State S B)(l : B → State S C) →
     ((m >>= k) >>= l) ≡ (m >>= λ a → k a >>= l)
  assoc m k l = refl
  ```

Emacs mode
----------

* The new menu option `Switch to another version of Agda` tries to do
  what it says.

* Changed feature: Interactively split result.

  [ This is as before: ]
  Make-case (`C-c C-c`) with no variables given tries to split on the
  result to introduce projection patterns.  The hole needs to be of
  record type, of course.

  ```agda
  test : {A B : Set} (a : A) (b : B) → A × B
  test a b = ?
  ```

  Result-splitting `?` will produce the new clauses:

  ```agda
  proj₁ (test a b) = ?
  proj₂ (test a b) = ?
  ```

  [ This has changed: ]
  If hole is of function type, `make-case` will introduce only pattern
  variables (as much as it can).

  ```agda
  testFun : {A B : Set} (a : A) (b : B) → A × B
  testFun = ?
  ```

  Result-splitting `?` will produce the new clause:

  ```agda
  testFun a b = ?
  ```

  A second invocation of `make-case` will then introduce projection
  patterns.

Error messages
--------------

* Agda now suggests corrections of misspelled options, e.g.

  ```agda
  {-# OPTIONS
    --dont-termination-check
    --without-k
    --senf-gurke
    #-}
  ```

  Unrecognized options:

  ```
  --dont-termination-check (did you mean --no-termination-check ?)
  --without-k (did you mean --without-K ?)
  --senf-gurke
  ```

  Nothing close to `--senf-gurke`, I am afraid.

Compiler backends
-----------------

* The Epic backend has been removed
  [Issue [#1481](https://github.com/agda/agda/issues/1481)].

Bug fixes
---------

* Fixed bug with `unquoteDecl` not working in instance blocks
  [Issue [#1491](https://github.com/agda/agda/issues/1491)].

* Other issues fixed (see
  [bug tracker](https://github.com/agda/agda/issues)

  [#1497](https://github.com/agda/agda/issues/1497)

  [#1500](https://github.com/agda/agda/issues/1500)
