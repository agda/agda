-- Andreas, 2025-05-30 issue #7906, reported and test case by Amelia.
-- We used the original clauses for reducing away non-recursive calls
-- in the termination checker.
-- The original clauses do not fire if one underapplies a function,
-- even when the missing arguments could be simply returned as lambdas.
-- The compiled clauses do that.
-- Issue was fixed by using compiled clause reduction even in the termination checker.

{-# OPTIONS --allow-unsolved-metas #-}

module Issue7906 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open Agda.Primitive

-- Secondary issue:

module IteratedReduction where

  open import Agda.Builtin.Nat

  record R : Set where
    field
      fun : Nat → Nat
      val : Nat
  open R

  r : R
  -- non-recursive clauses:
  r .fun zero = zero
  r .fun (suc n) = suc n
  r .val = fails
    where
    succeeds = r .fun 42        -- this accepted by the termination checker
    fails = r .fun (r .fun 42)  -- this should also be accepted by the termination checker

-- Original issue:

private variable
  l l' : Level
  A B C : Set l
  x y z : A
  f : A → B
  P : A → Set l

fibre : (A → B) → B → Set _
fibre {A = A} f y = Σ A λ x → f x ≡ y

subst : (P : A → Set l) → x ≡ y → P x → P y
subst P refl x = x

postulate
  Whatever : {A : Set l} → A → Set
  whatever : {A : Set l} (x : A) → Whatever x

record is-iso {A : Set l} {B : Set l'} (f : A → B) : Set (l ⊔ l') where
  field
    from : B → A
    linv : Whatever (λ x → from (f x))

open is-iso

_≃_ : Set l → Set l → Set l
A ≃ B = Σ (A → B) is-iso

module _ {A : Set l} {B : Set l} {f : A → B} {P : B → Set l} where
  shuffle : ((b : B) → fibre f b → P b) ≃ ((a : A) → P (f a))

  shuffle .fst g a = g (f a) (a , refl) -- used to fail
  -- shuffle .fst = λ g a → g (f a) (a , refl) -- worked already
  shuffle .snd = go where
    go : is-iso (shuffle .fst)
    go .from g b x = subst P (x .snd) (g (x .fst))
    go .linv = whatever {!   !}
