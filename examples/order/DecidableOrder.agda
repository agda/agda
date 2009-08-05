module DecidableOrder where

open import Logic.Relations
open import Logic.Identity using (_≡_)

open module Antisym = PolyEq _≡_ using (Antisymmetric)

record DecidableOrder (A : Set) : Set1 where
  field
    _≤_     : Rel A
    refl    : Reflexive _≤_
    antisym : Antisymmetric _≤_
    trans   : Transitive _≤_
    total   : Total _≤_
    decide  : forall x y -> Decidable (x ≤ y)

  infix 80 _≤_ _≥_

  _≥_ = \(x y : A) -> y ≤ x
