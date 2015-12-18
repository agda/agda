-- Fixed on AIM XIV 2011-09-09 AA, UN
-- {-# OPTIONS -v tc.lhs.unify:50 #-}
module Issue292e where

data ⊥ : Set where

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

infix 4 _≅_

data _≅_ {A : Set} (x : A) : ∀ {B : Set} → B → Set where
  refl : x ≅ x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

data Bool : Set where true false : Bool

data D : Bool -> Set where
  tt : D true
  ff : D false

P : Set -> Set
P S = Σ S (\s → s ≅ tt)

pbool : P (D true)
pbool = tt , refl

¬pbool2 : ¬ P (D false)
¬pbool2 ( ff , () )
-- Jesper, 2015-12-18 fix of fix of fix: shouldn't work, as there is no way to
-- unify the types [D true] and [D false] unless injective type constructors
-- are enabled.

-- WAS: Andreas, 2011-09-13 fix of fix: should work again

{- WAS: expected error
ff ≅ tt should be empty, but that's not obvious to me
when checking that the clause ¬pbool2 (ff , ()) has type
¬ P (D false)
-}
