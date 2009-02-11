------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Data.Vec
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Function
open import Relation.Binary

module UsingVectorEquality (S : Setoid) where

  private module SS = Setoid S
  open SS using () renaming (carrier to A)
  import Data.Vec.Equality as VecEq
  open VecEq.Equality S

  replicate-lemma : ∀ {m} n x (xs : Vec A m) →
                    replicate {n = n}     x ++ (x ∷ xs) ≈
                    replicate {n = 1 + n} x ++      xs
  replicate-lemma zero    x xs = refl (x ∷ xs)
  replicate-lemma (suc n) x xs = SS.refl ∷-cong replicate-lemma n x xs

  xs++[]=xs : ∀ {n} (xs : Vec A n) → xs ++ [] ≈ xs
  xs++[]=xs []       = []-cong
  xs++[]=xs (x ∷ xs) = SS.refl ∷-cong xs++[]=xs xs

open import Relation.Binary.PropositionalEquality

-- lookup is natural.

lookup-natural : ∀ {A B n} (f : A → B) (i : Fin n) →
                 lookup i ∘ map f ≗ f ∘ lookup i
lookup-natural f zero    (x ∷ xs) = refl
lookup-natural f (suc i) (x ∷ xs) = lookup-natural f i xs
