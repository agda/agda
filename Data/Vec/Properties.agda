------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

open import Relation.Binary

module Data.Vec.Properties (S : Setoid) where

private module SS = Setoid S
open SS using () renaming (carrier to A)
open import Data.Vec
import Data.Vec.Equality as VecEq
open VecEq.Equality S
open import Data.Nat

replicate-lemma : ∀ {m} n x (xs : Vec A m) →
                  replicate {n = n}     x ++ (x ∷ xs) ≈
                  replicate {n = 1 + n} x ++      xs
replicate-lemma zero    x xs = refl (x ∷ xs)
replicate-lemma (suc n) x xs = SS.refl ∷-cong replicate-lemma n x xs

xs++[]=xs : ∀ {n} (xs : Vec A n) → xs ++ [] ≈ xs
xs++[]=xs []       = []-cong
xs++[]=xs (x ∷ xs) = SS.refl ∷-cong xs++[]=xs xs
