------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Data.Vec
open import Data.Vec.Equality
open import Data.Nat
import Relation.Binary.PropositionalEquality as PropEq

replicate-lemma : ∀ {a m} n x (xs : Vec a m) →
                  replicate {n = n}     x ++ (x ∷ xs) ≈
                  replicate {n = 1 + n} x ++      xs
replicate-lemma zero    x xs = refl (x ∷ xs)
replicate-lemma (suc n) x xs = PropEq.refl ∷-cong replicate-lemma n x xs

xs++[]=xs : ∀ {a n} (xs : Vec a n) → xs ++ [] ≈ xs
xs++[]=xs []       = []-cong
xs++[]=xs (x ∷ xs) = PropEq.refl ∷-cong xs++[]=xs xs
