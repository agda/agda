------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Data.Vec
open import Data.Vec.Equality
open import Data.Nat
open import Logic

replicate-lemma : forall {a m} n x (xs : Vec a m)
  -> replicate {n = n}     x ++ (x ∷ xs) ≈-Vec
     replicate {n = 1 + n} x ++      xs
replicate-lemma zero    x xs = Vec-refl (x ∷ xs)
replicate-lemma (suc n) x xs = ≡-refl ∷-cong replicate-lemma n x xs

xs++[]=xs : forall {a n} (xs : Vec a n) -> xs ++ [] ≈-Vec xs
xs++[]=xs []       = []-cong
xs++[]=xs (x ∷ xs) = ≡-refl ∷-cong xs++[]=xs xs
