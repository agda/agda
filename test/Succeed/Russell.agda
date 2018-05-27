-- Andreas, 2013-03-15
-- Paolo Capriotti's formalization of Russell's paradox
{-# OPTIONS --without-K --type-in-type #-}
module Russell where

open import Common.Product
open import Common.Equality

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

-- a model of set theory, uses Set : Set
data U : Set where
  set : (I : Set) → (I → U) → U

-- a set is regular if it doesn't contain itself
regular : U → Set
regular (set I f) = (i : I) → ¬ (f i ≡ set I f)

-- Russell's set: the set of all regular sets
R : U
R = set (Σ U regular) proj₁

-- R is not regular
R-nonreg : ¬ (regular R)
R-nonreg reg = reg (R , reg) refl

-- R is regular
R-reg : regular R
R-reg (x , reg) p = subst regular p reg (x , reg) p

-- contradiction

absurd : ⊥
absurd = R-nonreg R-reg
