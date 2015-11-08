-- {-# OPTIONS -v tc.proj.like:10 #-}
-- {-# OPTIONS -v tc.conv:10 #-}
open import Common.Level

module ProjectionLikeAndModules (A : Set) (a : A) where

record ⊤ : Set where
  constructor tt

data Wrap (W : Set) : Set where
  wrap : W → Wrap W

data Bool : Set where
  true false : Bool

-- postulate

-- `or' should be projection like in the module parameters
if : Bool → {ℓ : Level} {B : Set ℓ} → B → B → B
if true  a b = a
if false a b = b

postulate
  u v : ⊤
  P : {ℓ : Level} {C : Set ℓ} (c : C) -> Set

test : (y : Bool)
  -> P (if y (wrap u) (wrap tt))
  -> P (if y (wrap tt) (wrap v))
test y h = h

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:536
