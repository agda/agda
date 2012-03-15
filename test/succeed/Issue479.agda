-- Andreas, 2012-03-15, example by Ulf
-- {-# OPTIONS -v tc.meta:20 #-}
module Issue479 where

import Common.Level
open import Common.Equality

data ⊥ : Set where
data Bool : Set where true false : Bool

X       : Bool
X=true  : X ≡ true
X≠false : X ≡ false → ⊥
X = _
X≠false ()
X=true = refl

-- The emptyness check for X ≡ false should be postponed until
-- X has been solved to true.
