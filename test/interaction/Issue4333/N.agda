{-# OPTIONS --rewriting #-}
{-# OPTIONS --confluence-check #-}

-- {-# OPTIONS -v import.iface:10 #-}
-- {-# OPTIONS -v import.iface.imports:20 #-}
-- {-# OPTIONS -v import.iface.confluence:20 #-}

module Issue4333.N where

open import Issue4333.M
open import Issue4333.N0
open import Issue4333.N1

postulate
  of-type : (X : Set) (x : X) → Set

-- Subject reduction violated for b₁' = b.
_ = of-type (B a₁') b₁'
_ = of-type (B a₀') b
