-- Andreas, 2013-02-18 problem with 'with'-display, see also issue 295
-- {-# OPTIONS -v tc.with:50 #-}
module Issue800 where

  data ⊤ : Set where
    tt : ⊤

  data I⊤ : ⊤ → Set where
    itt : ∀ r → I⊤ r

  bug : ∀ l → ∀ k → I⊤ l → ⊤
  bug .l k (itt l) with itt k
  ... | foo = {! foo!}

{-
Current rewriting:
  bug .l l (itt k) | itt .k = ?

Desired rewriting:
  bug .l k (itt l) | itt .k = ?
-}
