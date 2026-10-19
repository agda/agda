{-# OPTIONS --cubical-compatible --erasure #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

data D : @0 ⊤ → Set where
  c : (x : ⊤) → D x

-- The transpX clause for F was still ill-typed after the fix of #7139
-- because the left inverse *proof* (leftInv) was not permuted correctly.
-- (This was reported as a "not usable at modality" error.)
F : (@0 x : ⊤) → @0 x ≡ tt → D x → Set₁
F _ _ (c _) = Set
