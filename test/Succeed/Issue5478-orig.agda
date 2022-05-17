{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-double-check #-}

-- {-# OPTIONS -v impossible:70 #-}
-- {-# OPTIONS -v tc.interaction:30 #-}
-- {-# OPTIONS -v tc.check.internal:20 #-}

open import Agda.Builtin.Sigma

record R1 (A : Set) : Set where

instance
  prodR1 : {A : Set} {B : A → Set} → ⦃ {a : A} → R1 (B a) ⦄ → R1 (Σ A B)
  prodR1 = record {}

record R2 (A : Set) ⦃ aR1 : R1 A ⦄ : Set₁ where
  field
    f : A → Set
open R2 ⦃...⦄ public

record R3 (A : Set) (B : A → Set) : Set₁ where
  instance
    bR1 : {a : A} → R1 (B a)
    bR1 = {!!} -- record {}
  field
    ⦃ r2 ⦄ : R2 (Σ A B)
    fab : ∀ {a} {b : B a} → f (a , b)
