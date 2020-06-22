{-# OPTIONS --rewriting --confluence-check #-}

open import Common.Prelude
open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  f g    : Nat → Nat
  f-zero : f zero ≡ g zero
  f-suc  : ∀ n → f n ≡ g n → f (suc n) ≡ g (suc n)

r : (n : Nat) → f n ≡ g n
r zero = f-zero
r (suc n) = f-suc n refl
  where
    rn : f n ≡ g n
    rn = r n
    {-# REWRITE rn #-}
