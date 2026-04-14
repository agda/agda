{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality.Rewrite renaming (primNoMatch to ⟨_⟩)
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data T : Nat → Set where
  U : (n : Nat) → T n

postulate
  f  : (n : Nat) → T (n + 0) → T n
  fn : (n : Nat) → f n (U ⟨ n + 0 ⟩) ≡ U n

  {-# REWRITE fn #-}

f0 : f 0 (U 0) ≡ U 0
f0 = refl
