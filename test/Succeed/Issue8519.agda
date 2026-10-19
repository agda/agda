{-# OPTIONS --rewriting --cubical #-}

open import Agda.Builtin.Equality renaming (_≡_ to _≡ᴵ_)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat

{-# BUILTIN REWRITE _≡_ #-}

postulate
  f : Nat → Nat

module M (x : Nat) where

  postulate
    f-β : f x ≡ 4
  {-# REWRITE f-β #-}

  -- Succeeds
  test1 : f x ≡ 4
  test1 = λ _ → 4

  -- Used to fail
  test2 : f x ≡ 4
  test2 _ = 4

-- Succeeds
test3 : (x : Nat) → f x ≡ 4
test3 x _ = 4
