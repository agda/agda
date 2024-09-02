module Issue7250 where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Issue7250.B

-- open One′
-- ^ no luck again

instance
  Whatever-Bool : Whatever Bool
  Whatever-Bool .go false = true
  Whatever-Bool .go true  = false
  {-# OVERLAPPABLE Whatever-Bool #-}
    -- ^ practically wrong annotation but it's good to trigger the bug
--  {-# OVERLAPPING Whatever-Bool #-}

private
  test₁ : Bool
  test₁ = go false

  _ : test₁ ≡ true
  _ = refl

  test₂ : Nat
  test₂ = go 42

  _ : test₂ ≡ 42
  _ = refl
