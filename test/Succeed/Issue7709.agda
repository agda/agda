module Issue7709 where

open import Agda.Builtin.Nat

postulate NonZero : Nat → Set

_^_ : Nat → Nat → Nat
x ^ zero  = 1
x ^ suc n = x * x ^ n

auto : {A : Set} ⦃ _ : A ⦄ → A
auto ⦃ x ⦄ = x

module Sub1 (bits : Nat) where
  postulate instance 2^bits≢0 : NonZero (2 ^ bits)

-- Naïvely, would add an instance with 2^64
--
--   case 0 of suc → case 0 of suc → ...
--
-- intermediate steps, which would probably run out of memory.

open Sub1 64

it : NonZero (2 ^ 64)
it = auto
