-- Andreas, 2022-03-02, issue #5784, reported by Trebor-Huang
-- Test case by Ulf Norell
--
-- primEraseEquality needs to normalize the sides of the equation,
-- not just reduce them.

-- Andreas, 2024-08-20, trigger warning WithoutKFlagPrimEraseEquality
{-# OPTIONS --without-K #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

primitive
  primEraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
  -- Warning:
  -- Using primEraseEquality with the without-K flag is inconsistent.

data Wrap : Set where
  wrap : Nat → Wrap

test : wrap (1 + 1) ≡ wrap 2
test = primEraseEquality refl

thm : test ≡ refl
thm = refl

-- Should succeed
-- WAS: primEraseEquality refl != refl
