{-# OPTIONS --rewriting --confluence-check #-}

-- {-# OPTIONS -v rewriting:100 -v tc.conv.atom:30 -v tc.inj.use:30 #-}

open import Common.Equality

{-# BUILTIN REWRITE _≡_ #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)

postulate
  plus-zero : ∀ x → (x + zero) ≡ x

{-# REWRITE plus-zero #-}

mutual
  secret-number : Nat
  secret-number = _

  test : ∀ x → (x + secret-number) ≡ x
  test x = refl

  reveal : secret-number ≡ zero
  reveal = refl
