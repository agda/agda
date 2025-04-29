data Nat : Set where
  zero : Nat
  suc : Nat → Nat

postulate
  P : {A : Set} → A → Set
  A : Set

{-# DISPLAY P (suc zero) = A #-}

_ : P suc
_ = zero

-- was: Nat !=< A
-- should be: Nat !=< P suc
