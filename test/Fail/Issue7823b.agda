data Nat : Set where
  zero : Nat
  suc : Nat → Nat

postulate
  P : {A : Set} → A → Set
  A : Set

{-# DISPLAY P suc = A #-}

_ : P (suc zero)
_ = zero

-- was: Nat !=< A
-- should be: Nat !=< P (suc zero)
