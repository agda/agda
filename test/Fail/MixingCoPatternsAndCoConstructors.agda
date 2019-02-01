{-# OPTIONS --guardedness #-}
module MixingCoPatternsAndCoConstructors where

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

module MStream where

  record Stream (A : Set) : Set where
    coinductive
    constructor _∷_
    field
      head : A
      tail : Stream A
  open Stream

  weird : (n : ℕ) → Stream ℕ
  head (weird zero)    = zero
  tail (weird zero)    = weird zero
  head (weird (suc n)) = n
  tail (weird (suc n)) = tail (weird n)

  weird' : (n : ℕ) → Stream ℕ
  head (weird' zero) = zero
  tail (weird' zero) = weird' zero
  weird' (suc n) = n ∷ tail (weird' n)

  -- BAD:
  weird'' : (n : ℕ) → Stream ℕ
  weird'' zero    = zero ∷ weird'' zero
  weird'' (suc n) = n ∷ tail (weird'' n)

  -- productive, but not strongly normalizing,
  -- should be rejected by termination checker:

  repeat : {A : Set}(a : A) → Stream A
  head (repeat a) = a
  tail (repeat a) = a ∷ tail (repeat a)

module Coinduction where

  import Common.Level
  open import Common.Coinduction

  record Stream (A : Set) : Set where
    inductive
    constructor _∷_
    field
      head : A
      tail : ∞ (Stream A)
  open Stream

  weird'' : (n : ℕ) → Stream ℕ
  weird'' zero    = zero ∷ (♯ weird'' zero)
  weird'' (suc n) = n ∷ tail (weird'' n)




module CoList where

  mutual

    data CoList (A : Set) : Set where
      []  : CoList A
      _∷_ : (x : A)(xs : CoList∞ A) → CoList A

    record CoList∞ (A : Set) : Set where
      coinductive
      constructor delay
      field
        force : CoList A

  open CoList∞

  downFrom : (n : ℕ) → CoList ℕ
  downFrom zero    = []
  downFrom (suc n) = n ∷ delay (downFrom n)

  down : (n : ℕ) → CoList∞ ℕ
  force (down zero)    = []
  force (down (suc n)) = n ∷ delay (force (down n))
    -- weird detour: delay (force ... to test termination checker
