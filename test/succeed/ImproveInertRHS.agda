
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Id (A : Set) : Set where
  mkId : A → Id A

data Monad (M : Set → Set) : Set where

postulate
  return : {M : Set → Set} {{Mon : Monad M}} {A : Set} → A → M A
  State : (S A : Set) → Set

  instance
    MonadState : ∀ {S} → Monad (State S)
    MonadId : Monad Id

-- Yields
--   _M Nat == State Nat Nat,
-- which inert improvement solves by
--   _M x := State (_S x) (_A x)
--     with _S Nat == Nat
--          _A Nat == Nat
-- This allows instance search to pick the right instance.
rz : State Nat Nat
rz = return zero

postulate
  StateT : (S : Set) (M : Set → Set) (A : Set) → Set

  instance
    MonadStateT : ∀ {S M} {{MonM : Monad M}} → Monad (StateT S M)

rzt : ∀ {M} {{Mon : Monad M}} → StateT Nat M Nat
rzt = return zero