
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Id (A : Set) : Set where
  mkId : A → Id A

data Monad (M : Set → Set) : Set where

postulate
  return : ∀ {M} {{Mon : Monad M}} {A} → A → M A
  _>>=_  : ∀ {M} {{Mon : Monad M}} {A B} → M A → (A → M B) → M B
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
    MonadStateT : ∀ {S M} {{_ : Monad M}} → Monad (StateT S M)

stateT₁ : ∀ {M} {{Mon : Monad M}} → StateT Nat M Nat
stateT₁ = return zero

stateT₂ : ∀ {M} {{Mon : Monad M}} → StateT Nat M Nat
stateT₂ = return zero >>= λ n → return (suc n)

postulate
  _<$_ : ∀ {A B M} {{Mon : Monad M}} → A → M B → M A

record ⊤ : Set where
  constructor tt

foo : Id ⊤
foo = _ <$ return zero
