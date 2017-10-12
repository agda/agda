------------------------------------------------------------------------
-- The Agda standard library
--
-- Example showing how the free monad construction on containers can be
-- used
------------------------------------------------------------------------

module README.Container.FreeMonad where

open import Category.Monad
open import Data.Empty
open import Data.Unit
open import Data.Bool.Base using (Bool; true)
open import Data.Nat
open import Data.Sum using (inj₁; inj₂)
open import Data.Product renaming (_×_ to _⟨×⟩_)
open import Data.Container
open import Data.Container.Combinator
open import Data.Container.FreeMonad
open import Data.W
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------

-- The signature of state and its (generic) operations.

State : Set → Container _
State S = ⊤ ⟶ S ⊎ S ⟶ ⊤
  where
  _⟶_ : Set → Set → Container _
  I ⟶ O = I ▷ λ _ → O

get : ∀ {S} → State S ⋆ S
get = inn (inj₁ _ , return)
  where
  open RawMonad rawMonad

put : ∀ {S} → S → State S ⋆ ⊤
put s = inn (inj₂ s , return)
  where
  open RawMonad rawMonad

-- Using the above we can, for example, write a stateful program that
-- delivers a boolean.
prog : State ℕ ⋆ Bool
prog =
  get         >>= λ n →
  put (suc n) >>
  return true
  where
  open RawMonad rawMonad

runState : ∀ {S X} → State S ⋆ X → (S → X ⟨×⟩ S)
runState (sup (inj₁ x) _)        = λ s → x , s
runState (sup (inj₂ (inj₁ _)) k) = λ s → runState (k s) s
runState (sup (inj₂ (inj₂ s)) k) = λ _ → runState (k _) s

test : runState prog 0 ≡ (true , 1)
test = refl

-- It should be noted that @State S ⋆ X@ is not the state monad. If we
-- could quotient @State S ⋆ X@ by the seven axioms of state (see
-- Plotkin and Power's "Notions of Computation Determine Monads", 2002)
-- then we would get the state monad.
