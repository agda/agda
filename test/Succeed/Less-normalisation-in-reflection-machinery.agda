open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Common.Product

{-# TERMINATING #-}

Loop : Set
Loop = Loop

data Box (A : Set) : Set where
  box : A → Box A

{-# TERMINATING #-}

Boxed-loop : Set
Boxed-loop = Box Boxed-loop

postulate
  boxed-loop : Boxed-loop

test₂ : Term
test₂ = quoteTerm Loop

macro

  m₄ : Term → Term → TC ⊤
  m₄ _ hole = unify hole (def (quote ⊤) [])

test₄ : Set
test₄ = m₄ Loop

macro

  m₆ : Term → TC ⊤
  m₆ hole =
    bindTC (checkType (def (quote Loop) []) (agda-sort (lit 0))) λ A →
    unify hole A

test₆ : Set
test₆ = m₆

macro

  m₇ : Term → TC ⊤
  m₇ hole =
    bindTC (quoteTC Loop) λ A →
    unify hole A

test₇ : Set
test₇ = m₇

Vec : Set → Nat → Set
Vec A zero    = ⊤
Vec A (suc n) = A × Vec A n

macro

  m₈ : Term → TC ⊤
  m₈ hole =
    bindTC (reduce V) λ V →
    unify hole V
    where
    varg = arg (arg-info visible (modality relevant quantity-ω))
    V    = def (quote Vec) (varg (def (quote Boxed-loop) []) ∷
                            varg (lit (nat 1)) ∷
                            [])

test₈ : Set
test₈ = m₈
