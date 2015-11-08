-- Hurkens' paradox [1].

-- [1] A. Hurkens, A simplification of Girard's paradox.

{-# OPTIONS --type-in-type
  #-}

module Hurkens where

⊥ : Set
⊥ = (A : Set) -> A

¬_ : Set -> Set
¬ A = A -> ⊥

P : Set -> Set
P A = A -> Set

U : Set
U = (X : Set) -> (P (P X) -> X) -> P (P X)

τ : P (P U) -> U
τ t = \X f p -> t \x -> p (f (x X f))

σ : U -> P (P U)
σ s = s U \t -> τ t

Δ : P U
Δ = \y -> ¬ ((p : P U) -> σ y p -> p (τ (σ y)))

Ω : U
Ω = τ \p -> (x : U) -> σ x p -> p x

D : Set
D = (p : P U) -> σ Ω p -> p (τ (σ Ω))

lem₁ : (p : P U) -> ((x : U) -> σ x p -> p x) -> p Ω
lem₁ p H1 = H1 Ω \x -> H1 (τ (σ x))

lem₂ : ¬ D
lem₂ = lem₁ Δ \x H2 H3 -> H3 Δ H2 \p -> H3 \y -> p (τ (σ y))

lem₃ : D
lem₃ p = lem₁ \y -> p (τ (σ y))

loop : ⊥
loop = lem₂ lem₃
