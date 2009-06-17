------------------------------------------------------------------------
-- Some examples showing where the natural numbers and some related
-- operations and properties are defined, and how they can be used
------------------------------------------------------------------------

module README.Nat where

-- The natural numbers and various arithmetic operations are defined
-- in Data.Nat.

open import Data.Nat

ex₁ : ℕ
ex₁ = 1 + 3

-- Propositional equality and some related properties can be found
-- in Relation.Binary.PropositionalEquality.

open import Relation.Binary.PropositionalEquality

ex₂ : 3 + 5 ≡ 2 * 4
ex₂ = refl

-- Data.Nat.Properties contains a number of properties about natural
-- numbers. Algebra defines what a commutative semiring is, among
-- other things.

open import Algebra
import Data.Nat.Properties as Nat
private
  module ℕ = CommutativeSemiring Nat.commutativeSemiring

ex₃ : ∀ m n → m * n ≡ n * m
ex₃ m n = ℕ.*-comm m n

-- The module ≡-Reasoning in Relation.Binary.PropositionalEquality
-- provides some combinators for equational reasoning.

open ≡-Reasoning
open import Data.Product

ex₄ : ∀ m n → m * (n + 0) ≡ n * m
ex₄ m n = begin
  m * (n + 0)  ≡⟨ cong (_*_ m) (proj₂ ℕ.+-identity n) ⟩
  m * n        ≡⟨ ℕ.*-comm m n ⟩
  n * m        ∎

-- The module SemiringSolver in Data.Nat.Properties contains a solver
-- for natural number equalities involving constants, _+_ and _*_.

open Nat.SemiringSolver

ex₅ : ∀ m n → m * (n + 0) ≡ n * m
ex₅ = solve 2 (λ m n → m :* (n :+ con 0)  :=  n :* m) refl
