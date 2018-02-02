------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing where the integers and some related
-- operations and properties are defined, and how they can be used
------------------------------------------------------------------------

module README.Integer where

-- The integers and various arithmetic operations are defined in
-- Data.Integer.

open import Data.Integer

-- The +_ function converts natural numbers into integers.

ex₁ : ℤ
ex₁ = + 2

-- The -_ function negates an integer.

ex₂ : ℤ
ex₂ = - + 4

-- Some binary operators are also defined, including addition,
-- subtraction and multiplication.

ex₃ : ℤ
ex₃ = + 1  +  + 3 * - + 2  -  + 4

-- Propositional equality and some related properties can be found
-- in Relation.Binary.PropositionalEquality.

open import Relation.Binary.PropositionalEquality as P using (_≡_)

ex₄ : ex₃ ≡ - + 9
ex₄ = P.refl

-- Data.Integer.Properties contains a number of properties related to
-- integers. Algebra defines what a commutative ring is, among other
-- things.

import Data.Integer.Properties as ℤₚ

ex₅ : ∀ i j → i * j ≡ j * i
ex₅ i j = ℤₚ.*-comm i j

-- The module ≡-Reasoning in Relation.Binary.PropositionalEquality
-- provides some combinators for equational reasoning.

open P.≡-Reasoning
open import Data.Product

ex₆ : ∀ i j → i * (j + + 0) ≡ j * i
ex₆ i j = begin
  i * (j + + 0)  ≡⟨ P.cong (i *_) (ℤₚ.+-identityʳ j) ⟩
  i * j          ≡⟨ ℤₚ.*-comm i j ⟩
  j * i          ∎

-- The module RingSolver in Data.Integer.Properties contains a solver
-- for integer equalities involving variables, constants, _+_, _*_, -_
-- and _-_.

ex₇ : ∀ i j → i * - j - j * i ≡ - + 2 * i * j
ex₇ = solve 2 (λ i j → i :* :- j :- j :* i  :=  :- con (+ 2) :* i :* j)
              P.refl
  where open ℤₚ.RingSolver
