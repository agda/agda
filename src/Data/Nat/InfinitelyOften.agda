------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of and lemmas related to "true infinitely often"
------------------------------------------------------------------------

module Data.Nat.InfinitelyOften where

import Level
open import Algebra
open import Category.Monad
open import Data.Empty
open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as Prod hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary using (_∪_; _⊆_)
open RawMonad (¬¬-Monad {p = Level.zero})

-- Only true finitely often.

Fin : (ℕ → Set) → Set
Fin P = ∃ λ i → ∀ j → i ≤ j → ¬ P j

-- Fin is preserved by binary sums.

_∪-Fin_ : ∀ {P Q} → Fin P → Fin Q → Fin (P ∪ Q)
_∪-Fin_ {P} {Q} (i , ¬p) (j , ¬q) = (i ⊔ j , helper)
  where
  open ≤-Reasoning

  helper : ∀ k → i ⊔ j ≤ k → ¬ (P ∪ Q) k
  helper k i⊔j≤k (inj₁ p) = ¬p k (begin
    i      ≤⟨ m≤m⊔n i j ⟩
    i ⊔ j  ≤⟨ i⊔j≤k ⟩
    k      ∎) p
  helper k i⊔j≤k (inj₂ q) = ¬q k (begin
    j      ≤⟨ m≤m⊔n j i ⟩
    j ⊔ i  ≡⟨ ⊔-comm j i ⟩
    i ⊔ j  ≤⟨ i⊔j≤k ⟩
    k      ∎) q

-- A non-constructive definition of "true infinitely often".

Inf : (ℕ → Set) → Set
Inf P = ¬ Fin P

-- Inf commutes with binary sums (in the double-negation monad).

commutes-with-∪ : ∀ {P Q} → Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
commutes-with-∪ p∪q =
  call/cc λ ¬[p⊎q] →
  (λ ¬p ¬q → ⊥-elim (p∪q (¬p ∪-Fin ¬q)))
    <$> ¬[p⊎q] ∘ inj₁ ⊛ ¬[p⊎q] ∘ inj₂

-- Inf is functorial.

map : ∀ {P Q} → P ⊆ Q → Inf P → Inf Q
map P⊆Q ¬fin = ¬fin ∘ Prod.map id (λ fin j i≤j → fin j i≤j ∘ P⊆Q)

-- Inf is upwards closed.

up : ∀ {P} n → Inf P → Inf (P ∘ _+_ n)
up     zero    = id
up {P} (suc n) = up n ∘ up₁
  where
  up₁ : Inf P → Inf (P ∘ suc)
  up₁ ¬fin (i , fin) = ¬fin (suc i , helper)
    where
    helper : ∀ j → 1 + i ≤ j → ¬ P j
    helper ._ (s≤s i≤j) = fin _ i≤j

-- A witness.

witness : ∀ {P} → Inf P → ¬ ¬ ∃ P
witness ¬fin ¬p = ¬fin (0 , λ i _ Pi → ¬p (i , Pi))

-- Two different witnesses.

twoDifferentWitnesses
  : ∀ {P} → Inf P → ¬ ¬ ∃₂ λ m n → m ≢ n × P m × P n
twoDifferentWitnesses inf =
  witness inf                     >>= λ w₁ →
  witness (up (1 + proj₁ w₁) inf) >>= λ w₂ →
  return (_ , _ , m≢1+m+n (proj₁ w₁) , proj₂ w₁ , proj₂ w₂)
