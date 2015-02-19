------------------------------------------------------------------------
-- The Agda standard library
--
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

open import Algebra

module Algebra.Operations {s₁ s₂} (S : Semiring s₁ s₂) where

open Semiring S renaming (zero to *-zero)
open import Data.Nat.Base
  using (zero; suc; ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Product using (module Σ)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.EqReasoning as EqR
open EqR setoid

------------------------------------------------------------------------
-- Operations

-- Multiplication by natural number.

infixr 7 _×_ _×′_

_×_ : ℕ → Carrier → Carrier
0     × x = 0#
suc n × x = x + n × x

-- A variant that includes a "redundant" case which ensures that 1 × y
-- is definitionally equal to y.

_×′_ : ℕ → Carrier → Carrier
0     ×′ x = 0#
1     ×′ x = x
suc n ×′ x = x + n ×′ x

-- Exponentiation.

infixr 8 _^_

_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Some properties

-- Unfolding lemma for _×′_.

1+×′ : ∀ n x → suc n ×′ x ≈ x + n ×′ x
1+×′ 0 x = begin
  x       ≈⟨ sym $ Σ.proj₂ +-identity x ⟩
  x + 0#  ∎
1+×′ (suc n) x = begin
  x + suc n ×′ x  ≡⟨⟩
  x + suc n ×′ x  ∎

-- _×_ and _×′_ are extensionally equal (up to the setoid
-- equivalence).

×≈×′ : ∀ n x → n × x ≈ n ×′ x
×≈×′ 0       x = begin 0# ∎
×≈×′ (suc n) x = begin
  x + n × x   ≈⟨ +-cong refl (×≈×′ n x) ⟩
  x + n ×′ x  ≈⟨ sym $ 1+×′ n x ⟩
  suc n ×′ x  ∎

-- _×_ is homomorphic with respect to _ℕ+_/_+_.

×-homo-+ : ∀ c m n → (m ℕ+ n) × c ≈ m × c + n × c
×-homo-+ c 0 n = begin
  n × c       ≈⟨ sym $ Σ.proj₁ +-identity (n × c) ⟩
  0# + n × c  ∎
×-homo-+ c (suc m) n = begin
  c + (m ℕ+ n) × c     ≈⟨ +-cong refl (×-homo-+ c m n) ⟩
  c + (m × c + n × c)  ≈⟨ sym $ +-assoc c (m × c) (n × c) ⟩
  c + m × c + n × c    ∎

-- _×′_ is homomorphic with respect to _ℕ+_/_+_.

×′-homo-+ : ∀ c m n → (m ℕ+ n) ×′ c ≈ m ×′ c + n ×′ c
×′-homo-+ c m n = begin
  (m ℕ+ n) ×′ c    ≈⟨ sym $ ×≈×′ (m ℕ+ n) c ⟩
  (m ℕ+ n) ×  c    ≈⟨ ×-homo-+ c m n ⟩
  m ×  c + n ×  c  ≈⟨ +-cong (×≈×′ m c) (×≈×′ n c) ⟩
  m ×′ c + n ×′ c  ∎

-- _× 1# is homomorphic with respect to _ℕ*_/_*_.

×1-homo-* : ∀ m n → (m ℕ* n) × 1# ≈ (m × 1#) * (n × 1#)
×1-homo-* 0 n = begin
  0#             ≈⟨ sym $ Σ.proj₁ *-zero (n × 1#) ⟩
  0# * (n × 1#)  ∎
×1-homo-* (suc m) n = begin
  (n ℕ+ m ℕ* n) × 1#                   ≈⟨ ×-homo-+ 1# n (m ℕ* n) ⟩
  n × 1# + (m ℕ* n) × 1#               ≈⟨ +-cong refl (×1-homo-* m n) ⟩
  n × 1# + (m × 1#) * (n × 1#)         ≈⟨ sym $ +-cong (Σ.proj₁ *-identity (n × 1#)) refl ⟩
  1# * (n × 1#) + (m × 1#) * (n × 1#)  ≈⟨ sym $ Σ.proj₂ distrib (n × 1#) 1# (m × 1#) ⟩
  (1# + m × 1#) * (n × 1#)             ∎

-- _×′ 1# is homomorphic with respect to _ℕ*_/_*_.

×′1-homo-* : ∀ m n → (m ℕ* n) ×′ 1# ≈ (m ×′ 1#) * (n ×′ 1#)
×′1-homo-* m n = begin
  (m ℕ* n) ×′ 1#         ≈⟨ sym $ ×≈×′ (m ℕ* n) 1# ⟩
  (m ℕ* n) ×  1#         ≈⟨ ×1-homo-* m n ⟩
  (m ×  1#) * (n ×  1#)  ≈⟨ *-cong (×≈×′ m 1#) (×≈×′ n 1#) ⟩
  (m ×′ 1#) * (n ×′ 1#)  ∎

-- _×_ preserves equality.

×-cong : _×_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×-cong {n} {n′} {x} {x′} n≡n′ x≈x′ = begin
  n  × x   ≈⟨ reflexive $ PropEq.cong (λ n → n × x) n≡n′ ⟩
  n′ × x   ≈⟨ ×-congʳ n′ x≈x′ ⟩
  n′ × x′  ∎
  where
  ×-congʳ : ∀ n → (_×_ n) Preserves _≈_ ⟶ _≈_
  ×-congʳ 0       x≈x′ = refl
  ×-congʳ (suc n) x≈x′ = x≈x′ ⟨ +-cong ⟩ ×-congʳ n x≈x′

-- _×′_ preserves equality.

×′-cong : _×′_ Preserves₂ _≡_ ⟶ _≈_ ⟶ _≈_
×′-cong {n} {n′} {x} {x′} n≡n′ x≈x′ = begin
  n  ×′ x   ≈⟨ sym $ ×≈×′ n x ⟩
  n  ×  x   ≈⟨ ×-cong n≡n′ x≈x′ ⟩
  n′ ×  x′  ≈⟨ ×≈×′ n′ x′ ⟩
  n′ ×′ x′  ∎

-- _^_ preserves equality.

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong {x} {x'} {n} {n'} x≈x' n≡n' = begin
  x  ^ n   ≈⟨ reflexive $ PropEq.cong (_^_ x) n≡n' ⟩
  x  ^ n'  ≈⟨ ^-congˡ n' x≈x' ⟩
  x' ^ n'  ∎
  where
  ^-congˡ : ∀ n → (λ x → x ^ n) Preserves _≈_ ⟶ _≈_
  ^-congˡ zero    x≈x' = refl
  ^-congˡ (suc n) x≈x' = x≈x' ⟨ *-cong ⟩ ^-congˡ n x≈x'
