------------------------------------------------------------------------
-- The Agda standard library
--
-- Example of a Quotient: ℤ as (ℕ × ℕ / ~)
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality.Quotients.Examples where

open import Relation.Binary.HeterogeneousEquality.Quotients
open import Level as L hiding (lift)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality hiding (isEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Function
open ≅-Reasoning

postulate quot : Quotients L.zero L.zero

ℕ² = ℕ × ℕ

_∼_ : ℕ² → ℕ² → Set
(x , y) ∼ (x' , y') = x + y' ≅ x' + y

infix 10 _∼_

∼-trans : ∀ {i j k} → i ∼ j → j ∼ k → i ∼ k
∼-trans {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} p q =
  ≡-to-≅ $ +-cancelˡ-≡ y₂ $ ≅-to-≡ $ begin
  y₂ + (x₁ + y₃) ≡⟨ ≡.sym (+-assoc y₂ x₁ y₃) ⟩
  y₂ + x₁ + y₃   ≡⟨ ≡.cong (_+ y₃) (+-comm y₂ x₁) ⟩
  x₁ + y₂ + y₃   ≅⟨ cong (_+ y₃) p ⟩
  x₂ + y₁ + y₃   ≡⟨ ≡.cong (_+ y₃) (+-comm x₂ y₁) ⟩
  y₁ + x₂ + y₃   ≡⟨ +-assoc y₁ x₂ y₃ ⟩
  y₁ + (x₂ + y₃) ≅⟨ cong (y₁ +_) q ⟩
  y₁ + (x₃ + y₂) ≡⟨ +-comm y₁ (x₃ + y₂) ⟩
  x₃ + y₂ + y₁   ≡⟨ ≡.cong (_+ y₁) (+-comm x₃ y₂) ⟩
  y₂ + x₃ + y₁   ≡⟨ +-assoc y₂ x₃ y₁ ⟩
  y₂ + (x₃ + y₁) ∎

~-isEquivalence : IsEquivalence _∼_
~-isEquivalence = record { refl  = refl
                         ; sym   = sym
                         ; trans = λ {i} {j} {k} → ∼-trans {i} {j} {k}
                         }

ℕ²-∼-setoid : Setoid L.zero L.zero
ℕ²-∼-setoid = record { isEquivalence = ~-isEquivalence }

Int : Quotient ℕ²-∼-setoid
Int = quot _
open Quotient Int renaming (Q to ℤ)

_+²_ : ℕ² → ℕ² → ℕ²
(x₁ , y₁) +² (x₂ , y₂) = x₁ + x₂ , y₁ + y₂

+²-cong : ∀{a b a' b'} → a ∼ a' → b ∼ b' → a +² b ∼ a' +² b'
+²-cong {a₁ , b₁} {c₁ , d₁} {a₂ , b₂} {c₂ , d₂} ab~cd₁ ab~cd₂ = begin
  (a₁ + c₁) + (b₂ + d₂) ≡⟨ ≡.cong (_+ (b₂ + d₂)) (+-comm a₁ c₁) ⟩
  (c₁ + a₁) + (b₂ + d₂) ≡⟨ +-assoc c₁ a₁ (b₂ + d₂) ⟩
  c₁ + (a₁ + (b₂ + d₂)) ≡⟨ ≡.cong (c₁ +_) (≡.sym (+-assoc a₁ b₂ d₂)) ⟩
  c₁ + (a₁ + b₂ + d₂)   ≅⟨ cong (λ n → c₁ + (n + d₂)) ab~cd₁ ⟩
  c₁ + (a₂ + b₁ + d₂)   ≡⟨ ≡.cong (c₁ +_) (+-assoc a₂ b₁ d₂) ⟩
  c₁ + (a₂ + (b₁ + d₂)) ≡⟨ ≡.cong (λ n → c₁ + (a₂ + n)) (+-comm b₁ d₂) ⟩
  c₁ + (a₂ + (d₂ + b₁)) ≡⟨ ≡.sym (+-assoc c₁ a₂ (d₂ + b₁)) ⟩
  (c₁ + a₂) + (d₂ + b₁) ≡⟨ ≡.cong (_+ (d₂ + b₁)) (+-comm c₁ a₂) ⟩
  (a₂ + c₁) + (d₂ + b₁) ≡⟨ +-assoc a₂ c₁ (d₂ + b₁) ⟩
  a₂ + (c₁ + (d₂ + b₁)) ≡⟨ ≡.cong (a₂ +_) (≡.sym (+-assoc c₁ d₂ b₁)) ⟩
  a₂ + (c₁ + d₂ + b₁)   ≅⟨ cong (λ n → a₂ + (n + b₁)) ab~cd₂ ⟩
  a₂ + (c₂ + d₁ + b₁)   ≡⟨ ≡.cong (a₂ +_) (+-assoc c₂ d₁ b₁) ⟩
  a₂ + (c₂ + (d₁ + b₁)) ≡⟨ ≡.cong (λ n → a₂ + (c₂ + n)) (+-comm d₁ b₁) ⟩
  a₂ + (c₂ + (b₁ + d₁)) ≡⟨ ≡.sym (+-assoc a₂ c₂ (b₁ + d₁)) ⟩
  (a₂ + c₂) + (b₁ + d₁) ∎

_+ℤ_ : ℤ → ℤ → ℤ
_+ℤ_ = Properties₂.lift₂ Int Int (λ i j → abs (i +² j))
     $ λ {a} {b} {c} p p' → compat-abs (+²-cong {a} {b} {c} p p')

zero² : ℕ²
zero² = 0 , 0

zeroℤ : ℤ
zeroℤ = abs zero²

+²-identityʳ : (i : ℕ²) → (i +² zero²) ∼ i
+²-identityʳ (x , y) = begin
  (x + 0) + y ≡⟨ ≡.cong (_+ y) (+-identityʳ x) ⟩
  x + y       ≡⟨ ≡.cong (x +_) (≡.sym (+-identityʳ y)) ⟩
  x + (y + 0) ∎

+ℤ-on-abs≅abs-+₂ : ∀ a b → abs a +ℤ abs b ≅ abs (a +² b)
+ℤ-on-abs≅abs-+₂ = Properties₂.lift₂-conv Int Int _
                 $ λ {a} {b} {c} p p′ → compat-abs (+²-cong {a} {b} {c} p p′)

+ℤ-identityʳ : ∀ i → i +ℤ zeroℤ ≅ i
+ℤ-identityʳ = lift _ eq (≅-heterogeneous-irrelevanceʳ _ _ ∘ compat-abs) where

  eq : ∀ a → abs a +ℤ zeroℤ ≅ abs a
  eq a = begin
    abs a +ℤ zeroℤ      ≡⟨⟩
    abs a +ℤ abs zero²  ≅⟨ +ℤ-on-abs≅abs-+₂ a zero² ⟩
    abs (a +² zero²)    ≅⟨ compat-abs (+²-identityʳ a) ⟩
    abs a               ∎

+²-identityˡ : (i : ℕ²) → (zero² +² i) ∼ i
+²-identityˡ i = refl

+ℤ-identityˡ : (i : ℤ)  → zeroℤ +ℤ i ≅ i
+ℤ-identityˡ = lift _ eq (≅-heterogeneous-irrelevanceʳ _ _ ∘ compat-abs) where

  eq : ∀ a → zeroℤ +ℤ abs a ≅ abs a
  eq a = begin
    zeroℤ +ℤ abs a     ≡⟨⟩
    abs zero² +ℤ abs a ≅⟨ +ℤ-on-abs≅abs-+₂ zero² a ⟩
    abs (zero² +² a)   ≅⟨ compat-abs (+²-identityˡ a) ⟩
    abs a              ∎

+²-assoc : (i j k : ℕ²) → (i +² j) +² k ∼ i +² (j +² k)
+²-assoc (a , b) (c , d) (e , f) = begin
  ((a + c) + e) + (b + (d + f)) ≡⟨ ≡.cong (_+ (b + (d + f))) (+-assoc a c e) ⟩
  (a + (c + e)) + (b + (d + f)) ≡⟨ ≡.cong ((a + (c + e)) +_) (≡.sym (+-assoc b d f)) ⟩
  (a + (c + e)) + ((b + d) + f) ∎

+ℤ-assoc : ∀ i j k → (i +ℤ j) +ℤ k ≅ i +ℤ (j +ℤ k)
+ℤ-assoc = Properties₃.lift₃ Int Int Int eq compat₃ where

  eq : ∀ i j k → (abs i +ℤ abs j) +ℤ abs k ≅ abs i +ℤ (abs j +ℤ abs k)
  eq i j k = begin
    (abs i +ℤ abs j) +ℤ abs k ≅⟨ cong (_+ℤ abs k) (+ℤ-on-abs≅abs-+₂ i j) ⟩
    (abs (i +² j) +ℤ abs k)   ≅⟨ +ℤ-on-abs≅abs-+₂ (i +² j) k ⟩
    abs ((i +² j) +² k)       ≅⟨ compat-abs (+²-assoc i j k) ⟩
    abs (i +² (j +² k))       ≅⟨ sym (+ℤ-on-abs≅abs-+₂ i (j +² k)) ⟩
    (abs i +ℤ abs (j +² k))   ≅⟨ cong (abs i +ℤ_) (sym (+ℤ-on-abs≅abs-+₂ j k)) ⟩
    abs i +ℤ (abs j +ℤ abs k) ∎

  compat₃ : ∀ {a a′ b b′ c c′} → a ∼ a′ → b ∼ b′ → c ∼ c′ → eq a b c ≅ eq a′ b′ c′
  compat₃ p q r = ≅-heterogeneous-irrelevanceˡ _ _
                $ cong₂ _+ℤ_ (cong₂ _+ℤ_ (compat-abs p) (compat-abs q))
                $ compat-abs r
