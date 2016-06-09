-- Andreas, 2016-06-09 issue during refactoring for #1963
-- Shrunk this issue with projection-like functions from std-lib

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.proj.like:10 #-}

open import Common.Level
open import Common.Nat renaming ( Nat to ℕ )

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

postulate anything : ∀{A : Set} → A

data _≤_ : (m n : ℕ) → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

≤-refl : ∀{n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀{k l m} → k ≤ l → l ≤ m → k ≤ m
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

n≤m+n : ∀ m n → n ≤ (m + n)
n≤m+n zero zero = z≤n
n≤m+n zero (suc n) = s≤s (n≤m+n zero n)
n≤m+n (suc m) zero = z≤n
n≤m+n (suc m) (suc n) = s≤s anything

record Preord c ℓ₁ : Set (lsuc (c ⊔ ℓ₁)) where
  infix 4 _∼_
  field
    Carrier    : Set c
    _∼_        : (x y : Carrier) → Set ℓ₁  -- The relation.
    refl       : ∀{x} → x ∼ x
    trans      : ∀{x y z} → x ∼ y → y ∼ z → x ∼ z

Npreord : Preord _ _
Npreord = record { Carrier = ℕ ; _∼_ = _≤_ ; refl = ≤-refl; trans = ≤-trans }

module Pre {p₁ p₂} (P : Preord p₁ p₂) where

  open Preord P

  infix  4 _IsRelatedTo_
  infix  3 _∎
  infixr 2 _≤⟨_⟩_
  infix  1 begin_

  data _IsRelatedTo_ (x y : Carrier) : Set p₂ where
    relTo : (x≤y : x ∼ y) → x IsRelatedTo y

  begin_ : ∀ {x y} → x IsRelatedTo y → x ∼ y
  begin relTo x≤y = x≤y

  _≤⟨_⟩_ : ∀ x {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≤⟨ x≤y ⟩ relTo y≤z = relTo (trans x≤y y≤z)

  _∎ : ∀ x → x IsRelatedTo x
  _∎ _ = relTo refl

-- begin_  :  {p₁ p₂ : Level} (P : Preord p₁ p₂)
--            {x y : Preord.Carrier P} →
--            x IsRelatedTo y → (P Preord.∼ x) y
--  is projection like in argument 5 for type ProjectionLike1963.Pre._IsRelatedTo_

-- _∎  :  {p₁ p₂ : Level} (P : Preord p₁ p₂) (x : Preord.Carrier P) →
--        x IsRelatedTo x
--  is projection like in argument 2 for type ProjectionLike1963.Preord

open Pre Npreord

_+-mono_ : ∀{m₁ m₂ n₁ n₂} → m₁ ≤ m₂ → n₁ ≤ n₂ → (m₁ + n₁) ≤ (m₂ + n₂)
_+-mono_ {zero} {m₂} {n₁} {n₂} z≤n n₁≤n₂ = begin
  n₁      ≤⟨ n₁≤n₂ ⟩
  n₂      ≤⟨ n≤m+n m₂ n₂ ⟩
  m₂ + n₂ ∎
s≤s m₁≤m₂ +-mono n₁≤n₂ = s≤s (m₁≤m₂ +-mono n₁≤n₂)

ISS : ∀ {n m} (p : n ≤ m) → Set
ISS z≤n     = ⊥
ISS (s≤s p) = ⊤

test : ISS ((z≤n {0}) +-mono (s≤s (z≤n {0})))
test = tt

-- Goal display:
--     C-u C-c C-,  ISS (z≤n +-mono s≤s z≤n)
--         C-c C-,  ISS (begin 1 ≤⟨ s≤s z≤n ⟩ 1 ≤⟨ s≤s z≤n ⟩ 1 ∎)
-- C-u C-u C-c C-,  ISS (λ {y} → Pre.begin _)
