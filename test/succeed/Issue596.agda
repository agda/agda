-- Andreas, 2012-04-03, reported by pumpkingod
module Issue596 where

import Common.Irrelevance
open import Common.Level
open import Common.Equality
open import Common.Prelude renaming (Nat to ℕ)

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

-- inlined from Data.Product

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

infixr 2 _×_

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∶ A ] B

-- inlined from Data.Nat.Divisibility and Data.Nat.Coprimality

infix 4 _∣_

data _∣_ : ℕ → ℕ → Set where
  divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m ∣ n

Coprime : (m n : ℕ) → Set
Coprime m n = ∀ {i} → i ∣ m × i ∣ n → i ≡ 1

record ℚ⁺ : Set where
  constructor rat⁺
  field
    numerator     : ℕ
    denominator-1 : ℕ

  denominator : ℕ
  denominator = suc denominator-1

  field
    .coprime      : Coprime numerator denominator

-- inlined from Data.Nat.LCM

record LCM (i j lcm : ℕ) : Set where
  constructor is -- Andreas, 2012-04-02 added constructor
  field
    -- The lcm is a common multiple.
    commonMultiple : i ∣ lcm × j ∣ lcm

    -- The lcm divides all common multiples, i.e. the lcm is the least
    -- common multiple according to the partial order _∣_.
    least : ∀ {m} → i ∣ m × j ∣ m → lcm ∣ m

postulate
  lcm : (i j : ℕ) → ∃ λ d → LCM i j d
  undefined : ∀ {a}{A : Set a} → A

0#⁺ : ℚ⁺
0#⁺ = rat⁺ 0 0 undefined -- (∣1⇒≡1 ∘ proj₂)

_+⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
_+⁺_ = undefined

-- the offending with-clause
+⁺-idˡ : ∀ q → 0#⁺ +⁺ q ≡ q
+⁺-idˡ (rat⁺ n d c) with lcm (suc zero) (suc d)
...                | q = undefined

-- should succeed
