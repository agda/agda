{-# OPTIONS --hidden-argument-puns -WnoUnreachableClauses #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

private variable
  A B : Set
  n   : Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

length₁ : Vec A n → Nat
length₁ {n} _ = n

-- One can ensure that {x} is not interpreted as a pun by inserting
-- parentheses around x, or by using a qualified name instead.
-- Furthermore {f x} is never interpreted as a pun.

length₂ : ∀ {n A} → Vec A n → Nat
length₂ {(zero)} _ = zero
length₂ {suc n}  _ = suc n

length₃ : ∀ {n A} → Vec A n → Nat
length₃ {Nat.zero} _ = zero
length₃ {suc n}    _ = suc n

-- The examples above work also for instance arguments.

length₄ : ⦃ n : Nat ⦄ → Vec A n → Nat
length₄ ⦃ n ⦄ _ = n

length₅ : ∀ ⦃ n ⦄ {A} → Vec A n → Nat
length₅ ⦃ (zero) ⦄ _ = zero
length₅ ⦃ suc n ⦄  _ = suc n

length₆ : ∀ ⦃ n ⦄ {A} → Vec A n → Nat
length₆ ⦃ Nat.zero ⦄ _ = zero
length₆ ⦃ suc n ⦄    _ = suc n

-- One can also use pattern-matching lambdas.

length₇ : Set → ∀ {A n} → Vec A n → Nat
length₇ = λ { _ {n} _ → n }

length₈ : Set → ∀ {n A} → Vec A n → Nat
length₈ = λ where
  _ {(zero)} _ → zero
  _ {suc n}  _ → suc n

length₉ : Set → ∀ {n A} → Vec A n → Nat
length₉ = λ where
  _ {Nat.zero} _ → zero
  _ {suc n}    _ → suc n

-- Puns in subpatterns are treated like puns in top-level patterns.

length₁₀ : Vec A n → Nat
length₁₀ []            = zero
length₁₀ (_∷_ {n} _ _) = suc n

record R : Set where
  constructor c
  field
    {m}  : Nat
    {xs} : Vec Nat 0

-- Puns can be used in subpatterns in lambda-abstractions.

_ : R → Vec Nat 0
_ = λ (c {xs}) → xs

_ : R → Nat
_ = λ (c {(xs)}) → xs

-- Puns can be used in Π-types.

postulate
  _ : ((c {xs}) : R) → xs ≡ []
  _ : ((c {(xs)}) : R) → xs ≡ 0

-- Puns can be used in module telescopes.

module _ ((c {xs}) : R) where

  _ : Vec Nat 0
  _ = xs

module _ ((c {(xs)}) : R) where

  _ : Nat
  _ = xs

module V (_ : Vec Nat 0) where

module M₁ ((c {xs}) : R) = V xs

module N (_ : Nat) where

module M₂ ((c {(xs)}) : R) = N xs

-- Puns can be used in let expressions.

_ : R → Vec Nat 0
_ = λ r → let c {xs} = r in xs

_ : R → Nat
_ = λ r → let c {(xs)} = r in xs

_>>=_ : A → (A → B) → B
x >>= f = f x

-- Puns can be used in do notation.

_ : R → Vec Nat 0
_ = λ r → do
  c {xs} ← r
    where c {xs} → xs
  xs

_ : R → Nat
_ = λ r → do
  c {(xs)} ← r
    where c {(xs)} → xs
  xs

-- Puns can be used in rewrite equations.

f₁ : R → Vec Nat 0
f₁ r with c {xs} ← r | xs
… | xs = xs

f₂ : R → Nat
f₂ r with c {(xs)} ← r | xs
… | xs = xs

-- Puns can be used in pattern synonyms.

postulate
  V : Vec Nat 0 → Set
  N : Nat → Set

pattern c₁ xs = c {xs}
pattern c₂ xs = c {(xs)}

f₃ : R → Vec Nat 0
f₃ (c₁ xs) = xs

f₄ : R → Nat
f₄ (c₂ xs) = xs
