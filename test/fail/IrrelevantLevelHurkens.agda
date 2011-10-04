-- {-# OPTIONS -v tc.meta.assign:15 #-}
-- Ulf, 2011-10-04
-- I still don't quite believe in irrelevant levels. In part because I just proved ⊥:

module IrrelevantLevelHurkens where

open import Imports.Level

data _≡_ {a}{A : Set a}(x : A) : A → Set where
  refl : x ≡ x

data Irr .(i : Level)(A : Set i) : Set where
  irr : Irr i A

data Unit : Set where
  unit : Unit

unirr : ∀ .i (A : Set i) → Irr i A → Unit
unirr i A irr = unit

↓_  : ∀ .{i} → Set i → Set
foo : ∀ .{i}{A : Set i}(x : Irr i A) → unirr i A x ≡ unirr zero (↓ A) _
↓ A    = _
foo xs = refl
{- Andreas, 2011-10-04 Irrelevant Levels do not harmonize with solving

type of meta = .{.i : Level} (A : Set .i) → Set
solving _39 := λ {.i} A → A
term _38 xs := xs
passed occursCheck
type of meta = ..{i : Level} {A : Set i} (x : Irr .(i) A) →
               Irr .(zero) (↓ A)
solving _38 := λ {i} {A} x → x

The solutions x and A for the two holes do not type check, if entered manually.
The solver would need to re-type-check to make sure solutions are correct.
For now, just do not supply --experimental-irrelevance flag.
-}

⊥′ : Set
⊥′ = ↓ ((A : Set) → A)

¬_ : Set → Set
¬ A = A → ⊥′

P : Set → Set
P A = ↓ (A → Set)

U : Set
U = ↓ ((X : Set) → (P (P X) → X) → P (P X))

τ : P (P U) → U
τ t = λ X f p → t λ x → p (f (x X f))

σ : U → P (P U)
σ s pu = s U (λ t → τ t) pu

Δ : P U
Δ = λ y → ¬ ((p : P U) → σ y p → p (τ (σ y)))

Ω : U
Ω X t px = τ (λ p → (x : U) → σ x p → p x) X t px

D : Set
D = (p : P U) → σ Ω p → p (τ (σ Ω))

lem₁ : (p : P U) → ((x : U) → σ x p → p x) → p Ω
lem₁ p H1 = H1 Ω λ x → H1 (τ (σ x))

lem₂ : ¬ D
lem₂ d A = lem₁ Δ (λ x H2 H3 → H3 Δ H2 λ p → H3 λ y → p (τ (σ y))) d A

lem₃ : D
lem₃ p = lem₁ λ y → p (τ (σ y))

loop : ⊥′
loop = λ A → lem₂ lem₃ A

data ⊥ : Set where

false : ⊥
false = loop ⊥

