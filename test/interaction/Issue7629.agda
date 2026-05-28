-- Andreas, 2026-05-01, issue #7629
-- Internal error when splitting on hit.

{-# OPTIONS --cubical #-}

open import Agda.Primitive using (Set)
open import Agda.Primitive.Cubical using (I; i0; i1)
open import Agda.Builtin.Cubical.Path using (PathP)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ _ → A)

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

hProp : Set₁
hProp = Σ Set isProp

data ℤ : Set where
  pos : Nat → ℤ

postulate
  _·_ : ℤ → ℤ → ℤ
  _<_ : ℤ → ℤ → Set
  isProp< : (x y : ℤ) → isProp (x < y)
  Nat→ℤ : Nat → ℤ

_∼_ : ℤ × Nat → ℤ × Nat → Set
(a , b) ∼ (c , d) = (a · Nat→ℤ d) ≡ (c · Nat→ℤ b)

data ℚ : Set where
  [_] : ℤ × Nat → ℚ
  eq/ : (a/b c/d : ℤ × Nat) → a/b ∼ c/d → [ a/b ] ≡ [ c/d ]

postulate
  lemma< : ((a , b) (c , d) (e , f) : (ℤ × Nat))
         → (c · Nat→ℤ f) ≡ (e · Nat→ℤ d)
         → ((a · Nat→ℤ d) < (c · Nat→ℤ b))
         ≡ ((a · Nat→ℤ f) < (e · Nat→ℤ b))

  isPropIsProp : ∀ (A : Set) → isProp (isProp A)

  isProp→PathP :
    ∀ {B : I → Set}
    → ((i : I) → isProp (B i))
    → (b0 : B i0) (b1 : B i1)
    → PathP B b0 b1

mutual
  fun₀ : ℤ × Nat → ℚ → hProp

  postulate
    toPath : ∀ a/b c/d (x : a/b ∼ c/d) (y : ℚ) → fun₀ a/b y ≡ fun₀ c/d y

  fun₀ (a , b) [ c , d ]         .fst = (a · Nat→ℤ d) < (c · Nat→ℤ b)
  fun₀ _       [ _ ]             .snd = isProp< _ _
  fun₀ a/b (eq/ c/d e/f cf≡ed i) .fst = lemma< a/b c/d e/f cf≡ed i
  fun₀ a/b (eq/ c/d e/f cf≡ed i) .snd =
    isProp→PathP (λ i → isPropIsProp (lemma< a/b c/d e/f cf≡ed i))
                 (isProp< _ _)
                 (isProp< _ _)
                 i

_<'_ : ℚ → ℚ → hProp
_<'_ [ a/b ]               y = fun₀ a/b y
_<'_ (eq/ a/b c/d ad≡cb i) y = toPath a/b c/d ad≡cb y i

0ℚ : ℚ
0ℚ = [ pos zero , zero ]

test : Σ ℚ (λ q → fst (0ℚ <' q)) → Set
test (q , q+) = {!q!}  -- C-c C-c

-- WAS: Internal error.

-- Splitting should succeed (with unsolved constraints).
