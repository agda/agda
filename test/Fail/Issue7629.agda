-- Andreas, 2026-05-01, issue #7629
-- Internal error due to bug in clause compiler concerning HITs.

{-# OPTIONS --cubical #-}

module Issue7629 where

open import Agda.Primitive
open import Agda.Primitive.Cubical using (I; i0; i1)
open import Agda.Builtin.Cubical.Path using (PathP)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

infix 4 _≡_ _<_ _<'_

_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ _ → A)

isProp : Set → Set
isProp A = (x y : A) → x ≡ y

hProp : Set₁
hProp = Σ Set isProp

postulate
  _<_ : Nat → Nat → Set
  isProp< : (x y : Nat) → isProp (x < y)

record Wrap : Set where
  constructor wrap
  field get : Nat
open Wrap

data ℚ : Set where
  [_] : Wrap → ℚ
  eq/ : (wa wb : Wrap) → [ wa ] ≡ [ wb ]

postulate
  lemma< : (wa wb wc : Wrap) → (get wa < get wb) ≡ (get wa < get wc)
  isPropIsProp : ∀ (A : Set) → isProp (isProp A)
  isProp→PathP :
    ∀ {B : I → Set}
    → ((i : I) → isProp (B i))
    → (b0 : B i0) (b1 : B i1)
    → PathP B b0 b1

mutual
  fun₀ : Wrap → ℚ → hProp
  fun₀ (wrap a) [ wrap c ] .fst = a < c
  fun₀ _        [ _ ]      .snd = isProp< _ _
  fun₀ wa (eq/ wb wc i)    .fst = lemma< wa wb wc i
  fun₀ wa (eq/ wb wc i)    .snd =
    isProp→PathP (λ i → isPropIsProp (lemma< wa wb wc i))
                 (isProp< _ _)
                 (isProp< _ _)
                 i

postulate
  toPath : ∀ wa wb (y : ℚ) → fun₀ wa y ≡ fun₀ wb y

_<'_ : ℚ → ℚ → hProp
_<'_ [ wa ]        y = fun₀ wa y
_<'_ (eq/ wa wb i) y = toPath wa wb y i

0ℚ : ℚ
0ℚ = [ wrap zero ]

test : (wa wb : Wrap) → (i : I) → fst (0ℚ <' eq/ wa wb i) → Set
test wa wb i ()

-- WAS: Internal error.

-- Expected error: [ShouldBeEmpty]
-- fst (0ℚ <' eq/ wa wb i) should be empty, but that's not obvious to me
-- when checking the clause left hand side
-- test wa wb i ()
