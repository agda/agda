-- Andreas, 2026-05-01, issue #7629
-- Internal error due to bug in clause compiler concerning HITs.
-- Regression test.

{-# OPTIONS --cubical #-}

module Issue7629Regression where

open import Agda.Primitive using (lzero; lsuc; Set)
open import Agda.Primitive.Cubical using (I; i0; i1)
open import Agda.Builtin.Cubical.Path using (PathP)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

_==_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_==_ {A = A} = PathP (λ _ → A)

isProp : ∀ {ℓ} → Set ℓ → Set ℓ
isProp A = (x y : A) → x == y

hProp : ∀ ℓ → Set (lsuc ℓ)
hProp ℓ = Σ (Set ℓ) isProp

data Z : Set where
  pos : Nat → Z

Pair : Set
Pair = Σ Z (λ _ → Nat)

postulate
  mul : Z → Z → Z
  lt : Z → Z → Set
  isPropLt : (x y : Z) → isProp (lt x y)
  natToZ : Nat → Z

_~_ : Pair → Pair → Set
(a , b) ~ (c , d) = mul a (natToZ d) == mul c (natToZ b)

data Rat : Set where
  [_] : Pair → Rat
  eq/ : (ab cd : Pair) → ab ~ cd → [ ab ] == [ cd ]

postulate
  lemma :
      ((a , b) (c , d) (e , f) : Pair)
    → mul c (natToZ f) == mul e (natToZ d)
    → lt (mul a (natToZ d)) (mul c (natToZ b))
    == lt (mul a (natToZ f)) (mul e (natToZ b))

  isPropIsProp : ∀ {ℓ} {A : Set ℓ} → isProp (isProp A)

  isPropToPathP :
      ∀ {ℓ} {B : I → Set ℓ}
    → ((i : I) → isProp (B i))
    → (b0 : B i0) (b1 : B i1)
    → PathP B b0 b1

mutual
  fun0 : Pair → Rat → hProp lzero
  less : Rat → Rat → hProp lzero

  postulate
    toPath : ∀ ab cd (x : ab ~ cd) (y : Rat) → fun0 ab y == fun0 cd y

  fun0 (a , b) [ c , d ] .fst = lt (mul a (natToZ d)) (mul c (natToZ b))
  fun0 _       [ _ ]     .snd = isPropLt _ _
  fun0 ab (eq/ cd ef cfEqEd i) = record
    { fst = lemma ab cd ef cfEqEd i
    ; snd = isPropToPathP (λ i → isPropIsProp {A = lemma ab cd ef cfEqEd i})
                          (isPropLt _ _)
                          (isPropLt _ _) i
    }

  less [ ab ] y = fun0 ab y
  less (eq/ ab cd adEqCb i) y = toPath ab cd adEqCb y i

zeroRat : Rat
zeroRat = [ pos zero , zero ]

test : Σ Rat (λ q → fst (less zeroRat q)) → Set
test ([ q ] , q+) = Rat
test (eq/ ab cd adEqCb i , q+) = Rat

-- Should succeed.
