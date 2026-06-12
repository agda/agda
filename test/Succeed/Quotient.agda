{-# OPTIONS --safe --quotients --polarity --hidden-argument-puns #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Quotient
open import Agda.Builtin.Unit
open import Agda.Primitive

private variable
  a       : Level
  A B     : Set _
  p x y z : A

-- Symmetry.

sym : x ≡ y → y ≡ x
sym refl = refl

-- Transitivity.

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- A simplification lemma.

trans-sym : trans p (sym p) ≡ refl
trans-sym {p = refl} = refl

-- The property of being a proposition.

Is-proposition : Set a → Set a
Is-proposition A = (x y : A) → x ≡ y

opaque

  -- Propositions are sets.

  Is-proposition→Is-set : Is-proposition A → Is-set A
  Is-proposition→Is-set {A} prop p q =
    trans (sym (prop′≡ p)) (prop′≡ q)
    where
    prop′ : (x y : A) → x ≡ y
    prop′ x y = trans (prop x y) (sym (prop y y))

    prop′≡ : (p : x ≡ y) → prop′ x y ≡ p
    prop′≡ refl = trans-sym

-- Propositional truncation.

∥_∥ : Set a → Set a
∥ A ∥ = A / λ _ _ → ⊤

-- The point constructor.

∣_∣ : A → ∥ A ∥
∣ x ∣ = [ x ]

-- The propositional truncation operator returns propositions.

@0 prop : Is-proposition ∥ A ∥
prop x y =
  qrec (λ y → x ≡ y)
    (λ y →
       qrec (λ x → x ≡ [ y ]) (λ _ → resp tt) (λ _ → set _ _)
         (λ _ → Is-proposition→Is-set set) x)
    (λ _ → set _ _) (λ _ → Is-proposition→Is-set set) y

-- A recursor for ∥_∥.

trec : @0 Is-proposition B → (A → B) → ∥ A ∥ → B
trec prop f =
  qrec _ f (λ _ → prop _ _) (λ _ → Is-proposition→Is-set prop)

-- The recursor computes correctly.

_ :
  {@0 prop : Is-proposition B}
  {f : A → B} →
  trec prop f ∣ x ∣ ≡ f x
_ = refl
