{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive
open import Agda.Primitive.Cubical

variable
  a p         : Level
  A           : Set a
  P           : A → Set p
  eq₁ u v x y : A

refl : x ≡ x
refl {x = x} = λ _ → x

subst : (P : A → Set p) → x ≡ y → P x → P y
subst P x≡y p = primTransp (λ i → P (x≡y i)) i0 p

hcong :
  (f : (x : A) → P x) (x≡y : x ≡ y) →
  PathP (λ i → P (x≡y i)) (f x) (f y)
hcong f x≡y = λ i → f (x≡y i)

dcong :
  (f : (x : A) → P x) (x≡y : x ≡ y) →
  subst P x≡y (f x) ≡ f y
dcong {P = P} f x≡y = λ i →
  primTransp (λ j → P (x≡y (primIMax i j))) i (f (x≡y i))

-- This lemma is due to Anders Mörtberg.

lemma₁ :
  {P : I → Set p} {p : P i0} {q : P i1} →
  PathP P p q ≡ (primTransp P i0 p ≡ q)
lemma₁ {P = P} {p = p} {q = q} = λ i →
  PathP
    (λ j → P (primIMax i j))
    (primTransp (λ j → P (primIMin i j)) (primINeg i) p)
    q

data 𝕊¹ : Set where
  base : 𝕊¹
  loop : base ≡ base

postulate

  Q : 𝕊¹ → Set
  b : Q base
  ℓ : subst Q loop b ≡ b

lemma₂ :
  {eq : x ≡ y} →
  subst Q eq u ≡ v →
  PathP (λ i → Q (eq i)) u v
lemma₂ = subst (λ A → A → PathP _ _ _) lemma₁ (λ x → x)

lemma₃ : (x : 𝕊¹) → Q x
lemma₃ base     = b
lemma₃ (loop i) = lemma₂ ℓ i

postulate

  lemma₄ :
    (eq₂ : subst Q eq₁ (lemma₃ x) ≡ lemma₃ y) →
    hcong lemma₃ eq₁ ≡ lemma₂ eq₂ →
    dcong lemma₃ eq₁ ≡ eq₂


works : dcong lemma₃ loop ≡ ℓ
works = lemma₄ ℓ refl


-- "injectivity" of lemma₃ was the problem
should-work-too : dcong lemma₃ loop ≡ ℓ
should-work-too = lemma₄ _ refl
