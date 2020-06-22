
{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path using (_≡_)
open import Agda.Builtin.Sigma using (Σ; fst; _,_)

postulate
  Is-proposition : Set → Set
  subst          : ∀ {A : Set} (P : A → Set) {x y} → x ≡ y → P x → P y

Proposition : Set₁
Proposition = Σ _ Is-proposition

data _/_ (A : Set) (R : A → A → Proposition) : Set where
  [_]  : A → A / R
  resp : ∀ {x y} → fst (R x y) → [ x ] ≡ [ y ]

variable
  A : Set
  R : A → A → Proposition

postulate
  F : (P : A / R → Set)
      (p-[] : ∀ x → P [ x ]) →
      (∀ {x y} (r : fst (R x y)) → subst P (resp r) (p-[] x) ≡ p-[] y) →
      Set

F' : (A : Set)
     (R : A → A → Proposition)
     (P : A / R → Set)
     (p-[] : ∀ x → P [ x ]) →
     (∀ {x y} (r : fst (R x y)) → subst P (resp r) (p-[] x) ≡ p-[] y) →
     Set
F' A R = F {A = A} {R = R}
