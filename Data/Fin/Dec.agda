------------------------------------------------------------------------
-- Decision procedures for finite sets and subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Dec where

open import Data.Function
open import Data.Nat
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Fin.Subset.Props
open import Data.Product
open import Data.Empty
open import Relation.Nullary

infix 4 _∈?_

_∈?_ : ∀ {n} x (p : Subset n) → Dec (x ∈ p)
zero  ∈? inside  ∷ p = yes here
zero  ∈? outside ∷ p = no  λ()
suc n ∈? s ∷ p       with n ∈? p
...                  | yes n∈p = yes (there n∈p)
...                  | no  n∉p = no  (n∉p ∘ drop-there)

private

  restrictP : ∀ {n} → (Fin (suc n) → Set) → (Fin n → Set)
  restrictP P f = P (suc f)

  restrict : ∀ {n} {P : Fin (suc n) → Set} →
             (∀ f → Dec (P f)) →
             (∀ f → Dec (restrictP P f))
  restrict dec f = dec (suc f)

any? : ∀ {n} {P : Fin n → Set} →
       ((f : Fin n) → Dec (P f)) →
       Dec (∃ P)
any? {zero}  {P} dec = no ((¬ Fin 0 ∶ λ()) ∘ proj₁)
any? {suc n} {P} dec with dec zero | any? (restrict dec)
...                  | yes p | _            = yes (_ , p)
...                  | _     | yes (_ , p') = yes (_ , p')
...                  | no ¬p | no ¬p'       = no helper
  where
  helper : ∄ P
  helper (zero  , p)  = ¬p p
  helper (suc f , p') = contradiction (_ , p') ¬p'

nonempty? : ∀ {n} (p : Subset n) → Dec (Nonempty p)
nonempty? p = any? (λ x → x ∈? p)

private

  restrict∈ : ∀ {n} P {Q : Fin (suc n) → Set} →
              (∀ {f} → Q f → Dec (P f)) →
              (∀ {f} → restrictP Q f → Dec (restrictP P f))
  restrict∈ _ dec {f} Qf = dec {suc f} Qf

decFinSubset : ∀ {n} {P Q : Fin n → Set} →
               (∀ f → Dec (Q f)) →
               (∀ {f} → Q f → Dec (P f)) →
               Dec (∀ {f} → Q f → P f)
decFinSubset {zero}          _    _    = yes λ{}
decFinSubset {suc n} {P} {Q} decQ decP = helper
  where
  helper : Dec (∀ {f} → Q f → P f)
  helper with decFinSubset (restrict decQ) (restrict∈ P decP)
  helper | no ¬q⟶p = no (λ q⟶p → ¬q⟶p (λ {f} q → q⟶p {suc f} q))
  helper | yes q⟶p with decQ zero
  helper | yes q⟶p | yes q₀ with decP q₀
  helper | yes q⟶p | yes q₀ | no ¬p₀ = no (λ q⟶p → ¬p₀ (q⟶p {zero} q₀))
  helper | yes q⟶p | yes q₀ | yes p₀ = yes (λ {_} → hlpr _)
    where
    hlpr : ∀ f → Q f → P f
    hlpr zero    _  = p₀
    hlpr (suc f) qf = q⟶p qf
  helper | yes q⟶p | no ¬q₀ = yes (λ {_} → hlpr _)
    where
    hlpr : ∀ f → Q f → P f
    hlpr zero    q₀ = contradiction q₀ ¬q₀
    hlpr (suc f) qf = q⟶p qf

all∈? : ∀ {n} {P : Fin n → Set} {q} →
        (∀ {f} → f ∈ q → Dec (P f)) →
        Dec (∀ {f} → f ∈ q → P f)
all∈? {q = q} dec = decFinSubset (λ f → f ∈? q) dec

all? : ∀ {n} {P : Fin n → Set} →
       (∀ f → Dec (P f)) →
       Dec (∀ f → P f)
all? dec with all∈? {q = all inside} (λ {f} _ → dec f)
...      | yes ∀p = yes (λ f → ∀p (allInside f))
...      | no ¬∀p = no  (λ ∀p → ¬∀p (λ {f} _ → ∀p f))

lift : ∀ {n} {P : Fin n → Set} →
       (∀ x → Dec (P x)) →
       (∀ p → Dec (Lift P p))
lift dec p = all∈? (λ {x} _ → dec x)

private

  restrictSP : ∀ {n} → Side → (Subset (suc n) → Set) → (Subset n → Set)
  restrictSP s P p = P (s ∷ p)

  restrictS : ∀ {n} {P : Subset (suc n) → Set} →
              (s : Side) →
              (∀ p → Dec (P p)) →
              (∀ p → Dec (restrictSP s P p))
  restrictS s dec p = dec (s ∷ p)

anySubset? : ∀ {n} {P : Subset n → Set} →
             (∀ s → Dec (P s)) →
             Dec (∃ P)
anySubset? {zero} {P} dec with dec []
... | yes P[] = yes (_ , P[])
... | no ¬P[] = no helper
  where
  helper : ∄ P
  helper ([] , P[]) = ¬P[] P[]
anySubset? {suc n} {P} dec with anySubset? (restrictS inside  dec)
                              | anySubset? (restrictS outside dec)
... | yes (_ , Pp) | _            = yes (_ , Pp)
... | _            | yes (_ , Pp) = yes (_ , Pp)
... | no ¬Pp       | no ¬Pp'      = no helper
    where
    helper : ∄ P
    helper (inside  ∷ p , Pp)  = ¬Pp  (_ , Pp)
    helper (outside ∷ p , Pp') = ¬Pp' (_ , Pp')
