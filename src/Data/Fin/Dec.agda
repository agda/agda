------------------------------------------------------------------------
-- The Agda standard library
--
-- Decision procedures for finite sets and subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Dec where

open import Function
import Data.Bool as Bool
open import Data.Nat.Base hiding (_<_)
open import Data.Vec hiding (_∈_)
open import Data.Vec.Relation.Equality as VecEq
  using () renaming (module PropositionalEquality to PropVecEq)
open import Data.Fin
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Product as Prod
open import Data.Empty
open import Function
import Function.Equivalence as Eq
open import Relation.Binary as B
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U using (Pred)

infix 4 _∈?_

_∈?_ : ∀ {n} x (p : Subset n) → Dec (x ∈ p)
zero  ∈? inside  ∷ p = yes here
zero  ∈? outside ∷ p = no  λ()
suc n ∈? s ∷ p       with n ∈? p
...                  | yes n∈p = yes (there n∈p)
...                  | no  n∉p = no  (n∉p ∘ drop-there)

private

  restrictP : ∀ {p n} → (Fin (suc n) → Set p) → (Fin n → Set p)
  restrictP P f = P (suc f)

  restrict : ∀ {p n} {P : Fin (suc n) → Set p} →
             U.Decidable P → U.Decidable (restrictP P)
  restrict dec f = dec (suc f)

any? : ∀ {n} {P : Fin n → Set} →
       U.Decidable P → Dec (∃ P)
any? {zero}      dec = no λ { (() , _) }
any? {suc n} {P} dec with dec zero | any? (restrict dec)
...                  | yes p | _            = yes (_ , p)
...                  | _     | yes (_ , p') = yes (_ , p')
...                  | no ¬p | no ¬p'       = no helper
  where
  helper : ∄ P
  helper (zero  , p)  = ¬p p
  helper (suc f , p') = ¬p' (_ , p')

nonempty? : ∀ {n} (p : Subset n) → Dec (Nonempty p)
nonempty? p = any? (λ x → x ∈? p)

private

  restrict∈ : ∀ {p q n}
              (P : Fin (suc n) → Set p) {Q : Fin (suc n) → Set q} →
              (∀ {f} → Q f → Dec (P f)) →
              (∀ {f} → restrictP Q f → Dec (restrictP P f))
  restrict∈ _ dec {f} Qf = dec {suc f} Qf

decFinSubset : ∀ {p q n} {P : Fin n → Set p} {Q : Fin n → Set q} →
               U.Decidable Q →
               (∀ {f} → Q f → Dec (P f)) →
               Dec (∀ {f} → Q f → P f)
decFinSubset {n = zero}          _    _    = yes λ{}
decFinSubset {n = suc n} {P} {Q} decQ decP = helper
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
    hlpr zero    q₀ = ⊥-elim (¬q₀ q₀)
    hlpr (suc f) qf = q⟶p qf

all∈? : ∀ {n p} {P : Fin n → Set p} {q} →
        (∀ {f} → f ∈ q → Dec (P f)) →
        Dec (∀ {f} → f ∈ q → P f)
all∈? {q = q} dec = decFinSubset (λ f → f ∈? q) dec

all? : ∀ {n p} {P : Fin n → Set p} →
       U.Decidable P → Dec (∀ f → P f)
all? dec with all∈? {q = ⊤} (λ {f} _ → dec f)
...      | yes ∀p = yes (λ f → ∀p ∈⊤)
...      | no ¬∀p = no  (λ ∀p → ¬∀p (λ {f} _ → ∀p f))

decLift : ∀ {n} {P : Fin n → Set} →
          U.Decidable P → U.Decidable (Lift P)
decLift dec p = all∈? (λ {x} _ → dec x)

private

  restrictSP : ∀ {n} → Side → (Subset (suc n) → Set) → (Subset n → Set)
  restrictSP s P p = P (s ∷ p)

  restrictS : ∀ {n} {P : Subset (suc n) → Set} →
              (s : Side) → U.Decidable P → U.Decidable (restrictSP s P)
  restrictS s dec p = dec (s ∷ p)

anySubset? : ∀ {n} {P : Subset n → Set} →
             U.Decidable P → Dec (∃ P)
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

-- If a decidable predicate P over a finite set is sometimes false,
-- then we can find the smallest value for which this is the case.

¬∀⟶∃¬-smallest :
  ∀ n {p} (P : Fin n → Set p) → U.Decidable P →
  ¬ (∀ i → P i) → ∃ λ i → ¬ P i × ((j : Fin′ i) → P (inject j))
¬∀⟶∃¬-smallest zero    P dec ¬∀iPi = ⊥-elim (¬∀iPi (λ()))
¬∀⟶∃¬-smallest (suc n) P dec ¬∀iPi with dec zero
¬∀⟶∃¬-smallest (suc n) P dec ¬∀iPi | no ¬P0 = (zero , ¬P0 , λ ())
¬∀⟶∃¬-smallest (suc n) P dec ¬∀iPi | yes P0 =
  Prod.map suc (Prod.map id extend′) $
    ¬∀⟶∃¬-smallest n (λ n → P (suc n)) (dec ∘ suc) (¬∀iPi ∘ extend)
  where
  extend : (∀ i → P (suc i)) → (∀ i → P i)
  extend ∀iP[1+i] zero    = P0
  extend ∀iP[1+i] (suc i) = ∀iP[1+i] i

  extend′ : ∀ {i : Fin n} →
            ((j : Fin′ i) → P (suc (inject j))) →
            ((j : Fin′ (suc i)) → P (inject j))
  extend′ g zero    = P0
  extend′ g (suc j) = g j


-- When P is a decidable predicate over a finite set the following
-- lemma can be proved.

¬∀⟶∃¬ : ∀ n {p} (P : Fin n → Set p) → U.Decidable P →
        ¬ (∀ i → P i) → ∃ λ i → ¬ P i
¬∀⟶∃¬ n P dec ¬P = Prod.map id proj₁ $ ¬∀⟶∃¬-smallest n P dec ¬P

-- Decision procedure for _⊆_ (obtained via the natural lattice
-- order).

infix 4 _⊆?_

_⊆?_ : ∀ {n} → B.Decidable (_⊆_ {n = n})
p₁ ⊆? p₂ =
  Dec.map (Eq.sym NaturalPoset.orders-equivalent) $
  Dec.map′ PropVecEq.to-≡ PropVecEq.from-≡ $
  VecEq.DecidableEquality._≟_ Bool.decSetoid p₁ (p₁ ∩ p₂)
