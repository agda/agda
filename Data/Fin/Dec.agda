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

_∈?_ : forall {n} x (p : Subset n) -> Dec (x ∈ p)
zero  ∈? inside  ∷ p = yes here
zero  ∈? outside ∷ p = no  \()
suc n ∈? s ∷ p       with n ∈? p
...                  | yes n∈p = yes (there n∈p)
...                  | no  n∉p = no  (n∉p ∘ drop-there)

private

  restrictP : forall {n} -> (Fin (suc n) -> Set) -> (Fin n -> Set)
  restrictP P f = P (suc f)

  restrict
    :  forall {n} {P : Fin (suc n) -> Set}
    -> (forall f -> Dec (P f))
    -> (forall f -> Dec (restrictP P f))
  restrict dec f = dec (suc f)

any? :  forall {n} {P : Fin n -> Set}
     -> ((f : Fin n) -> Dec (P f))
     -> Dec (∃ P)
any? {zero}  {P} dec = no ((\()) ∘ proj₁)
any? {suc n} {P} dec with dec zero | any? (restrict dec)
...                  | yes p | _            = yes (_ , p)
...                  | _     | yes (_ , p') = yes (_ , p')
...                  | no ¬p | no ¬p'       = no helper
  where
  helper : ∄ P
  helper (zero  , p)  = ¬p p
  helper (suc f , p') = contradiction (_ , p') ¬p'

nonempty? : forall {n} (p : Subset n) -> Dec (Nonempty p)
nonempty? p = any? (\x -> x ∈? p)

private

  restrict∈
    :  forall {n} P {Q : Fin (suc n) -> Set}
    -> (forall {f} -> Q f -> Dec (P f))
    -> (forall {f} -> restrictP Q f -> Dec (restrictP P f))
  restrict∈ _ dec {f} Qf = dec {suc f} Qf

decFinSubset
  :  forall {n} {P Q : Fin n -> Set}
  -> (forall f -> Dec (Q f))
  -> (forall {f} -> Q f -> Dec (P f))
  -> Dec (forall {f} -> Q f -> P f)
decFinSubset {zero}          _    _    = yes \{}
decFinSubset {suc n} {P} {Q} decQ decP = helper
  where
  helper : Dec (forall {f} -> Q f -> P f)
  helper with decFinSubset (restrict decQ) (restrict∈ P decP)
  helper | no ¬q⟶p = no (\q⟶p -> ¬q⟶p (\{f} q -> q⟶p {suc f} q))
  helper | yes q⟶p with decQ zero
  helper | yes q⟶p | yes q₀ with decP q₀
  helper | yes q⟶p | yes q₀ | no ¬p₀ = no (\q⟶p -> ¬p₀ (q⟶p {zero} q₀))
  helper | yes q⟶p | yes q₀ | yes p₀ = yes (\{_} -> hlpr _)
    where
    hlpr : forall f -> Q f -> P f
    hlpr zero    _  = p₀
    hlpr (suc f) qf = q⟶p qf
  helper | yes q⟶p | no ¬q₀ = yes (\{_} -> hlpr _)
    where
    hlpr : forall f -> Q f -> P f
    hlpr zero    q₀ = contradiction q₀ ¬q₀
    hlpr (suc f) qf = q⟶p qf

all∈?
  :  forall {n} {P : Fin n -> Set} {q}
  -> (forall {f} -> f ∈ q -> Dec (P f))
  -> Dec (forall {f} -> f ∈ q -> P f)
all∈? {q = q} dec = decFinSubset (\f -> f ∈? q) dec

all? :  forall {n} {P : Fin n -> Set}
     -> (forall f -> Dec (P f))
     -> Dec (forall f -> P f)
all? dec with all∈? {q = all inside} (\{f} _ -> dec f)
...      | yes ∀p = yes (\f -> ∀p (allInside f))
...      | no ¬∀p = no  (\ ∀p -> ¬∀p (\{f} _ -> ∀p f))

lift :  forall {n} {P : Fin n -> Set}
     -> (forall x -> Dec (P x))
     -> (forall p -> Dec (Lift P p))
lift dec p = all∈? (\{x} _ -> dec x)

private

  restrictSP
    :  forall {n}
    -> Side -> (Subset (suc n) -> Set) -> (Subset n -> Set)
  restrictSP s P p = P (s ∷ p)

  restrictS
    :  forall {n} {P : Subset (suc n) -> Set}
    -> (s : Side)
    -> (forall p -> Dec (P p))
    -> (forall p -> Dec (restrictSP s P p))
  restrictS s dec p = dec (s ∷ p)

anySubset? :  forall {n} {P : Subset n -> Set}
           -> (forall s -> Dec (P s))
           -> Dec (∃ P)
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
