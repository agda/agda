------------------------------------------------------------------------
-- The Agda standard library
--
-- Monads on indexed sets (predicates)
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad.Predicate where

open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Indexed
open import Data.Unit
open import Data.Product
open import Function
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)

------------------------------------------------------------------------

record RawPMonad {i ℓ} {I : Set i} (M : Pt I (i ⊔ ℓ)) :
                 Set (suc i ⊔ suc ℓ) where

  infixl 1 _?>=_ _?>_ _>?>_
  infixr 1 _=<?_ _<?<_

  -- ``Demonic'' operations (the opponent chooses the state).

  field
    return? : ∀ {P} → P ⊆ M P
    _=<?_   : ∀ {P Q} → P ⊆ M Q → M P ⊆ M Q

  _?>=_ : ∀ {P Q} → M P ⊆ const (P ⊆ M Q) ⇒ M Q
  m ?>= f = f =<? m

  _?>=′_ : ∀ {P Q} → M P ⊆ const (∀ j → {_ : P j} → j ∈ M Q) ⇒ M Q
  m ?>=′ f = m ?>= λ {j} p → f j {p}

  _?>_ : ∀ {P Q} → M P ⊆ const (∀ {j} → j ∈ M Q) ⇒ M Q
  m₁ ?> m₂ = m₁ ?>= λ _ → m₂

  join? : ∀ {P} → M (M P) ⊆ M P
  join? m = m ?>= id

  _>?>_ : {P Q R : _} → P ⊆ M Q → Q ⊆ M R → P ⊆ M R
  f >?> g = _=<?_ g ∘ f

  _<?<_ : ∀ {P Q R} → Q ⊆ M R → P ⊆ M Q → P ⊆ M R
  g <?< f = f >?> g

  -- ``Angelic'' operations (the player knows the state).

  rawIMonad : RawIMonad (λ i j A → i ∈ M (const A ∩ ｛ j ｝))
  rawIMonad = record
    { return = λ x → return? (x , refl)
    ; _>>=_  = λ m k → m ?>= λ { {._} (x , refl) → k x }
    }

  open RawIMonad rawIMonad public
