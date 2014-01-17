------------------------------------------------------------------------
-- The Agda standard library
--
-- Applicative functors on indexed sets (predicates)
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

module Category.Applicative.Predicate where

open import Category.Functor.Predicate
open import Data.Product
open import Function
open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)

------------------------------------------------------------------------

record RawPApplicative {i ℓ} {I : Set i} (F : Pt I ℓ) :
                       Set (i ⊔ suc ℓ) where
  infixl 4 _⊛_ _<⊛_ _⊛>_
  infix  4 _⊗_

  field
    pure : ∀ {P} → P ⊆ F P
    _⊛_  : ∀ {P Q} → F (P ⇒ Q) ⊆ F P ⇒ F Q

  rawPFunctor : RawPFunctor F
  rawPFunctor = record
    { _<$>_ = λ g x → pure g ⊛ x
    }

  private
    open module RF = RawPFunctor rawPFunctor public

  _<⊛_ : ∀ {P Q} → F P ⊆ const (∀ {j} → F Q j) ⇒ F P
  x <⊛ y = const <$> x ⊛ y

  _⊛>_ : ∀ {P Q} → const (∀ {i} → F P i) ⊆ F Q ⇒ F Q
  x ⊛> y = flip const <$> x ⊛ y

  _⊗_ : ∀ {P Q} → F P ⊆ F Q ⇒ F (P ∩ Q)
  x ⊗ y = (_,_) <$> x ⊛ y

  zipWith : ∀ {P Q R} → (P ⊆ Q ⇒ R) → F P ⊆ F Q ⇒ F R
  zipWith f x y = f <$> x ⊛ y
