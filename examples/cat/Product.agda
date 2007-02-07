
module Product where

open import Base
open import Category
open import Unique
open import Dual

module Prod (ℂ : Cat) where

  private
    ℂ' = η-Cat ℂ
    open module C = Cat ℂ'
    open module U = Uniq ℂ'

  data _×_ (A B : Obj) : Set1 where
    prod : (AB : Obj)
	   (π₀ : AB ─→ A)
	   (π₁ : AB ─→ B) ->
	   ((X : Obj)(f : X ─→ A)(g : X ─→ B) ->
	    ∃! \(h : X ─→ AB) -> π₀ ∘ h == f /\ π₁ ∘ h == g
	   ) -> A × B

  Product : {A B : Obj} -> A × B -> Obj
  Product (prod AB _ _ _) = AB

  π₀ : {A B : Obj}(p : A × B) -> Product p ─→ A
  π₀ (prod _ p _ _) = p

  π₁ : {A B : Obj}(p : A × B) -> Product p ─→ B
  π₁ (prod _ _ q _) = q

module Sum (ℂ : Cat) = Prod (η-Cat ℂ op)
    renaming ( _×_     to _+_
	     ; prod    to sum
	     ; Product to Sum
	     ; π₀      to inl
	     ; π₁      to inr
	     )

  

