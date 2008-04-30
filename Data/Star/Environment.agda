------------------------------------------------------------------------
-- Environments (heterogeneous collections)
------------------------------------------------------------------------

module Data.Star.Environment (Ty : Set) where

open import Data.Star
open import Data.Star.List
open import Data.Star.Decoration
open import Data.Star.Pointer
open import Data.Unit
open import Relation.Binary.PropositionalEquality

-- Contexts, listing the types of all the elements in an environment.

Ctxt : Set
Ctxt = [ Ty ]

-- Variables (de Bruijn indices); pointers into environments.

infix 4 _∋_

_∋_ : Ctxt -> Ty -> Set
Γ ∋ σ = Any (\_ -> ⊤) (_≡_ σ) Γ

vz : forall {Γ σ} -> Γ ▻ σ ∋ σ
vz = this ≡-refl

vs : forall {Γ σ τ} -> Γ ∋ τ -> Γ ▻ σ ∋ τ
vs = that tt

-- Environments. The T function maps types to element types.

Env : (Ty -> Set) -> Ctxt -> Set
Env T Γ = All T Γ

-- A safe lookup function for environments.

Env-lookup : forall {Γ σ} {T : Ty -> Set} ->
         Γ ∋ σ -> Env T Γ -> T σ
Env-lookup i ρ with lookup i ρ
... | result ≡-refl x = x
