------------------------------------------------------------------------
-- Environments (heterogeneous collections)
------------------------------------------------------------------------

module Data.Star.Environment (Ty : Set) where

open import Data.Star
open import Data.Star.List
import Data.Star.Decoration as Dec
open Dec hiding (lookup)
open import Logic
open import Data.Unit

-- Contexts, listing the types of all the elements in an environment.

Ctxt : Set
Ctxt = [ Ty ]

-- Variables (de Bruijn indices); pointers into environments.

infix 4 _∋_

_∋_ : Ctxt -> Ty -> Set
Γ ∋ σ = Any (\_ -> ⊤) (_≡_ σ) Γ

vz : forall {Γ σ} -> σ ◅ Γ ∋ σ
vz = this ≡-refl

vs : forall {Γ σ τ} -> Γ ∋ τ -> σ ◅ Γ ∋ τ
vs = that tt

-- Environments. The T function maps types to element types.

Env : (Ty -> Set) -> Ctxt -> Set
Env T Γ = All T Γ

-- A safe lookup function for environments.

lookup : forall {Γ σ} {T : Ty -> Set} ->
         Γ ∋ σ -> Env T Γ -> T σ
lookup i ρ with Dec.lookup i ρ
... | result ≡-refl x = x
