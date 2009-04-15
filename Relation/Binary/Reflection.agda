------------------------------------------------------------------------
-- Helpers intended to ease the development of "tactics" which use
-- proof by reflection
------------------------------------------------------------------------

open import Relation.Binary
open import Data.Nat
open import Data.Fin
open import Data.Vec as Vec
open import Data.Function

-- Think of the parameters as follows:
--
-- * Expr:    A representation of code.
-- * var:     The Expr type should support a notion of variables.
-- * ⟦_⟧:     Computes the semantics of an expression. Takes an
--            environment mapping variables to something.
-- * ⟦_⇓⟧:    Computes the semantics of the normal form of the
--            expression.
-- * correct: Normalisation preserves the semantics.
--
-- Given these parameters two "tactics" are returned, prove and solve.
--
-- For an example of the use of this module, see Algebra.RingSolver.

module Relation.Binary.Reflection
         {Expr : ℕ → Set} {A}
         Sem
         (var : ∀ {n} → Fin n → Expr n)
         (⟦_⟧ ⟦_⇓⟧ : ∀ {n} → Expr n → Vec A n → Setoid.carrier Sem)
         (correct : ∀ {n} (e : Expr n) ρ →
                    ⟦ e ⇓⟧ ρ ⟨ Setoid._≈_ Sem ⟩₁ ⟦ e ⟧ ρ)
         where

open import Data.Vec.N-ary
open import Data.Product
import Relation.Binary.EqReasoning as Eq

open Setoid Sem
open Eq Sem

-- If two normalised expressions are semantically equal, then their
-- non-normalised forms are also equal.

prove : ∀ {n} (ρ : Vec A n) e₁ e₂ →
        ⟦ e₁ ⇓⟧ ρ ≈ ⟦ e₂ ⇓⟧ ρ →
        ⟦ e₁  ⟧ ρ ≈ ⟦ e₂  ⟧ ρ
prove ρ e₁ e₂ hyp = begin
  ⟦ e₁  ⟧ ρ ≈⟨ sym (correct e₁ ρ) ⟩
  ⟦ e₁ ⇓⟧ ρ ≈⟨ hyp ⟩
  ⟦ e₂ ⇓⟧ ρ ≈⟨ correct e₂ ρ ⟩
  ⟦ e₂  ⟧ ρ ∎

-- Applies the function to all possible "variables".

close : ∀ {A} n → N-ary n (Expr n) A → A
close n f = f $ⁿ Vec.map var (allFin n)

-- A variant of prove which should in many cases be easier to use,
-- because variables and environments are handled in a less explicit
-- way.
--
-- If the type signature of solve is a bit daunting, then it may be
-- helpful to instantiate n with a small natural number and normalise
-- the remainder of the type.

solve : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
  Eqʰ n _≈_ (curryⁿ ⟦ proj₁ (close n f) ⇓⟧) (curryⁿ ⟦ proj₂ (close n f) ⇓⟧) →
  Eq  n _≈_ (curryⁿ ⟦ proj₁ (close n f)  ⟧) (curryⁿ ⟦ proj₂ (close n f)  ⟧)
solve n f hyp =
  curryⁿ-pres ⟦ proj₁ (close n f) ⟧ ⟦ proj₂ (close n f) ⟧
    (λ ρ → prove ρ (proj₁ (close n f)) (proj₂ (close n f))
             (curryⁿ-pres⁻¹ ⟦ proj₁ (close n f) ⇓⟧ ⟦ proj₂ (close n f) ⇓⟧
                            (Eqʰ-to-Eq n hyp) ρ))

-- A variant of _,_ which is intended to make uses of solve look a
-- bit nicer.

infix 4 _⊜_

_⊜_ : ∀ {A} → A → A → A × A
_⊜_ = _,_
