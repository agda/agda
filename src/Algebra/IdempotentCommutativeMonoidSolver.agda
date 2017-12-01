------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for equations in commutative monoids
--
-- Adapted from Algebra.Monoid-solver
------------------------------------------------------------------------

open import Algebra

open import Data.Bool.Base as Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe
  using (Maybe; decToMaybe; From-just; from-just)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; proj₁; proj₂; uncurry)
open import Data.Vec using (Vec; []; _∷_; lookup; replicate)

open import Function using (_∘_)

import Relation.Binary.EqReasoning as EqReasoning
import Relation.Binary.Reflection  as Reflection
import Relation.Nullary.Decidable  as Dec
import Data.Vec.Relation.Pointwise as Pointwise

open import Relation.Binary.PropositionalEquality as P using (_≡_; decSetoid)
open import Relation.Nullary using (Dec)

module Algebra.IdempotentCommutativeMonoidSolver
  {m₁ m₂} (M : IdempotentCommutativeMonoid m₁ m₂) where

open IdempotentCommutativeMonoid M
open EqReasoning setoid

------------------------------------------------------------------------
-- Monoid expressions

-- There is one constructor for every operation, plus one for
-- variables; there may be at most n variables.

infixr 5 _⊕_
infixr 10 _•_

data Expr (n : ℕ) : Set where
  var : Fin n → Expr n
  id  : Expr n
  _⊕_ : Expr n → Expr n → Expr n

-- An environment contains one value for every variable.

Env : ℕ → Set _
Env n = Vec Carrier n

-- The semantics of an expression is a function from an environment to
-- a value.

⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
⟦ var x   ⟧ ρ = lookup x ρ
⟦ id      ⟧ ρ = ε
⟦ e₁ ⊕ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a vector of bits (a set).

Normal : ℕ → Set
Normal n = Vec Bool n

-- The semantics of a normal form.

⟦_⟧⇓ : ∀ {n} → Normal n → Env n → Carrier
⟦ []    ⟧⇓ _ = ε
⟦ b ∷ v ⟧⇓ (a ∷ ρ) = if b then a ∙ (⟦ v ⟧⇓ ρ) else (⟦ v ⟧⇓ ρ)

------------------------------------------------------------------------
-- Constructions on normal forms

-- The empty bag.

empty : ∀{n} → Normal n
empty = replicate false

-- A singleton bag.

sg : ∀{n} (i : Fin n) → Normal n
sg zero    = true ∷ empty
sg (suc i) = false ∷ sg i

-- The composition of normal forms.

_•_  : ∀{n} (v w : Normal n) → Normal n
[]      • []      = []
(l ∷ v) • (m ∷ w) = (l ∨ m) ∷ v • w

------------------------------------------------------------------------
-- Correctness of the constructions on normal forms

-- The empty bag stands for the unit ε.

empty-correct : ∀{n} (ρ : Env n) → ⟦ empty ⟧⇓ ρ ≈ ε
empty-correct [] = refl
empty-correct (a ∷ ρ) = empty-correct ρ

-- The singleton bag stands for a single variable.

sg-correct : ∀{n} (x : Fin n) (ρ : Env n) →  ⟦ sg x ⟧⇓ ρ ≈ lookup x ρ
sg-correct zero (x ∷ ρ) = begin
    x ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ ∙-cong refl (empty-correct ρ) ⟩
    x ∙ ε              ≈⟨ proj₂ identity _ ⟩
    x                  ∎
sg-correct (suc x) (m ∷ ρ) = sg-correct x ρ

-- Normal form composition corresponds to the composition of the monoid.

flip12 : ∀ a b c → a ∙ (b ∙ c) ≈ b ∙ (a ∙ c)
flip12 a b c = begin
    a ∙ (b ∙ c)  ≈⟨ sym (assoc _ _ _) ⟩
    (a ∙ b) ∙ c  ≈⟨ ∙-cong (comm _ _) refl ⟩
    (b ∙ a) ∙ c  ≈⟨ assoc _ _ _ ⟩
    b ∙ (a ∙ c)  ∎

distr : ∀ a b c → a ∙ (b ∙ c) ≈ (a ∙ b) ∙ (a ∙ c)
distr a b c = begin
    a ∙ (b ∙ c)  ≈⟨ ∙-cong (sym (idem a)) refl ⟩
    (a ∙ a) ∙ (b ∙ c)  ≈⟨ assoc _ _ _ ⟩
    a ∙ (a ∙ (b ∙ c))  ≈⟨ ∙-cong refl (sym (assoc _ _ _)) ⟩
    a ∙ ((a ∙ b) ∙ c)  ≈⟨ ∙-cong refl (∙-cong (comm _ _) refl) ⟩
    a ∙ ((b ∙ a) ∙ c)  ≈⟨ ∙-cong refl (assoc _ _ _) ⟩
    a ∙ (b ∙ (a ∙ c))  ≈⟨ sym (assoc _ _ _) ⟩
    (a ∙ b) ∙ (a ∙ c)  ∎

comp-correct : ∀ {n} (v w : Normal n) (ρ : Env n) →
              ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
comp-correct [] [] ρ = sym (proj₁ identity _)
comp-correct (true ∷ v) (true ∷ w) (a ∷ ρ) =
  trans (∙-cong refl (comp-correct v w ρ)) (distr _ _ _)
comp-correct (true ∷ v) (false ∷ w) (a ∷ ρ) =
  trans (∙-cong refl (comp-correct v w ρ)) (sym (assoc _ _ _))
comp-correct (false ∷ v) (true ∷ w) (a ∷ ρ) =
  trans (∙-cong refl (comp-correct v w ρ)) (flip12 _ _ _)
comp-correct (false ∷ v) (false ∷ w) (a ∷ ρ) =
  comp-correct v w ρ

------------------------------------------------------------------------
-- Normalization

-- A normaliser.

normalise : ∀ {n} → Expr n → Normal n
normalise (var x)   = sg x
normalise id        = empty
normalise (e₁ ⊕ e₂) = normalise e₁ • normalise e₂

-- The normaliser preserves the semantics of the expression.

normalise-correct : ∀ {n} (e : Expr n) (ρ : Env n) →
    ⟦ normalise e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ
normalise-correct (var x)   ρ = sg-correct x ρ
normalise-correct id        ρ = empty-correct ρ
normalise-correct (e₁ ⊕ e₂) ρ =  begin

    ⟦ normalise e₁ • normalise e₂ ⟧⇓ ρ

  ≈⟨ comp-correct (normalise e₁) (normalise e₂) ρ ⟩

    ⟦ normalise e₁ ⟧⇓ ρ ∙ ⟦ normalise e₂ ⟧⇓ ρ

  ≈⟨ ∙-cong (normalise-correct e₁ ρ) (normalise-correct e₂ ρ) ⟩

    ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ
  ∎

------------------------------------------------------------------------
-- "Tactics"

open module R = Reflection
                  setoid var ⟦_⟧ (⟦_⟧⇓ ∘ normalise) normalise-correct
  public using (solve; _⊜_)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : ∀ {n} (nf₁ nf₂ : Normal n) → Dec (nf₁ ≡ nf₂)
nf₁ ≟ nf₂ = Dec.map Pointwise-≡ (decidable Bool._≟_ nf₁ nf₂)
  where open Pointwise

-- We can also give a sound, but not necessarily complete, procedure
-- for determining if two expressions have the same semantics.

prove′ : ∀ {n} (e₁ e₂ : Expr n) → Maybe (∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ)
prove′ e₁ e₂ =
  Maybe.map lemma (decToMaybe (normalise e₁ ≟ normalise e₂))
  where
  lemma : normalise e₁ ≡ normalise e₂ → ∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ
  lemma eq ρ =
    R.prove ρ e₁ e₂ (begin
      ⟦ normalise e₁ ⟧⇓ ρ  ≡⟨ P.cong (λ e → ⟦ e ⟧⇓ ρ) eq ⟩
      ⟦ normalise e₂ ⟧⇓ ρ  ∎)

-- This procedure can be combined with from-just.

prove : ∀ n (e₁ e₂ : Expr n) →
  From-just (∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ) (prove′  e₁ e₂)
prove _ e₁ e₂ = from-just (prove′ e₁ e₂)

-- prove : ∀ n (es : Expr n × Expr n) →
--         From-just (∀ ρ → ⟦ proj₁ es ⟧ ρ ≈ ⟦ proj₂ es ⟧ ρ)
--                   (uncurry prove′ es)
-- prove _ = from-just ∘ uncurry prove′

-- -}
