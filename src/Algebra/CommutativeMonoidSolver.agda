------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for equations in commutative monoids
--
-- Adapted from Algebra.Monoid-solver
------------------------------------------------------------------------

open import Algebra

open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe
  using (Maybe; decToMaybe; From-just; from-just)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_)
open import Data.Nat.GeneralisedArithmetic using (fold)
open import Data.Product using (_×_; proj₁; proj₂; uncurry)
open import Data.Vec using (Vec; []; _∷_; lookup; replicate)

open import Function using (_∘_)

import Relation.Binary.EqReasoning  as EqReasoning
import Relation.Binary.Reflection   as Reflection
import Relation.Nullary.Decidable   as Dec
import Data.Vec.Relation.Pointwise as Pointwise

open import Relation.Binary.PropositionalEquality as P using (_≡_; decSetoid)
open import Relation.Nullary using (Dec)

module Algebra.CommutativeMonoidSolver {m₁ m₂} (M : CommutativeMonoid m₁ m₂) where

open CommutativeMonoid M
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

-- A normal form is a vector of multiplicities (a bag).

Normal : ℕ → Set
Normal n = Vec ℕ n

-- The semantics of a normal form.

⟦_⟧⇓ : ∀ {n} → Normal n → Env n → Carrier
⟦ []    ⟧⇓ _ = ε
⟦ n ∷ v ⟧⇓ (a ∷ ρ) = fold (⟦ v ⟧⇓ ρ) (λ b → a ∙ b) n

------------------------------------------------------------------------
-- Constructions on normal forms

-- The empty bag.

empty : ∀{n} → Normal n
empty = replicate 0

-- A singleton bag.

sg : ∀{n} (i : Fin n) → Normal n
sg zero    = 1 ∷ empty
sg (suc i) = 0 ∷ sg i

-- The composition of normal forms.

_•_  : ∀{n} (v w : Normal n) → Normal n
[]      • []      = []
(l ∷ v) • (m ∷ w) = l + m ∷ v • w

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

comp-correct : ∀ {n} (v w : Normal n) (ρ : Env n) →
              ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
comp-correct [] [] ρ =  sym (proj₁ identity _)
comp-correct (l ∷ v) (m ∷ w) (a ∷ ρ) = lemma l m (comp-correct v w ρ)
  where
    flip12 : ∀ a b c → a ∙ (b ∙ c) ≈ b ∙ (a ∙ c)
    flip12 a b c = begin
        a ∙ (b ∙ c)  ≈⟨ sym (assoc _ _ _) ⟩
        (a ∙ b) ∙ c  ≈⟨ ∙-cong (comm _ _) refl ⟩
        (b ∙ a) ∙ c  ≈⟨ assoc _ _ _ ⟩
        b ∙ (a ∙ c)  ∎
    lemma : ∀ l m {d b c} (p : d ≈ b ∙ c) →
      fold d (a ∙_) (l + m) ≈ fold b (a ∙_) l ∙ fold c (a ∙_) m
    lemma zero zero p = p
    lemma zero (suc m) p = trans (∙-cong refl (lemma zero m p)) (flip12 _ _ _)
    lemma (suc l) m p = trans (∙-cong refl (lemma l m p)) (sym (assoc a _ _))

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
nf₁ ≟ nf₂ = Dec.map Pointwise-≡ (decidable ℕ._≟_ nf₁ nf₂)
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
