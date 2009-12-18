------------------------------------------------------------------------
-- A variant of Induction for Set₁
------------------------------------------------------------------------

-- I want universe polymorphism.

module Induction1 where

open import Level
open import Relation.Unary

-- A RecStruct describes the allowed structure of recursion. The
-- examples in Induction.Nat should explain what this is all about.

RecStruct : Set → Set₂
RecStruct a = Pred a (suc zero) → Pred a (suc zero)

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : ∀ {a} → RecStruct a → Set₂
RecursorBuilder {a} Rec =
  (P : Pred a (suc zero)) → Rec P ⊆′ P → Universal (Rec P)

-- A recursor can be used to actually compute/prove something useful.

Recursor : ∀ {a} → RecStruct a → Set₂
Recursor {a} Rec = (P : Pred a (suc zero)) → Rec P ⊆′ P → Universal P

-- And recursors can be constructed from recursor builders.

build : ∀ {a} {Rec : RecStruct a} →
        RecursorBuilder Rec →
        Recursor Rec
build builder P f x = f x (builder P f x)

-- We can repeat the exercise above for subsets of the type we are
-- recursing over.

SubsetRecursorBuilder : ∀ {a} → Pred a (suc zero) → RecStruct a → Set₂
SubsetRecursorBuilder {a} Q Rec =
  (P : Pred a (suc zero)) → Rec P ⊆′ P → Q ⊆′ Rec P

SubsetRecursor : ∀ {a} → Pred a (suc zero) → RecStruct a → Set₂
SubsetRecursor {a} Q Rec = (P : Pred a (suc zero)) → Rec P ⊆′ P → Q ⊆′ P

subsetBuild : ∀ {a} {Q : Pred a (suc zero)} {Rec : RecStruct a} →
              SubsetRecursorBuilder Q Rec →
              SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)
