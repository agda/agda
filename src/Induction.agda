------------------------------------------------------------------------
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

-- Note: The types in this module can perhaps be easier to understand
-- if they are normalised. Note also that Agda can do the
-- normalisation for you.

module Induction where

open import Relation.Unary

-- A RecStruct describes the allowed structure of recursion. The
-- examples in Induction.Nat should explain what this is all about.

RecStruct : Set → Set₁
RecStruct a = Pred a → Pred a

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : ∀ {a} → RecStruct a → Set₁
RecursorBuilder {a} Rec = (P : Pred a) → Rec P ⊆′ P → Universal (Rec P)

-- A recursor can be used to actually compute/prove something useful.

Recursor : ∀ {a} → RecStruct a → Set₁
Recursor {a} Rec = (P : Pred a) → Rec P ⊆′ P → Universal P

-- And recursors can be constructed from recursor builders.

build : ∀ {a} {Rec : RecStruct a} →
        RecursorBuilder Rec →
        Recursor Rec
build builder P f x = f x (builder P f x)

-- We can repeat the exercise above for subsets of the type we are
-- recursing over.

SubsetRecursorBuilder : ∀ {a} → Pred a → RecStruct a → Set₁
SubsetRecursorBuilder {a} Q Rec = (P : Pred a) → Rec P ⊆′ P → Q ⊆′ Rec P

SubsetRecursor : ∀ {a} → Pred a → RecStruct a → Set₁
SubsetRecursor {a} Q Rec = (P : Pred a) → Rec P ⊆′ P → Q ⊆′ P

subsetBuild : ∀ {a} {Q : Pred a} {Rec : RecStruct a} →
              SubsetRecursorBuilder Q Rec →
              SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)
