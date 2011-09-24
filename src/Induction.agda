------------------------------------------------------------------------
-- The Agda standard library
--
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

-- The idea underlying Induction.* comes from Epigram 1, see Section 4
-- of "The view from the left" by McBride and McKinna.

-- Note: The types in this module can perhaps be easier to understand
-- if they are normalised. Note also that Agda can do the
-- normalisation for you.

module Induction where

open import Level
open import Relation.Unary

-- A RecStruct describes the allowed structure of recursion. The
-- examples in Induction.Nat should explain what this is all about.

RecStruct : ∀ {a} → Set a → Set (suc a)
RecStruct {a} A = Pred A a → Pred A a

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : ∀ {a} {A : Set a} → RecStruct A → Set _
RecursorBuilder Rec = ∀ P → Rec P ⊆′ P → Universal (Rec P)

-- A recursor can be used to actually compute/prove something useful.

Recursor : ∀ {a} {A : Set a} → RecStruct A → Set _
Recursor Rec = ∀ P → Rec P ⊆′ P → Universal P

-- And recursors can be constructed from recursor builders.

build : ∀ {a} {A : Set a} {Rec : RecStruct A} →
        RecursorBuilder Rec →
        Recursor Rec
build builder P f x = f x (builder P f x)

-- We can repeat the exercise above for subsets of the type we are
-- recursing over.

SubsetRecursorBuilder : ∀ {a ℓ} {A : Set a} →
                        Pred A ℓ → RecStruct A → Set _
SubsetRecursorBuilder Q Rec = ∀ P → Rec P ⊆′ P → Q ⊆′ Rec P

SubsetRecursor : ∀ {a ℓ} {A : Set a} →
                 Pred A ℓ → RecStruct A → Set _
SubsetRecursor Q Rec = ∀ P → Rec P ⊆′ P → Q ⊆′ P

subsetBuild : ∀ {a ℓ} {A : Set a} {Q : Pred A ℓ} {Rec : RecStruct A} →
              SubsetRecursorBuilder Q Rec →
              SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)
