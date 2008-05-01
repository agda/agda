------------------------------------------------------------------------
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

module Induction where

open import Relation.Unary

-- A RecStruct describes the allowed structure of recursion. The
-- examples in Induction.Nat should explain what this is all about.

RecStruct : Set -> Set1
RecStruct a = Pred a -> Pred a

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : forall {a} -> RecStruct a -> Set1
RecursorBuilder {a} Rec =
     (P : Pred a) -> Rec P ⟶ P -> forall x -> Rec P x

-- A recursor can be used to actually compute/prove something useful.

Recursor : forall {a} -> RecStruct a -> Set1
Recursor {a} Rec = (P : Pred a) -> Rec P ⟶ P -> forall x -> P x

-- And recursors can be constructed from recursor builders.

build
  :  forall {a} {Rec : RecStruct a}
  -> RecursorBuilder Rec
  -> Recursor Rec
build builder P f x = f x (builder P f x)

-- We can repeat the exercise above for subsets of the type we are
-- recursing over.

SubsetRecursorBuilder : forall {a} -> Pred a -> RecStruct a -> Set1
SubsetRecursorBuilder {a} Q Rec =
     (P : Pred a) -> Rec P ⟶ P -> Q ⟶ Rec P

SubsetRecursor : forall {a} -> Pred a -> RecStruct a -> Set1
SubsetRecursor {a} Q Rec = (P : Pred a) -> Rec P ⟶ P -> Q ⟶ P

subsetBuild
  :  forall {a} {Q : Pred a} {Rec : RecStruct a}
  -> SubsetRecursorBuilder Q Rec
  -> SubsetRecursor Q Rec
subsetBuild builder P f x q = f x (builder P f x q)
