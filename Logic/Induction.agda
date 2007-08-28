------------------------------------------------------------------------
-- An abstraction of various forms of recursion/induction
------------------------------------------------------------------------

module Logic.Induction where

-- A RecStruct describes the allowed structure of recursion. The
-- examples in Logic.Induction.Nat should explain what this is all
-- about.

RecStruct : Set -> Set1
RecStruct a = (a -> Set) -> (a -> Set)

-- A recursor builder constructs an instance of a recursion structure
-- for a given input.

RecursorBuilder : forall {a} -> RecStruct a -> Set1
RecursorBuilder {a} Rec =
     (P : a -> Set)
  -> (forall x -> Rec P x -> P x)
  -> forall x -> Rec P x

-- A recursor can be used to actually compute/prove something useful.

Recursor : forall {a} -> RecStruct a -> Set1
Recursor {a} Rec =
     (P : a -> Set)
  -> (forall x -> Rec P x -> P x)
  -> forall x -> P x

-- And recursors can be constructed from recursor builders.

build
  :  forall {a} {Rec : RecStruct a}
  -> RecursorBuilder Rec
  -> Recursor Rec
build builder P f x = f x (builder P f x)
