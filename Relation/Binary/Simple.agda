------------------------------------------------------------------------
-- Some simple binary relations
------------------------------------------------------------------------

module Relation.Binary.Simple where

open import Relation.Binary
open import Data.Unit
open import Data.Empty

-- Constant relations.

Const : forall {a} -> Set -> Rel a
Const I = \_ _ -> I

-- The universally true relation.

Always : forall {a} -> Rel a
Always = Const ⊤

-- The universally false relation.

Never : forall {a} -> Rel a
Never = Const ⊥
