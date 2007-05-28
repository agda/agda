
module List where

open import Prelude
open import Star

[_] : Set -> Rel True
[ A ] = \_ _ -> A

List : Set -> Set
List A = Star [ A ] _ _

-- Actually there isn't really that much interesting stuff to be
-- done for lists that isn't generic.

{- Note that the "proofs" are the elements of the list. -}
