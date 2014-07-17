module InstanceMeta where

data Bool : Set where
  true false : Bool

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

record Eq (A : Set) : Set where
  constructor eq
  field
    _==_ : A → A → Bool
open Eq {{...}} public

instance
  eq-Bool : Eq Bool
  eq-Bool = eq aux  where

    aux : Bool → Bool → Bool
    aux true true = true
    aux false false = true
    aux _ _ = false

  eq-Maybe : {A : Set} {{_ : Eq A}} → Eq (Maybe A)
  eq-Maybe {A} = eq aux  where

    aux : Maybe A → Maybe A → Bool
    aux Nothing Nothing = true
    aux (Just y) (Just z) = (y == z)
    aux _ _ = false

test : Bool
test = {!!} == {!!}
-- This should not loop, only produce unsolved metas
