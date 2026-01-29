module Issue8215 where

postulate
  T : Set
  t : T

record A (X : Set) : Set where
  field
    f : X

open A {{...}}

record B (X : Set) : Set where
  field
    instance a : A X
    g : X

open B {{...}}


instance AT : A T
AT = record {f = t}

{-
instance BT : B T
BT = record {a = AT; g = t}
-}

-- Internal error here
f′ : T
f′ = f
