module Issue1258 where

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Bool : Set where
  true false : Bool

postulate f : (A : Set) -> A -> Bool

Foo : Bool -> Set
Foo true = Bool
Foo false = Bool

Alpha : Bool
Beta : Foo Alpha

test : f (Foo Alpha) Beta == f Bool false

Alpha = _
Beta = Alpha
test = refl

-- Normalizing Alpha yields a metavariable, but normalizing Beta yields
-- false.
