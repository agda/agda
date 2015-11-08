
-- There was a bug when postponing a type checking problem under
-- a non-empty context. Fixed now.
module PostponedTypeChecking where

data Unit : Set where
  unit : Unit

record R : Set where
 field f : Unit

data *_ (A : Set) : Set where
  <_> : A -> * A

get : {A : Set} -> * A -> A
get < x > = x

mk : Unit -> Unit -> * R
mk _ _ = < record { f = unit } >

r : R
r = get (mk unit unit)

data IsUnit : Unit -> Set where
  isUnit : IsUnit unit

foo : IsUnit (R.f r)
foo = isUnit

