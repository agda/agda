
module FamilyPattern where

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

postulate C : {A : Set} -> A -> Set

-- We can't solve unify x = y since the type is a meta variable.
subst : {A : Set}{x y : A} -> x == y -> C y -> C x
subst refl cx = cx
-- subst {A}          refl cx = cx -- works
-- subst {x = x} .{x} refl cx = cx -- works

