
module BuiltinEquality where

postulate
  _==_ : {A : Set} -> A -> A -> Set
  refl : {A : Set}{x : A} -> x == x

{-# BUILTIN EQUAL _==_ #-}
{-# BUILTIN REFL  refl #-}

private
 primitive
  primEqElim : {A : Set}(x : A)(C : (y : A) -> x == y -> Set) ->
	       C x refl -> (y : A) -> (p : x == y) -> C y p

eqElim = \{A : Set} -> primEqElim {A}

-- id x C h should reduce to h
id : {A : Set}(x : A)(C : (y : A) -> x == y -> Set) -> C x refl -> C x refl
id x C h = eqElim x C h x refl

test : {A : Set}(x : A)(C : (y : A) -> x == y -> Set)(h : C x refl) -> id x C h == h
test x C h = refl

