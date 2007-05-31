
module Equality where

  postulate _==_ : {A : Set} -> A -> A -> Set
	    refl : {A : Set}{x : A} -> x == x

  {-# BUILTIN EQUAL _==_ #-}
  {-# BUILTIN REFL  refl #-}

  private
   primitive
    primEqElim : {A : Set}(x : A)(C : (y : A) -> x == y -> Set) ->
		 C x refl -> (y : A) -> (p : x == y) -> C y p

  elim-== = \{A : Set} -> primEqElim {A}

  subst : {A : Set}(C : A -> Set){x y : A} -> x == y -> C y -> C x
  subst C {x}{y} p Cy = elim-== x (\z _ -> C z -> C x) (\Cx -> Cx) y p Cy

  sym : {A : Set}{x y : A} -> x == y -> y == x
  sym {x = x}{y = y} p = subst (\z -> y == z) p refl

  trans : {A : Set}{x y z : A} -> x == y -> y == z -> x == z
  trans {x = x}{y = y}{z = z} xy yz = subst (\w -> w == z) xy yz

  cong : {A B : Set}{x y : A}(f : A -> B) -> x == y -> f x == f y
  cong {y = y} f xy = subst (\ ∙ -> f ∙ == f y) xy refl

