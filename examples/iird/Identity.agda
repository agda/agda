
module Identity where

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

elim== : {A : Set}(x : A)(C : (y : A) -> x == y -> Set) ->
         C x refl -> (y : A) -> (p : x == y) -> C y p
elim== x C Cx .x refl = Cx

elim==₁ : {A : Set}(x : A)(C : (y : A) -> x == y -> Set1) ->
	  C x refl -> (y : A) -> (p : x == y) -> C y p
elim==₁ x C Cx .x refl = Cx

sym : {A : Set}{x y : A} -> x == y -> y == x
sym {A}{x}{y} eq = elim== x (\z _ -> z == x) refl y eq

subst : {A : Set}{x y : A}(P : A -> Set) -> x == y -> P x -> P y
subst P xy px = elim== _ (\z _ -> P z) px _ xy

subst₁ : {A : Set}{x y : A}(P : A -> Set1) -> x == y -> P x -> P y
subst₁ P xy px = elim==₁ _ (\z _ -> P z) px _ xy

symRef : (A : Set)(x : A) -> sym (refl{A}{x}) == refl
symRef A x = refl

symSym : {A : Set}{x y : A}(p : x == y) -> sym (sym p) == p
symSym {A}{x}{y} p = elim== x (\y q -> sym (sym q) == q) refl y p

-- Proving the symmetric elimination rule is not trivial.
elimS : {A : Set}(x : A)(C : (y : A) -> y == x -> Set) ->
        C x refl -> (y : A) -> (p : y == x) -> C y p
elimS x C r y p = subst (C y) (symSym p) h
  where
    h : C y (sym (sym p))
    h = elim== x (\y p -> C y (sym p)) r y (sym p)


