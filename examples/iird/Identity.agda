
module Identity where

import DefinitionalEquality
open DefinitionalEquality

postulate

  -- Formation
  _==_  : {A : Set} -> A -> A -> Set

  -- Introduction
  refl  : {A : Set}{x : A} -> x == x

  -- Elimination
  elim==  : {A : Set}(x : A)(C : (y : A) -> x == y -> Set) ->
            C x refl -> (y : A) -> (p : x == y) -> C y p

  elim==₁  : {A : Set}(x : A)(C : (y : A) -> x == y -> Set1) ->
             C x refl -> (y : A) -> (p : x == y) -> C y p

  -- Equality
  reduction== : {A : Set}{x : A}(C : (y : A) -> x == y -> Set)(r : C x refl) ->
          elim== x C r x refl ≡ r

  reduction==₁ : {A : Set}{x : A}(C : (y : A) -> x == y -> Set1)(r : C x refl) ->
          elim==₁ x C r x refl ≡₁ r

sym : {A : Set}{x y : A} -> x == y -> y == x
sym {A}{x}{y} eq = elim== x (\z _ -> z == x) refl y eq

subst : {A : Set}{x y : A}(P : A -> Set) -> x == y -> P x -> P y
subst P xy px = elim== _ (\z _ -> P z) px _ xy

subst₁ : {A : Set}{x y : A}(P : A -> Set1) -> x == y -> P x -> P y
subst₁ P xy px = elim==₁ _ (\z _ -> P z) px _ xy

symRef : (A : Set)(x : A) -> sym (refl{A}{x}) == refl
symRef A x = subst-≡ (\z -> z == refl) (reduction== (\y _ -> y == x) refl) refl
-- symRef A x = reduction== (\y _ -> y == _) refl   -- can't solve x

symSym : {A : Set}{x y : A}(p : x == y) -> sym (sym p) == p
symSym {A}{x}{y} p = elim== x (\y q -> sym (sym q) == q) h y p
  where
    h : sym (sym (refl{A}{x})) == refl
    h = subst {x == x}{refl}{sym refl} (\q -> sym q == refl) (sym (symRef A x)) (symRef A x)

-- Proving the symmetric elimination rule is not trivial.
elimS : {A : Set}(x : A)(C : (y : A) -> y == x -> Set) ->
        C x refl -> (y : A) -> (p : y == x) -> C y p
elimS x C r y p = subst (C y) (symSym p) h
  where
    Csymrefl : C x (sym refl)
    Csymrefl = subst (C x) (sym (symRef _ x)) r

    h = elim== x (\y p -> C y (sym p)) Csymrefl y (sym p)


