
module ChainRule where

  import Sets
  import Functor
  import Logic.ChainReasoning.Poly as CR
  import Isomorphism
  import Derivative

  open Derivative
  open Sets
  open Functor
  open Semantics
  open Isomorphism
  module Chain = CR _==_ (\x -> refl{x = x}) (\x y z -> trans{x = x}{y}{z})
  open Chain

  chain-rule : (F G : U)(X : Set) -> ⟦ ∂ (F [ G ]) ⟧ X ≅ ⟦ ∂ F [ G ] × ∂ G ⟧ X
  chain-rule F G X = iso (i F) (j F) (ji F) (ij F)
    where
      i : (F : U) -> ⟦ ∂ (F [ G ]) ⟧ X -> ⟦ ∂ F [ G ] × ∂ G ⟧ X
      i (K A)	  ()
      i Id	  x		    = < <> , x >
      i (F₁ + F₂) (inl c)	    = (inl <×> id) (i F₁ c)
      i (F₁ + F₂) (inr c)	    = (inr <×> id) (i F₂ c)
      i (F₁ × F₂) (inl < c  , f₂ >) = (inl ∘ <∙, f₂ > <×> id) (i F₁ c)
      i (F₁ × F₂) (inr < f₁ , c  >) = (inr ∘ < f₁ ,∙> <×> id) (i F₂ c)

      j : (F : U) -> ⟦ ∂ F [ G ] × ∂ G ⟧ X -> ⟦ ∂ (F [ G ]) ⟧ X
      j (K A)	  < () , _ >
      j Id	  < <> , x > = x
      j (F₁ + F₂) < inl x , y > = inl (j F₁ < x , y >)
      j (F₁ + F₂) < inr x , y > = inr (j F₂ < x , y >)
      j (F₁ × F₂) < inl < x , y > , z > = inl < j F₁ < x , z > , y >
      j (F₁ × F₂) < inr < x , y > , z > = inr < x , j F₂ < y , z > >

      ij : (F : U)(x : _) -> i F (j F x) == x
      ij (K A)	   < () , _ >
      ij Id	   < <> , x > = refl
      ij (F₁ + F₂) < lx@(inl x) , y > =
	subst (\ ∙ -> (inl <×> id) ∙ == < lx , y >)
	      (ij F₁ < x , y >) refl
      ij (F₁ + F₂) < rx@(inr x) , y > =
	subst (\ ∙ -> (inr <×> id) ∙ == < rx , y >)
	      (ij F₂ < x , y >) refl
      ij (F₁ × F₂) < xy@(inl < x , y >) , z > =
	subst (\ ∙ -> (inl ∘ <∙, y > <×> id) ∙ == < xy , z >)
	      (ij F₁ < x , z >) refl
      ij (F₁ × F₂) < xy@(inr < x , y >) , z > =
	subst (\ ∙ -> (inr ∘ < x ,∙> <×> id) ∙ == < xy , z >)
	      (ij F₂ < y , z >) refl

      ji : (F : U)(y : _) -> j F (i F y) == y
      ji (K A) ()
      ji Id x = refl
      ji (F₁ + F₂) (inl c) =
	chain> j (F₁ + F₂) ((inl <×> id) (i F₁ c))
	   === inl (j F₁ _)	    by cong (j (F₁ + F₂) ∘ (inl <×> id)) (η-[×] (i F₁ c))
	   === inl (j F₁ (i F₁ c))  by cong (inl ∘ j F₁) (sym $ η-[×] (i F₁ c))
	   === inl c		    by cong inl (ji F₁ c)
      ji (F₁ + F₂) rc @ (inr c) =
	subst (\ ∙ -> j (F₁ + F₂) ((inr <×> id) ∙) == rc) (η-[×] (i F₂ c))
	$ subst (\ ∙ -> inr (j F₂ ∙) == rc) (sym $ η-[×] (i F₂ c))
	$ subst (\ ∙ -> inr ∙ == rc) (ji F₂ c) refl
      ji (F₁ × F₂) l @ (inl < c , f₂ >) =
	subst (\ ∙ -> j (F₁ × F₂) ((inl ∘ <∙, f₂ > <×> id) ∙) == l) (η-[×] (i F₁ c))
	$ subst (\ ∙ -> inl < j F₁ ∙ , f₂ > == l) (sym $ η-[×] (i F₁ c))
	$ subst (\ ∙ -> inl < ∙ , f₂ > == l) (ji F₁ c) refl
      ji (F₁ × F₂) r @ (inr < f₁ , c >) =
	subst (\ ∙ -> j (F₁ × F₂) ((inr ∘ < f₁ ,∙> <×> id) ∙) == r) (η-[×] (i F₂ c))
	$ subst (\ ∙ -> inr < f₁ , j F₂ ∙ > == r) (sym $ η-[×] (i F₂ c))
	$ subst (\ ∙ -> inr < f₁ , ∙ > == r) (ji F₂ c) refl

