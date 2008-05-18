
module Derivative where

  open import Sets
  open import Functor
  import Isomorphism

  ∂ : U -> U
  ∂ (K A)   = K [0]
  ∂ Id	    = K [1]
  ∂ (F + G) = ∂ F + ∂ G
  ∂ (F × G) = ∂ F × G + F × ∂ G

  open Semantics

  -- Plugging a hole
  plug-∂ : {X : Set}(F : U) -> ⟦ ∂ F ⟧ X -> X -> ⟦ F ⟧ X
  plug-∂ (K _)	()		 x
  plug-∂ Id	<>		 x = x
  plug-∂ (F + G) (inl c)	 x = inl (plug-∂ F c x)
  plug-∂ (F + G) (inr c)	 x = inr (plug-∂ G c x)
  plug-∂ (F × G) (inl < c , g >) x = < plug-∂ F c x , g >
  plug-∂ (F × G) (inr < f , c >) x = < f , plug-∂ G c x >

