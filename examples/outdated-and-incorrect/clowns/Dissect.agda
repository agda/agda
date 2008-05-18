
module Dissect where

  import Functor
  import Sets
  import Isomorphism

  open Sets
  open Functor
  open Functor.Semantics
  open Functor.Recursive

  infixr 40 _+₂_
  infixr 60 _×₂_

  ∇ : U -> U₂
  ∇ (K A) = K₂ [0]
  ∇ Id	  = K₂ [1]
  ∇ (F + G) = ∇ F +₂ ∇ G
  ∇ (F × G) = ∇ F ×₂ ↗ G  +₂  ↖ F ×₂ ∇ G

  diagonal : U₂ -> U
  diagonal (K₂ A) = K A
  diagonal (↖ F)  = F
  diagonal (↗ F)  = F
  diagonal (F +₂ G) = diagonal F + diagonal G
  diagonal (F ×₂ G) = diagonal F × diagonal G

  module Derivative where

    import Derivative as D

    ∂ : U -> U
    ∂ F = diagonal (∇ F)

    open Isomorphism

    same : (F : U)(X : Set) -> ⟦ ∂ F ⟧ X ≅ ⟦ D.∂ F ⟧ X
    same (K A)	 X = refl-≅ [0]
    same Id	 X = refl-≅ [1]
    same (F + G) X = iso[+] (same F X) (same G X)
    same (F × G) X = iso[+] (iso[×] (same F X) (refl-≅ _))
			    (iso[×] (refl-≅ _) (same G X))

  Stack : (F : U) -> Set -> Set -> Set
  Stack F C J = List (⟦ ∇ F ⟧₂ C J)

  NextJoker : U -> Set -> Set -> Set
  NextJoker F C J = J  [×]  ⟦ ∇ F ⟧₂ C J  [+]  ⟦ F ⟧ C

  mutual
    into : (F : U){C J : Set} -> ⟦ F ⟧ J -> NextJoker F C J
    into (K A)	  a	     = inr a
    into Id	  x	     = inl < x , <> >
    into (F + G) (inl f)     = (id <×> inl <+> inl) (into F f)
    into (F + G) (inr g)     = (id <×> inr <+> inr) (into G g)
    into (F × G) < fj , gj > = tryL F G (into F fj) gj

    next : (F : U){C J : Set} -> ⟦ ∇ F ⟧₂ C J -> C -> NextJoker F C J
    next (K A)	 ()		   _
    next Id	 <>		   c = inr c
    next (F + G) (inl f')	   c = (id <×> inl <+> inl) (next F f' c)
    next (F + G) (inr g')	   c = (id <×> inr <+> inr) (next G g' c)
    next (F × G) (inl < f' , gj >) c = tryL F G (next F f' c) gj
    next (F × G) (inr < fc , g' >) c = tryR F G fc (next G g' c)

    tryL : (F G : U){C J : Set} ->
	   NextJoker F C J -> ⟦ G ⟧ J -> NextJoker (F × G) C J
    tryL F G (inl < j , f' >) gj = inl < j , inl < f' , gj > >
    tryL F G (inr fc)         gj = tryR F G fc (into G gj)

    tryR : (F G : U){C J : Set} ->
	   ⟦ F ⟧ C -> NextJoker G C J -> NextJoker (F × G) C J
    tryR F G fc (inl < j , g' >) = inl < j , inr < fc , g' > >
    tryR F G fc (inr gc)	 = inr < fc , gc >

  map : (F : U){C J : Set} -> (J -> C) -> ⟦ F ⟧ J -> ⟦ F ⟧ C
  map F φ f = iter (into F f) where
    iter : NextJoker F _ _ -> ⟦ F ⟧ _
    iter (inl < j , d >) = iter (next F d (φ j))
    iter (inr f)	 = f

  fold : (F : U){T : Set} -> (⟦ F ⟧ T -> T) -> μ F -> T
  fold F {T} φ r = inward r [] where
    mutual
      inward : μ F -> Stack F T (μ F) -> T
      inward (inn f) γ = onward (into F f) γ

      outward : T -> Stack F T (μ F) -> T
      outward t []	  = t
      outward t (f' :: γ) = onward (next F f' t) γ

      onward : NextJoker F T (μ F) -> Stack F T (μ F) -> T
      onward (inl < r , f' >) γ = inward r (f' :: γ)
      onward (inr t)	      γ = outward (φ t) γ

  -- can we make a non-tail recursive fold?
  -- of course, nothing could be simpler: (not structurally recursive though)
  fold' : (F : U){T : Set} -> (⟦ F ⟧ T -> T) -> μ F -> T
  fold' F φ = φ ∘ map F (fold' F φ) ∘ out

  -- Fold operators
  Φ : (F : U) -> Set -> Set
  Φ (K A)   T = A -> T
  Φ Id	    T = T -> T
  Φ (F + G) T = Φ F T [×] Φ G T
  Φ (F × G) T = (T -> T -> T) [×] (Φ F T [×] Φ G T)

  mkφ : (F : U){T : Set} -> Φ F T -> ⟦ F ⟧ T -> T
  mkφ (K A)   f			    a	      = f a
  mkφ Id      f			    t	      = f t
  mkφ (F + G) < φf , φg >	    (inl f)   = mkφ F φf f
  mkφ (F + G) < φf , φg >	    (inr g)   = mkφ G φg g
  mkφ (F × G) < _○_ , < φf , φg > > < f , g > = mkφ F φf f ○ mkφ G φg g

