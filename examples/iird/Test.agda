
module Test where

open import LF
open import IID

-- r←→gArgs-subst eliminates the identity proof stored in the rArgs. If this proof is
-- by reflexivity r←→gArgs-subst is a definitional identity. This is the case
-- when a = g→rArgs a'
r←→gArgs-subst-identity :
  {I  : Set}(γ : OPg I)(U : I -> Set)
  (C  : (i : I) -> rArgs (ε γ) U i -> Set)
  (a' : Args γ U) ->
  let a = g→rArgs γ U a'
      i = index γ U a' in
  (h : C (index γ U (r→gArgs γ U i a))
	 (g→rArgs γ U (r→gArgs γ U i a))
  ) -> r←→gArgs-subst γ U C i a h ≡ h
r←→gArgs-subst-identity (ι i)	  U C _   h = refl-≡
r←→gArgs-subst-identity (σ A γ)	  U C arg h = r←→gArgs-subst-identity (γ (π₀ arg)) U C' (π₁ arg) h
  where C' = \i c -> C i (π₀ arg , c)
r←→gArgs-subst-identity (δ H i γ) U C arg h = r←→gArgs-subst-identity γ U C' (π₁ arg) h
  where C' = \i c -> C i (π₀ arg , c)

