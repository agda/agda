
module IID-Proof-Test where

open import LF
open import Identity
open import IID
open import IIDr
open import DefinitionalEquality
open import IID-Proof-Setup

η : {I : Set}(γ : OPg I)(U : I -> Set) -> Args γ U -> Args γ U
η (ι i)	  U _ = ★
η (σ A γ) U a = < a₀ | η (γ a₀) U a₁ >
  where
    a₀ = π₀ a
    a₁ = π₁ a
η (δ A i γ) U a = < a₀ | η γ U a₁ >
  where
    a₀ = π₀ a
    a₁ = π₁ a

r←→gArgs-equal :
  {I : Set}(γ : OPg I)(U : I -> Set)
  (i : I)(a : Args (ε γ i) U) ->
  _==_ {I × \i -> Args (ε γ i) U}
  < index γ U (r→gArgs γ U i a) | 
    g→rArgs γ U (r→gArgs γ U i a)
  > < i | a >
r←→gArgs-equal {I} (ι i) U j < p | ★ > = elim== i (\k q -> _==_ {I × \k -> Args (ε (ι i) k) U}
								< i | < refl | ★ > >
								< k | < q | ★ > >
						  ) refl j p
r←→gArgs-equal {I} (σ A γ)   U j < a | b > = cong f ih
  where ih = r←→gArgs-equal (γ a) U j b
	f : (I × \i -> Args (ε (γ a) i) U) -> (I × \i -> Args (ε (σ A γ) i) U)
	f < k | q > = < k | < a | q > >
r←→gArgs-equal {I} (δ H i γ) U j < g | b > = cong f ih
  where ih = r←→gArgs-equal γ U j b
	f : (I × \k -> Args (ε γ k) U) -> (I × \k -> Args (ε (δ H i γ) k) U)
	f < k | q > = < k | < g | q > >

{-
r←→gArgs-subst-identity' :
  {I  : Set}(γ : OPg I) ->
  
  (\(U : I -> Set)(C  : (i : I) -> rArgs (ε γ) U i -> Set)
    (a : Args γ U)(h : C (index γ U   (r→gArgs γ U (index γ U (η γ U a)) (g→rArgs γ U (η γ U a))))
			 (g→rArgs γ U (r→gArgs γ U (index γ U (η γ U a)) (g→rArgs γ U (η γ U a))))
		  ) -> r←→gArgs-subst γ U C (index γ U (η γ U a)) (g→rArgs γ U (η γ U a)) h
  ) ==¹
  (\(U : I -> Set)(C  : (i : I) -> rArgs (ε γ) U i -> Set)
    (a : Args γ U)(h : C (index γ U   (r→gArgs γ U (index γ U (η γ U a)) (g→rArgs γ U (η γ U a))))
			 (g→rArgs γ U (r→gArgs γ U (index γ U (η γ U a)) (g→rArgs γ U (η γ U a))))
		  ) -> h
  )
r←→gArgs-subst-identity' (ι i)	   = refl¹
r←→gArgs-subst-identity' (σ A γ)   = ?
r←→gArgs-subst-identity' (δ A i γ) = subst¹ (\ ∙ -> f ∙ ==¹ f (\U C a h -> h))
					    (r←→gArgs-subst-identity' γ) ?
  where
    ih = r←→gArgs-subst-identity' γ
    f = \g U C a h -> g U (\i c -> C i < π₀ a | c >) (π₁ a) h
-}
