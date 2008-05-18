
module IID-Proof-Setup where

open import LF
open import Identity
open import IID
open import IIDr
open import DefinitionalEquality

OPg : Set -> Set1
OPg I = OP I I

-- Encoding indexed inductive types as non-indexed types.
ε : {I : Set}(γ : OPg I) -> OPr I
ε (ι i)     j = σ (i == j) (\_ -> ι ★)
ε (σ A γ)   j = σ A (\a -> ε (γ a) j)
ε (δ H i γ) j = δ H i (ε γ j)

-- Adds a reflexivity proof.
g→rArgs : {I : Set}(γ : OPg I)(U : I -> Set)
	      (a : Args γ U) ->
	      rArgs (ε γ) U (index γ U a)
g→rArgs (ι e)     U arg	= (refl , ★)
g→rArgs (σ A γ)   U arg = (π₀ arg , g→rArgs (γ (π₀ arg)) U (π₁ arg))
g→rArgs (δ H i γ) U arg = (π₀ arg , g→rArgs γ U (π₁ arg))

-- Strips the equality proof.
r→gArgs : {I : Set}(γ : OPg I)(U : I -> Set)
	      (i : I)(a : rArgs (ε γ) U i) ->
	      Args γ U
r→gArgs (ι i)     U j _	  = ★
r→gArgs (σ A γ)   U j arg = (π₀ arg , r→gArgs (γ (π₀ arg)) U j (π₁ arg))
r→gArgs (δ H i γ) U j arg = (π₀ arg , r→gArgs γ U j (π₁ arg))

-- Converting an rArgs to a gArgs and back is (provably, not definitionally)
-- the identity.
r←→gArgs-subst :
  {I : Set}(γ : OPg I)(U : I -> Set)
  (C : (i : I) -> rArgs (ε γ) U i -> Set)
  (i : I)(a : rArgs (ε γ) U i) ->
  (C (index γ U (r→gArgs γ U i a))
     (g→rArgs γ U (r→gArgs γ U i a))
  ) -> C i a

r←→gArgs-subst {I} (ι i) U C j arg m =
  elim== i (\k q -> C k (q , ★)) m j (π₀ arg)

r←→gArgs-subst (σ A γ)   U C j arg m = 
  r←→gArgs-subst (γ (π₀ arg)) U (\i c -> C i (π₀ arg , c)) j (π₁ arg) m

r←→gArgs-subst (δ H i γ) U C j arg m =
  r←→gArgs-subst γ U (\i c -> C i (π₀ arg , c)) j (π₁ arg) m

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

-- Going the other way around is definitionally the identity.
g←→rArgs-identity :
  {I : Set}(γ : OPg I)(U : I -> Set)
  (a : Args γ U) ->
  r→gArgs γ U (index γ U a) (g→rArgs γ U a) ≡ a
g←→rArgs-identity (ι i)	    U _	  = refl-≡
g←→rArgs-identity (σ A γ)   U arg = cong-≡ (\ ∙ -> (π₀ arg , ∙)) (g←→rArgs-identity (γ (π₀ arg)) U (π₁ arg))
g←→rArgs-identity (δ H i γ) U arg = cong-≡ (\ ∙ -> (π₀ arg , ∙)) (g←→rArgs-identity γ U (π₁ arg))

-- Corresponding conversion functions for assumptions to inductive occurrences.
-- Basically an identity function.
g→rIndArg : {I : Set}(γ : OPg I)(U : I -> Set)
        (i : I)(a : rArgs (ε γ) U i) ->
        IndArg γ U (r→gArgs γ U i a) -> IndArg (ε γ i) U a
g→rIndArg (ι j)	    U i _ ()
g→rIndArg (σ A γ)   U i arg v       = g→rIndArg (γ (π₀ arg)) U i (π₁ arg) v
g→rIndArg (δ A j γ) U i arg (inl a) = inl a
g→rIndArg (δ A j γ) U i arg (inr v) = inr (g→rIndArg γ U i (π₁ arg) v)

-- Basically we can substitute general inductive occurences for the encoded
-- restricted inductive occurrences.
g→rIndArg-subst :
    {I : Set}(γ : OPg I)(U : I -> Set)
    (C : (i : I) -> U i -> Set)
    (i : I)(a : rArgs (ε γ) U i)
    (v : IndArg γ U (r→gArgs γ U i a)) ->
    C (IndIndex (ε γ i) U a (g→rIndArg γ U i a v))
      (Ind	(ε γ i) U a (g→rIndArg γ U i a v)) ->
    C (IndIndex γ U (r→gArgs γ U i a) v)
      (Ind	γ U (r→gArgs γ U i a) v)
g→rIndArg-subst (ι j)	  U C i _ ()	    h
g→rIndArg-subst (σ A γ)	  U C i arg v	    h = g→rIndArg-subst (γ (π₀ arg)) U C i (π₁ arg) v h
g→rIndArg-subst (δ A j γ) U C i arg (inl a) h = h
g→rIndArg-subst (δ A j γ) U C i arg (inr v) h = g→rIndArg-subst γ U C i (π₁ arg) v h

-- g→rIndArg-subst is purely book-keeping. On the object level it's definitional identity.
g→rIndArg-subst-identity :
    {I : Set}(γ : OPg I)(U : I -> Set)
    (C : (i : I) -> U i -> Set)
    (i : I)(a : rArgs (ε γ) U i)
    (v : IndArg γ U (r→gArgs γ U i a))
    (h : C (IndIndex (ε γ i) U a (g→rIndArg γ U i a v))
	   (Ind	(ε γ i) U a (g→rIndArg γ U i a v))
    ) -> g→rIndArg-subst γ U C i a v h ≡ h
g→rIndArg-subst-identity (ι j)	   U C i _   ()	   h
g→rIndArg-subst-identity (σ A γ)   U C i arg v	   h =
  g→rIndArg-subst-identity (γ (π₀ arg)) U C i (π₁ arg) v h
g→rIndArg-subst-identity (δ A j γ) U C i arg (inl a) h = refl-≡
g→rIndArg-subst-identity (δ A j γ) U C i arg (inr v) h =
  g→rIndArg-subst-identity γ U C i (π₁ arg) v h

-- And finally conversion of induction hypotheses. This goes the other direction.
r→gIndHyp :
    {I : Set}(γ : OPg I)(U : I -> Set)
    (C : (i : I) -> U i -> Set)
    (i : I)(a : rArgs (ε γ) U i) ->
    IndHyp (ε γ i) U C a -> IndHyp γ U C (r→gArgs γ U i a)
r→gIndHyp γ U C i a h v = g→rIndArg-subst γ U C i a v (h (g→rIndArg γ U i a v))

