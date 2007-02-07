
module IID-Proof-Setup where

open import LF
open import Identity
open import IID
open import IIDr

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
	      rArgs (ε γ) U (Index γ U a)
g→rArgs (ι e)     U a	  = < refl | ★ >
g→rArgs (σ A γ)   U < a | b > = < a | g→rArgs (γ a) U b >
g→rArgs (δ H i γ) U < g | b > = < g | g→rArgs γ U b >

-- Strips the equality proof.
r→gArgs : {I : Set}(γ : OPg I)(U : I -> Set)
	      (i : I)(a : rArgs (ε γ) U i) ->
	      Args γ U
r→gArgs (ι i)     U j _	    = ★
r→gArgs (σ A γ)   U j < a | b > = < a | r→gArgs (γ a) U j b >
r→gArgs (δ H i γ) U j < g | b > = < g | r→gArgs γ U j b >

-- Converting an rArgs to a gArgs and back is the identity. We need to pair the
-- arguments with their indices since they have different types.
r←→gArgs-subst :
  {I : Set}(γ : OPg I)(U : I -> Set)
  (C : (i : I) -> rArgs (ε γ) U i -> Set)
  (i : I)(a : rArgs (ε γ) U i) ->
  (C (Index γ U (r→gArgs γ U i a))
     (g→rArgs γ U (r→gArgs γ U i a))
  ) -> C i a

r←→gArgs-subst {I} (ι i) U C j < p | ★ > m =
  elim== i (\k q -> C k < q | ★ >) m j p

r←→gArgs-subst (σ A γ)   U C j < a | b > m = 
  r←→gArgs-subst (γ a) U (\i c -> C i < a | c >) j b m

r←→gArgs-subst (δ H i γ) U C j < g | b > m =
  r←→gArgs-subst γ U (\i c -> C i < g | c >) j b m

-- Corresponding conversion functions for assumptions to inductive occurrences.
-- Basically an identity function.
g→rIndArg : {I : Set}(γ : OPg I)(U : I -> Set)
        (i : I)(a : rArgs (ε γ) U i) ->
        IndArg γ U (r→gArgs γ U i a) -> IndArg (ε γ i) U a
g→rIndArg (ι j)	    U i < h | ★ > ()
g→rIndArg (σ A γ)   U i < a | b > v       = g→rIndArg (γ a) U i b v
g→rIndArg (δ A j γ) U i < g | b > (inl a) = inl a
g→rIndArg (δ A j γ) U i < g | b > (inr v) = inr (g→rIndArg γ U i b v)

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
g→rIndArg-subst (ι j)	  U C i < p | _ > ()	  h
g→rIndArg-subst (σ A γ)	  U C i < a | b > v	  h = g→rIndArg-subst (γ a) U C i b v h
g→rIndArg-subst (δ A j γ) U C i < g | b > (inl a) h = h
g→rIndArg-subst (δ A j γ) U C i < g | b > (inr v) h = g→rIndArg-subst γ U C i b v h


