module IIDg where

open import LF

-- Codes for indexed inductive types
data OPg (I : Set) : Set1 where
  ι : I -> OPg I
  σ : (A : Set)(γ : A -> OPg I) -> OPg I
  δ : (H : Set)(i : H -> I)(γ : OPg I) -> OPg I

-- The top-level structure of values in an IIDg
Args : {I : Set}(γ : OPg I)(U : I -> Set) -> Set
Args (ι _)     U = One
Args (σ A γ)   U = A × \a -> Args (γ a) U
Args (δ H i γ) U = ((x : H) -> U (i x)) × \_ -> Args γ U

-- The index of a value in an IIDg
Index : {I : Set}(γ : OPg I)(U : I -> Set) -> Args γ U -> I
Index (ι i)	U _	    = i
Index (σ A γ)	U < a | b > = Index (γ a) U b
Index (δ _ _ γ) U < _ | b > = Index γ U b

-- The assumptions of a particular inductive occurrence.
IndArg : {I : Set}(γ : OPg I)(U : I -> Set) -> Args γ U -> Set
IndArg (ι _)     U _	     = Zero
IndArg (σ A γ)	 U < a | b > = IndArg (γ a) U b
IndArg (δ H i γ) U < _ | b > = H + IndArg γ U b

-- The index of an inductive occurrence.
IndIndex : {I : Set}(γ : OPg I)(U : I -> Set)(a : Args γ U) -> IndArg γ U a -> I
IndIndex (ι _)	   U _	     ()
IndIndex (σ A γ)   U < a | b > h       = IndIndex (γ a) U b h
IndIndex (δ A i γ) U < g | b > (inl h) = i h
IndIndex (δ A i γ) U < g | b > (inr h) = IndIndex γ U b h

-- An inductive occurrence.
Ind : {I : Set}(γ : OPg I)(U : I -> Set)(a : Args γ U)(h : IndArg γ U a) -> U (IndIndex γ U a h)
Ind (ι _)     U _	  ()
Ind (σ A γ)   U < a | b > h	  = Ind (γ a) U b h
Ind (δ H i γ) U < g | b > (inl h) = g h
Ind (δ H i γ) U < _ | b > (inr h) = Ind γ U b h

-- The type of induction hypotheses.
IndHyp : {I : Set}(γ : OPg I)(U : I -> Set)(C : (i : I) -> U i -> Set)(a : Args γ U) -> Set
IndHyp γ U C a = (hyp : IndArg γ U a) -> C (IndIndex γ U a hyp) (Ind γ U a hyp)

-- Large induction hypostheses.
IndHyp₁ : {I : Set}(γ : OPg I)(U : I -> Set)(C : (i : I) -> U i -> Set1)(a : Args γ U) -> Set1
IndHyp₁ γ U C a = (hyp : IndArg γ U a) -> C (IndIndex γ U a hyp) (Ind γ U a hyp)

