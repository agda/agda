
-- The simpler case of index inductive definitions. (no induction-recursion)
module IID where

open import LF

-- A code for an IID
-- I - index set
-- E = I for general IIDs
-- E = One for restricted IIDs
data OP (I : Set)(E : Set) : Set1 where
  ι : E -> OP I E
  σ : (A : Set)(γ : A -> OP I E) -> OP I E
  δ : (A : Set)(i : A -> I)(γ : OP I E) -> OP I E

-- The type of constructor arguments. Parameterised over
--  U - the inductive type
-- This is the F of the simple polynomial type μF
Args : {I : Set}{E : Set} -> OP I E ->
     (U : I -> Set) -> Set
Args (ι e)     U = One
Args (σ A γ)   U = A × \a -> Args (γ a) U
Args (δ A i γ) U = ((a : A) -> U (i a)) × \_ -> Args γ U

-- Computing the index
index : {I : Set}{E : Set}(γ : OP I E)(U : I -> Set) -> Args γ U -> E
index (ι e)     U _ = e
index (σ A γ)   U a = index (γ (π₀ a)) U (π₁ a)
index (δ A i γ) U a = index γ U (π₁ a)

-- The assumptions of a particular inductive occurrence in a value.
IndArg : {I : Set}{E : Set}
       (γ : OP I E)(U : I -> Set) ->
       Args γ U -> Set
IndArg (ι e)     U _ = Zero
IndArg (σ A γ)   U a = IndArg (γ (π₀ a)) U (π₁ a)
IndArg (δ A i γ) U a = A + IndArg γ U (π₁ a)

-- Given the assumptions of an inductive occurence in a value we can compute
-- its index.
IndIndex : {I : Set}{E : Set}
          (γ : OP I E)(U : I -> Set) ->
          (a : Args γ U) -> IndArg γ U a -> I
IndIndex (ι e)     U _	      ()
IndIndex (σ A γ)   U arg c       = IndIndex (γ (π₀ arg)) U (π₁ arg) c
IndIndex (δ A i γ) U arg (inl a) = i a
IndIndex (δ A i γ) U arg (inr a) = IndIndex γ U (π₁ arg) a

-- Given the assumptions of an inductive occurrence in a value we can compute
-- its value.
Ind : {I : Set}{E : Set}
      (γ : OP I E)(U : I -> Set) ->
      (a : Args γ U)(v : IndArg γ U a) -> U (IndIndex γ U a v)
Ind (ι e)     U _	      ()
Ind (σ A γ)   U arg c       = Ind (γ (π₀ arg)) U (π₁ arg) c
Ind (δ A i γ) U arg (inl a) = (π₀ arg) a
Ind (δ A i γ) U arg (inr a) = Ind γ U (π₁ arg) a

-- The type of induction hypotheses. Basically
--  forall assumptions, the predicate holds for an inductive occurrence with
--  those assumptions
IndHyp : {I : Set}{E : Set}
      (γ : OP I E)(U : I -> Set) ->
      (F : (i : I) -> U i -> Set)(a : Args γ U) -> Set
IndHyp γ U F a = (v : IndArg γ U a) -> F (IndIndex γ U a v) (Ind γ U a v)

IndHyp₁ : {I : Set}{E : Set}
      (γ : OP I E)(U : I -> Set) ->
      (F : (i : I) -> U i -> Set1)(a : Args γ U) -> Set1
IndHyp₁ γ U F a = (v : IndArg γ U a) -> F (IndIndex γ U a v) (Ind γ U a v)

-- If we can prove a predicate F for any values, we can construct the inductive
-- hypotheses for a given value.
-- Termination note: g will only be applied to values smaller than a
induction :
  {I : Set}{E : Set}
  (γ : OP I E)(U : I -> Set)
  (F : (i : I) -> U i -> Set)
  (g : (i : I)(u : U i) -> F i u)
  (a : Args γ U) -> IndHyp γ U F a
induction γ U F g a = \hyp -> g (IndIndex γ U a hyp) (Ind γ U a hyp)

induction₁ :
  {I : Set}{E : Set}
  (γ : OP I E)(U : I -> Set)
  (F : (i : I) -> U i -> Set1)
  (g : (i : I)(u : U i) -> F i u)
  (a : Args γ U) -> IndHyp₁ γ U F a
induction₁ γ U F g a = \hyp -> g (IndIndex γ U a hyp) (Ind γ U a hyp)

