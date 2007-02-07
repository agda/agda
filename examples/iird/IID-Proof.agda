
module IID-Proof where

open import LF
open import Identity
open import IID
open import IIDr
open import IID-Proof-Setup

Ug : {I : Set} -> OPg I -> I -> Set
Ug γ i = Ur (ε γ) i

introg : {I : Set}(γ : OPg I)(a : Args γ (Ug γ)) -> Ug γ (Index γ (Ug γ) a)
introg γ a = intror (g→rArgs γ (Ug γ) a)

-- The elimination rule.
elim-Ug : {I : Set}(γ : OPg I)(C : (i : I) -> Ug γ i -> Set) ->
	  ((a : Args γ (Ug γ)) -> IndHyp γ (Ug γ) C a -> C (Index γ (Ug γ) a) (introg γ a)) ->
	  (i : I)(u : Ug γ i) -> C i u
elim-Ug {I} γ C m = elim-Ur (ε γ) C step    -- eliminate the restricted type
  where
    U = Ug γ

    -- we've got a method to take care of inductive occurrences for general families (m),
    -- but we need something to handle the restricted encoding.
    step : (i : I)(a : rArgs (ε γ) U i) -> IndHyp (ε γ i) U C a -> C i (intror a)
    step i a h = conclusion
      where
	-- First convert the argument to a general argument
	a' : Args γ U
	a' = r→gArgs γ U i a

	-- Next convert our induction hypothesis to an hypothesis for a general family
	h' : IndHyp γ U C a'
	h' v' = g→rIndArg-subst γ U C i a v' (h v)
	  where
	    -- Assumptions will have to be converted the other direction
	    v : IndArg (ε γ i) U a
	    v = g→rIndArg γ U i a v'

	-- Our method m can be applied to the converted argument and induction
	-- hypothesis. This gets us almost all the way.
	lem₁ : C (Index γ U a') (intror (g→rArgs γ U a'))
	lem₁ = m a' h'

	-- Now we just have to use the fact that the computed index is the same
	-- as our input index, and that g→rArgs ∘ r→gArgs is the identity.
	conclusion : C i (intror a)
	conclusion = r←→gArgs-subst γ U (\i a -> C i (intror a)) i a lem₁

