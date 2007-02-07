
module IID-Proof where

import Logic.ChainReasoning as Chain

open import LF
open import Identity
open import IID
open import IIDr
open import IID-Proof-Setup
open import DefinitionalEquality

Ug : {I : Set} -> OPg I -> I -> Set
Ug γ i = Ur (ε γ) i

introg : {I : Set}(γ : OPg I)(a : Args γ (Ug γ)) -> Ug γ (index γ (Ug γ) a)
introg γ a = intror (g→rArgs γ (Ug γ) a)

-- The elimination rule.
elim-Ug : {I : Set}(γ : OPg I)(C : (i : I) -> Ug γ i -> Set) ->
          ((a : Args γ (Ug γ)) -> IndHyp γ (Ug γ) C a -> C (index γ (Ug γ) a) (introg γ a)) ->
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
        h' = r→gIndHyp γ U C i a h

        -- Our method m can be applied to the converted argument and induction
        -- hypothesis. This gets us almost all the way.
        lem₁ : C (index γ U a') (intror (g→rArgs γ U a'))
        lem₁ = m a' h'

        -- Now we just have to use the fact that the computed index is the same
        -- as our input index, and that g→rArgs ∘ r→gArgs is the identity.
        -- r←→gArgs-subst will perform the elimination of the identity proof.
        conclusion : C i (intror a)
        conclusion = r←→gArgs-subst γ U (\i a -> C i (intror a)) i a lem₁

open module Chain-≡ = Chain.Poly.Heterogenous _≡_ (\x -> refl-≡) trans-≡

-- What remains is to prove that the reduction behaviour of the elimination
-- rule is the correct one. I.e that
--  elim-Ug C m (index a) (introg a) ≡ m a (induction C (elim-Ug C m) a)
elim-Ug-reduction :
    {I : Set}(γ : OPg I)(C : (i : I) -> Ug γ i -> Set)
    (m : (a : Args γ (Ug γ)) -> IndHyp γ (Ug γ) C a -> C (index γ (Ug γ) a) (introg γ a))
    (a : Args γ (Ug γ)) ->
    elim-Ug γ C m (index γ (Ug γ) a) (introg γ a)
    ≡ m a (induction γ (Ug γ) C (elim-Ug γ C m) a)
elim-Ug-reduction γ C m a =

 chain> elim-Ug γ C m (index γ (Ug γ) a) (introg γ a)

      -- Unfolding the definition of elim-Ug we get
    === r←→gArgs-subst γ U C' i ra
          (m gra (r→gih \hyp -> elim-Ug γ C m (r-ind-index hyp) (r-ind-value hyp)))
    by  refl-≡

     -- Now (and this is the key step), since we started with a value in the
     -- generalised type we know that the identity proof is refl, so
     -- r←→gArgs-subst is the identity.
    === m gra (r→gih \hyp -> elim-Ug γ C m (r-ind-index hyp) (r-ind-value hyp))
    by  r←→gArgs-subst-identity γ U C' a _

    -- We use congruence to prove separately that gra ≡ a and that the computed
    -- induction hypothesis is the one we need.
    === m a (\hyp -> elim-Ug γ C m (g-ind-index hyp) (g-ind-value hyp))
    by  cong₂-≡' m (g←→rArgs-identity γ U a)

        -- The induction hypotheses match
        (η-≡ \hyp₀ hyp₁ hyp₀=hyp₁ ->
         chain> r→gih (\hyp -> elim-Ug γ C m (r-ind-index hyp) (r-ind-value hyp)) hyp₀

            -- Unfolding the definition of r→gih we get
            === g→rIndArg-subst γ U C i ra hyp₀
                  (elim-Ug γ C m (r-ind-index (g→rIndArg γ U i ra hyp₀))
                                 (r-ind-value (g→rIndArg γ U i ra hyp₀))
                  )
            by  refl-≡

            -- g→rIndArg-subst is definitionally the identity.
            === elim-Ug γ C m (r-ind-index (g→rIndArg γ U i ra hyp₀))
                              (r-ind-value (g→rIndArg γ U i ra hyp₀))

            by  g→rIndArg-subst-identity γ U C i ra hyp₀ _

            -- We can turn the restricted inductive occurrence into a
            -- generalised occurrence.
            === elim-Ug γ C m (IndIndex γ U gra hyp₀) (Ind γ U gra hyp₀)

            by  g→rIndArg-subst γ U
                  (\j b -> elim-Ug γ C m (r-ind-index (g→rIndArg γ U i ra hyp₀))
                                         (r-ind-value (g→rIndArg γ U i ra hyp₀))
                           ≡ elim-Ug γ C m j b
                  ) i ra hyp₀ refl-≡

            -- Finally we have gra ≡ a and hyp₀ ≡ hyp₁ so we're done.
            === elim-Ug γ C m (IndIndex γ U a hyp₁) (Ind γ U a hyp₁)

            by  cong₂-≡' (\a hyp -> elim-Ug γ C m (IndIndex γ U a hyp)
                                                  (Ind      γ U a hyp)
                         ) (g←→rArgs-identity γ U a) hyp₀=hyp₁
        )

    -- Writing it in a nicer way:
    === m a (induction γ (Ug γ) C (elim-Ug γ C m) a)
    by  refl-≡

  where
    U   = Ug γ
    i   = index γ U a
    ra  = g→rArgs γ U a
    gra = r→gArgs γ U i ra

    r→gih = r→gIndHyp γ U C i ra

    r-ind-index = IndIndex (ε γ i) (Ur (ε γ)) ra
    r-ind-value = Ind      (ε γ i) (Ur (ε γ)) ra

    g-ind-index = IndIndex γ U a
    g-ind-value = Ind      γ U a

    C'  = \i a -> C i (intror a)

