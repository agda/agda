%include agda.fmt

\subsection{Typing rules}
\label{well-typed}

\AgdaHide{
\begin{code}
module Issue854.WellTyped where

open import Function hiding (_∋_)
open import Data.Fin
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Binary.Pointwise
open import Data.List.Relation.Binary.Subset.Propositional

open import Data.List.Membership.Propositional
open import Issue854.Terms
open import Issue854.Types
open import Issue854.Context as Ctx hiding (Rel; index)

infix 1 _⊢^v_∶_
infix 1 _⊢^c_∶_
infix 1 _⊢^cs_∶_
infixl 3 _·_
\end{code}
}

\begin{code}
mutual

  data _⊢^v_∶_ (Γ : Ctx) : VTerm → VType → Set where

    var : ∀ {V} →  (m : Γ ∋ V) →
                   -----------------------
                   Γ ⊢^v var (toℕ (Ctx.index m)) ∶ V


    con : ∀ {Δ P A p k} →  (m : (P , A) ∈ Δ) → Γ ⊢^v p ∶ P →
                           Γ ▻ A ⊢^v k ∶ μ Δ →
                           -------------------------------
                           Γ ⊢^v con (toℕ (index m)) p ∶ μ Δ

    thunk : ∀ {Σ V c} →  Γ ⊢^c c ∶ Σ ⋆ V →
                         -------------------
                         Γ ⊢^v thunk c ∶ ⁅ Σ ⋆ V ⁆

    ⟨⟩ :  ------------
          Γ ⊢^v ⟨⟩ ∶ 𝟙

    _,_ : ∀ {U V u v} →  Γ ⊢^v u ∶ U → Γ ⊢^v v ∶ V →
                         -------------------------
                         Γ ⊢^v u , v ∶ U ⊗ V

    𝟘-elim : ∀ {V v} →  Γ ⊢^v v ∶ 𝟘 →
                        -------------
                        Γ ⊢^v 𝟘-elim v ∶ V

    ι₁ : ∀ {U V u} →  Γ ⊢^v u ∶ U →
                      -------------
                      Γ ⊢^v ι₁ u ∶ U ⊕ V

    ι₂ : ∀ {U V v} →  Γ ⊢^v v ∶ V →
                      -------------
                      Γ ⊢^v ι₂ v ∶ U ⊕ V

  -- Pointwise version of the computation judgement.
  _⊢^cs_∶_ : Ctx → List CTerm → List CType → Set
  _⊢^cs_∶_ Γ = Pointwise (_⊢^c_∶_ Γ)

  data _⊢^c_∶_ (Γ : Ctx) : CTerm → CType → Set where

    return : ∀ {Σ V v} →  Γ ⊢^v v ∶ V →
                          -----------
                          Γ ⊢^c return v ∶ Σ ⋆ V

    _to_ : ∀ {Σ Σ′ Σ″ U V c k} →  Γ ⊢^c c ∶ Σ ⋆ U → Γ ▻ U ⊢^c k ∶ Σ′ ⋆ V →
                                  Σ ⊆ Σ″ → Σ′ ⊆ Σ″ →
                                  ---------------------------------
                                  Γ ⊢^c c to k ∶ Σ″ ⋆ V

    force : ∀ {C t} →  Γ ⊢^v t ∶ ⁅ C ⁆ →
                       ----------------
                       Γ ⊢^c force t ∶ C

    let′_be_ : ∀ {V C v k} →  Γ ⊢^v v ∶ V → Γ ▻ V ⊢^c k ∶ C →
                              -----------------------------
                              Γ ⊢^c let′ v be k ∶ C

    ⟨⟩ :  -------------
          Γ ⊢^c ⟨⟩ ∶ ⊤′

    split : ∀ {U V C p k} →  Γ ⊢^v p ∶ U ⊗ V → Γ ▻ U ▻ V ⊢^c k ∶ C →
                             -------------------------------------
                             Γ ⊢^c split p k ∶ C

    π₁ : ∀ {B C p} →  Γ ⊢^c p ∶ B & C →
                      --------------------
                      Γ ⊢^c π₁ p ∶ B

    π₂ : ∀ {B C p} →  Γ ⊢^c p ∶ B & C →
                      --------------------
                      Γ ⊢^c π₂ p ∶ C

    _,_ : ∀ {B C b c} →  Γ ⊢^c b ∶ B → Γ ⊢^c c ∶ C →
                         -------------------------
                         Γ ⊢^c b , c ∶ B & C

    ƛ_ : ∀ {V C b} →  Γ ▻ V ⊢^c b ∶ C →
                      ---------------
                      Γ ⊢^c ƛ b ∶ V ⇒ C

    _·_ : ∀ {V C f a} →  Γ ⊢^c f ∶ V ⇒ C → Γ ⊢^v a ∶ V →
                         -----------------------------
                         Γ ⊢^c f · a ∶ C

    op : ∀ {Σ P A} →  (m : (P , A) ∈ Σ) →
                      -----------------
                      Γ ⊢^c op (toℕ (Any.index m)) ∶ P ⇒ Σ ⋆ A

    iter : ∀ {Δ C φ x} →  Γ ⊢^cs φ ∶ Alg Δ C → Γ ⊢^v x ∶ μ Δ →
                          --------------------------------------
                          Γ ⊢^c iter φ x ∶ C

    run : ∀ {Σ Σ′ Σ″ Σ‴ I U V φ u} →  Γ ⊢^cs φ ∶ PHomo Σ′ U I Σ″ V →
                                      Γ ⊢^c u ∶ Σ ⋆ U → Σ ⊆ (Σ′ ++ Σ″) → Σ″ ⊆ Σ‴ →
                                      ---------------------------------------
                                      Γ ⊢^c run φ u ∶ I ⇒ Σ‴ ⋆ V
\end{code}
