-- Andreas, 2023-05-29, issue #6542, test case by Oskar Eriksson
-- Temporary regression in 2.6.4 (master).
-- Fixed by rolling back type-directed occurs checker.

open import Agda.Builtin.Sigma
import Issue6542.Import as I

module Issue6542 (M : Set) {{rel : I.R M}} where

open I M

escape : ∀ {A} → Γ ⊩ A → Γ ⊢ A
escape (Tᵣ ⊢Γ) = Tⱼ ⊢Γ

postulate
  escape′ : ([A] : Γ ⊩ A)
           → Γ ⊩ A / [A]
           → Γ ⊢ A
  magic : {A : Set} → A
  liftSubstS : ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
               ([A] : Γ ⊩ᵛ A / [Γ])
               ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             → (Δ ∙ subst σ A) ⊩ˢ liftSubst σ ∷ Γ ∙ A / [Γ] ∙ [A]
                               / (⊢Δ ∙ escape (fst (unwrap [A] _ _ ⊢Δ [σ])))
  liftSubstSEq : ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
                 ([A] : Γ ⊩ᵛ A / [Γ])
                 ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                 ([σ]′ : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ / [σ])
               → (Δ ∙ subst σ A) ⊩ˢ liftSubst σ ∷ Γ ∙ A / [Γ] ∙ [A]
                             / (⊢Δ ∙ escape (fst (unwrap [A] _ _ ⊢Δ [σ])))
                             / liftSubstS {A = A} [Γ] ⊢Δ [A] [σ]

foo : ([Γ] : ⊩ᵛ Γ)
    → (⊢Δ   : ⊢ Δ)
      ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
      ([A] : Γ ∙ T ⊩ᵛ A / [Γ] ∙ (Tᵛ [Γ]))
      ([B] : Γ ∙ T ∙ A ⊩ᵛ B / [Γ] ∙ (Tᵛ [Γ]) ∙ [A])
    → Set₁
foo {Γ = Γ} {Δ = Δ} {σ} {A} {B} [Γ] ⊢Δ [σ] [A] [B] =
  let [T] = Tᵛ [Γ]
      ⊢T = Tⱼ ⊢Δ
      [σA] = fst (unwrap [A] _ (liftSubst σ) (⊢Δ ∙ ⊢T)
                             (liftSubstS {A = T} [Γ] ⊢Δ [T] [σ]))
      ⊢A = escape [σA]
      ⊢ΔT = ⊢Δ ∙ Tⱼ ⊢Δ
      [ΓT] = [Γ] ∙ [T]
      ⊢ΔTA = ⊢Δ ∙ ⊢T ∙ ⊢A
      σA = subst (liftSubst σ) A
      [σ⇑⇑] = liftSubstS {A = A} {σ = liftSubst σ} [ΓT] ⊢ΔT [A]
                         (liftSubstS {A = T} {σ = σ} [Γ] ⊢Δ [T] [σ])
      [σ⇑]′ : Δ ∙ T ⊩ˢ liftSubst σ ∷ Γ ∙ T / [ΓT] / ⊢ΔT
                     / liftSubstS {A = T} {σ = σ} [Γ] ⊢Δ [T] [σ]
      [σ⇑]′ = magic
      [σ⇑⇑]′ = liftSubstSEq {A = A} [ΓT] ⊢ΔT [A]
                            (liftSubstS {A = T} [Γ] ⊢Δ [T] [σ]) [σ⇑]′
      [σB] =  fst (unwrap [B] _ (liftSubst (liftSubst σ)) ⊢ΔTA [σ⇑⇑])
      qwer = snd (unwrap [B] _ _ ⊢ΔTA [σ⇑⇑]) [σ⇑⇑]′
      qwe = escape′ [σB] qwer
  in  Set
