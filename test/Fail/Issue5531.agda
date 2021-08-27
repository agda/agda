{-# OPTIONS --type-in-type --rewriting #-}

open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

coe : {A B : Set} → A ≡ B → A → B
coe refl x = x

{-# BUILTIN REWRITE _≡_ #-}

Tel = Set
U = Set

variable
  Δ : Tel
  A B : Δ → U
  δ₀ δ₁ : Δ

postulate
  IdTel : (Δ : Tel)(δ₀ δ₁ : Δ) → Tel
  Id : (A : Δ → U){δ₀ δ₁ : Δ}(δ₂ : IdTel Δ δ₀ δ₁) → A δ₀ → A δ₁ → U
  ap : {A : Δ → U}(a : (δ : Δ) → A δ)
       → {δ₀ δ₁ : Δ}(δ₂ : IdTel Δ δ₀ δ₁) → Id A δ₂ (a δ₀) (a δ₁)

  idTel-sigma : {a₀ : A δ₀}{a₁ : A δ₁}
                → IdTel (Σ Δ A) (δ₀ , a₀) (δ₁ , a₁)
                  ≡ Σ (IdTel Δ δ₀ δ₁) (λ δ₂ → Id A δ₂ a₀ a₁)
  {-# REWRITE idTel-sigma #-}

  id-u : {A₀ A₁ : U}{δ₂ : IdTel Δ δ₀ δ₁}
         → Id {Δ = Δ}(λ _ → U) δ₂ A₀ A₁ ≡ (A₀ → A₁ → U)
  {-# REWRITE id-u #-}

  id-ap : {δ₂ : IdTel Δ δ₀ δ₁}{a₀ : A δ₀}{a₁ : A δ₁}
          → Id A δ₂ a₀ a₁ ≡ ap {A = λ _ → U} A δ₂ a₀ a₁

  ap-sigma : {δ₂ : IdTel Δ δ₀ δ₁}{a₀ : A δ₀}{a₁ : A δ₁}
             {B : (δ : Δ) → A δ → U}
             {b₀ : B δ₀ a₀}{b₁ : B δ₁ a₁}→
             ap {Δ = Δ}{A = λ _ → U} (λ δ → Σ (A δ) (B δ))
                δ₂ (a₀ , b₀) (a₁ , b₁) ≡
                Σ (Id A δ₂ a₀ a₁) λ a₂ → Id {Δ = Σ Δ A} (λ (δ , a) → B δ a) (δ₂ , a₂) b₀ b₁
  {-# REWRITE ap-sigma #-}
  {-# REWRITE id-ap #-}

  ap-proj₁ : {δ₂ : IdTel Δ δ₀ δ₁}
             {B : (δ : Δ) → A δ → U}
             {ab : (δ : Δ) → Σ (A δ) (B δ)}
             → ap {Δ = Δ}{A = A}(λ δ → fst (ab δ)) δ₂
               ≡ fst (ap ab δ₂)
