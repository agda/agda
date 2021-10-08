{-# OPTIONS --without-K --rewriting #-}

module Generalize where

open import Agda.Primitive

-- Generalization in definitions

module Definitions where

  variable
    ℓ : Level
    A B C : Set ℓ
    A₀ B₀  : Set
    a b c : A

  -- Function signature

  id : A → A
  id x = x

  -- Module signature
  module M (a : A) where
    identity = a

  -- Data parameters and constructors

  data Eq (a : A) : A → Setω where
    refl  : Eq a a
    trans : Eq a b → Eq b c → Eq a c

  record R (a : A) : Set₁ where
    field
      fld : B₀

    open M a

    alias = fld

    K : B → C → B
    K x _ = x

    field
      fld₁ : B₀

-- Original content (postulates only)

data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡_

{-# BUILTIN REWRITE _≡_ #-}

------------------------------------------------------------------

postulate   Con     :                       Set
postulate   Ty      : (Γ : Con) →           Set
postulate   Tms     : (Γ Δ : Con) →         Set
postulate   Tm      : (Γ : Con)(A : Ty Γ) → Set

------------------------------------------------------------------

variable    {Γ Δ Θ} :              Con
postulate   •       :              Con       -- • is \bub
postulate   _▹_     : ∀ Γ → Ty Γ → Con       -- ▹ is \tw2
infixl 5    _▹_

variable    {A B C} :                  Ty _
postulate   _∘ᵀ_    : Ty Δ → Tms Γ Δ → Ty Γ
infixl 6    _∘ᵀ_

variable    {σ δ ν} :                                 Tms _ _
postulate   _∘_     : Tms Θ Δ → Tms Γ Θ →             Tms Γ Δ
infixr 7    _∘_
postulate   id      :                                 Tms Γ Γ
postulate   ε       :                                 Tms Γ •
postulate   _,_     : (σ : Tms Γ Δ) → Tm Γ (A ∘ᵀ σ) → Tms Γ (Δ ▹ A)
infixl 5    _,_
postulate   π₁      : Tms Γ (Δ ▹ A) →                 Tms Γ Δ

variable    {t u v} :                          Tm _ _
postulate   π₂      : (σ : Tms Γ (Δ ▹ A)) →    Tm Γ (A ∘ᵀ π₁ σ)
postulate   _∘ᵗ_    : Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A ∘ᵀ σ)
infixl 6    _∘ᵗ_

postulate   ass     :   (σ ∘ δ) ∘ ν ≡ σ ∘ δ ∘ ν
{-# REWRITE ass #-}
postulate   idl     :        id ∘ δ ≡ δ
{-# REWRITE idl #-}
postulate   idr     :        δ ∘ id ≡ δ
{-# REWRITE idr #-}
postulate   εη      :             δ ≡ ε  -- can't rewrite, so we specialize this in the next two cases
postulate   εηid    :            id ≡ ε
{-# REWRITE εηid #-}
postulate   εη∘     :         ε ∘ δ ≡ ε
{-# REWRITE εη∘ #-}
postulate   ,β₁     :    π₁ (δ , t) ≡ δ
{-# REWRITE ,β₁ #-}
postulate   ,β₂     :    π₂ (δ , t) ≡ t
{-# REWRITE ,β₂ #-}
postulate   ,η      : (π₁ δ , π₂ δ) ≡ δ
{-# REWRITE ,η #-}
postulate   [id]ᵀ   :       A ∘ᵀ id ≡ A
{-# REWRITE [id]ᵀ #-}
postulate   [∘]ᵀ    :   A ∘ᵀ δ ∘ᵀ σ ≡ A ∘ᵀ δ ∘ σ
{-# REWRITE [∘]ᵀ #-}
postulate   ,∘      :   (δ , t) ∘ σ ≡ δ ∘ σ , t ∘ᵗ σ
{-# REWRITE ,∘ #-}

postulate   [∘]ᵗ    :   t ∘ᵗ σ ∘ᵗ δ ≡ t ∘ᵗ σ ∘ δ
{-# REWRITE [∘]ᵗ #-}
postulate   π₁∘     :      π₁ δ ∘ σ ≡ π₁ (δ ∘ σ)
{-# REWRITE π₁∘ #-}
postulate   π₂∘     :     π₂ δ ∘ᵗ σ ≡ π₂ (δ ∘ σ)
{-# REWRITE π₂∘ #-}
postulate   ∘id     :       t ∘ᵗ id ≡ t
{-# REWRITE ∘id #-}

_↑_ : ∀ σ A → Tms (Γ ▹ A ∘ᵀ σ) (Δ ▹ A)
σ ↑ A = σ ∘ π₁ id , π₂ id

⟨_⟩ : Tm Γ A → Tms Γ (Γ ▹ A)
⟨ t ⟩ = id , t

------------------------------------------------------------------

postulate   U       : Ty Γ
variable    {a b c} : Tm _ U
postulate   El      : Tm Γ U → Ty Γ
postulate   U[]     : U ∘ᵀ σ ≡ U
{-# REWRITE U[] #-}
postulate   El[]    : El a ∘ᵀ σ ≡ El (a ∘ᵗ σ)
{-# REWRITE El[] #-}

------------------------------------------------------------------

postulate   Π       : (a : Tm Γ U) → Ty (Γ ▹ El a) → Ty Γ
postulate   Π[]     : Π a B ∘ᵀ σ ≡ Π (a ∘ᵗ σ) (B ∘ᵀ σ ↑ El a)
{-# REWRITE Π[] #-}
postulate   app     : Tm Γ (Π a B) → Tm (Γ ▹ El a) B
postulate   app[]   : app t ∘ᵗ (σ ↑ El a) ≡ app (t ∘ᵗ σ)
{-# REWRITE app[] #-}
