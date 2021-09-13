-- Andreas, 2021-09-13, issue #5544 reported by Jason Hu
-- Serialization crashed with an uninstantiated meta-variable

{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Agda.Primitive
open import Agda.Builtin.Nat using (suc) renaming (Nat to ℕ)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma renaming (fst to proj₁; snd to proj₂)

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

infixr 2 _×_

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A λ (x : A) → B

infix  4 -,_

-,_ : ∀ {a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
-, y = _ , y

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

foldr : ∀ {a b} {A : Set a}{B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

length : ∀{a} {A : Set a} → List A → ℕ
length = foldr (λ _ → suc) 0

infix 2 _∶_∈_
data _∶_∈_ {a} {A : Set a} : ℕ → A → List A → Set a where
  here : ∀ {x l} → 0 ∶ x ∈ x ∷ l
  there : ∀ {n x y l} → n ∶ x ∈ l → suc n ∶ x ∈ y ∷ l

-- types
data Typ : Set where
  N   : Typ

Ctx : Set
Ctx = List Typ

variable
  S T U   : Typ
  Γ Γ′ Γ″ : Ctx
  Δ Δ′ Δ″ : Ctx

mutual

  infixl 11 _[_]
  data Exp : Set where
    v    : (x : ℕ) → Exp
    ze   : Exp
    su   : Exp → Exp
    _[_] : Exp → Subst → Exp

  infixl 3 _∘_
  data Subst : Set where
    ↑   : Subst
    I   : Subst
    _∘_ : Subst → Subst → Subst
    _,_ : Subst → Exp → Subst


variable
  t t′ t″ : Exp
  s s′ : Exp
  σ σ′ : Subst
  τ τ′ : Subst

module Typing where

  infix 4 _⊢_∶_ _⊢s_∶_

  mutual

    data _⊢_∶_ : Ctx → Exp → Typ → Set where

      su-I    : Γ ⊢ t ∶ N →
                -------------
                Γ ⊢ su t ∶ N

      t[σ]    : Δ ⊢ t ∶ T →
                Γ ⊢s σ ∶ Δ →
                ----------------
                Γ ⊢ t [ σ ] ∶ T

    data _⊢s_∶_ : Ctx → Subst → Ctx → Set where
      S-↑ : S ∷ Γ ⊢s ↑ ∶ Γ
      S-I : Γ ⊢s I ∶ Γ
      S-∘ : Γ ⊢s τ ∶ Γ′ →
            Γ′ ⊢s σ ∶ Γ″ →
            ----------------
            Γ ⊢s σ ∘ τ ∶ Γ″

  infix 4 _⊢_≈_∶_

  data _⊢_≈_∶_ : Ctx → Exp → Exp → Typ → Set where
      su-cong  : Γ ⊢ t                   ≈ t′ ∶ N →
                 ---------------------------------------
                 Γ ⊢ su t                ≈ su t′ ∶ N
      su-[]    : Γ ⊢s σ ∶ Δ →
                 Δ ⊢ t ∶ N →
                 --------------------------------------------
                 Γ ⊢ su t [ σ ]          ≈ su (t [ σ ]) ∶ N
      [∘]      : Γ ⊢s τ ∶ Γ′ →
                 Γ′ ⊢s σ ∶ Γ″ →
                 Γ″ ⊢ t ∶ T →
                 -------------------------------------------
                 Γ ⊢ t [ σ ∘ τ ]         ≈ t [ σ ] [ τ ] ∶ T
      [,]-v-su : ∀ {x} →
                 Γ ⊢s σ ∶ Δ →
                 Γ ⊢ s ∶ S →
                 x ∶ T ∈ Δ →
                 ---------------------------------------
                 Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T
      ≈-sym    : Γ ⊢ t                   ≈ t′ ∶ T →
                 ----------------------------------
                 Γ ⊢ t′                  ≈ t ∶ T
      ≈-trans  : Γ ⊢ t                   ≈ t′ ∶ T →
                 Γ ⊢ t′                  ≈ t″ ∶ T →
                 -----------------------------------
                 Γ ⊢ t                   ≈ t″ ∶ T



open Typing

data Nf : Set where
  su : Nf → Nf

Nf⇒Exp : Nf → Exp
Nf⇒Exp (su w) = su (Nf⇒Exp w)


mutual
  data D : Set where
    su : D → D

  data Df : Set where
    ↓ : (T : Typ) → (a : D) → Df

infix 4 Rf_-_↘_

data Rf_-_↘_ : ℕ → Df → Nf → Set where
    Rsu : ∀ n {a w} →
          Rf n - ↓ N a ↘ w →
          --------------------
          Rf n - ↓ N (su a) ↘ su w

weaken : Ctx → Subst
weaken []      = I
weaken (T ∷ Γ) = weaken Γ ∘ ↑

weaken⊨s : ∀ Δ → Δ ++ Γ ⊢s weaken Δ ∶ Γ
weaken⊨s []      = S-I
weaken⊨s (T ∷ Δ) = S-∘ S-↑ (weaken⊨s Δ)

Pred : Set₁
Pred = Exp → D → Set

DPred : Set₁
DPred = Ctx → Pred

record TopPred Δ σ t a T : Set where
  field
    nf  : Nf
    ↘nf : Rf length Δ - ↓ T a ↘ nf
    ≈nf : Δ ⊢ t [ σ ] ≈ Nf⇒Exp nf ∶ T

record Top T Γ t a : Set where
  field
    t∶T  : Γ ⊢ t ∶ T
    krip : ∀ Δ → TopPred (Δ ++ Γ) (weaken Δ) t a T


⟦_⟧ : Typ → DPred
⟦ N ⟧     = Top N


inv-t[σ] : Γ ⊢ t [ σ ] ∶ T →
           ∃ λ Δ → Δ ⊢ t ∶ T × Γ ⊢s σ ∶ Δ
inv-t[σ] (t[σ] t σ) = -, t , σ


infix 4 _∼∈⟦_⟧_ _⊨_∶_

record _∼∈⟦_⟧_ σ Γ Δ : Set where
  field
    ⊢σ   : Δ ⊢s σ ∶ Γ

record Intp Δ σ t T : Set where
  field
    ⟦t⟧  : D
    tT   : ⟦ T ⟧ Δ (t [ σ ]) ⟦t⟧

_⊨_∶_ : Ctx → Exp → Typ → Set
Γ ⊨ t ∶ T = ∀ {σ Δ} → σ ∼∈⟦ Γ ⟧ Δ → Intp Δ σ t T



su-I′ : Γ ⊨ t ∶ N →
        ---------------
        Γ ⊨ su t ∶ N
su-I′ t σ∼ρ = record
  { ⟦t⟧  = su ⟦t⟧
  ; tT   =
    let _ , t , σ = inv-t[σ] t∶T
    in record
    { t∶T  = t[σ] (su-I t) σ
    ; krip = λ Δ →
      let open TopPred (krip Δ)
          wΔ = weaken⊨s Δ
      in record
      { nf  = su nf
      ; ↘nf = Rsu _ ↘nf  -- Would succeed if `_` was changed to `?`
      ; ≈nf = ≈-trans (≈-sym ([∘] wΔ σ (su-I t)))
              (≈-trans (su-[] (S-∘ wΔ σ) t)
                       (su-cong (≈-trans ([∘] wΔ σ t)
                                         ≈nf)))
      }
    }
  }
  where open _∼∈⟦_⟧_ σ∼ρ
        open Intp (t σ∼ρ)
        open Top tT

-- Should succeed.
