-- {-# OPTIONS -v tc.size.solve:100 #-}

open import Agda.Builtin.Size

data Cx (U : Set) : Set where
  ⌀   : Cx U
  _,_ : Cx U → U → Cx U

module _ {U : Set} where
  data _⊆_ : Cx U → Cx U → Set where
    done : ⌀ ⊆ ⌀
    skip : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊆ (Γ′ , A)
    keep : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → (Γ , A) ⊆ (Γ′ , A)

  data _∈_ (A : U) : Cx U → Set where
    top : ∀ {Γ} → A ∈ (Γ , A)
    pop : ∀ {C Γ} → A ∈ Γ → A ∈ (Γ , C)

  mono∈ : ∀ {A Γ Γ′} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ done     ()
  mono∈ (skip η) i       = pop (mono∈ η i)
  mono∈ (keep η) top     = top
  mono∈ (keep η) (pop i) = pop (mono∈ η i)

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {⌀}     = done
  refl⊆ {Γ , A} = keep refl⊆

infixr 3 _⊃_
data Ty : Set where
  ι   : Ty
  _⊃_ : Ty → Ty → Ty

infix 1 _⊢⟨_⟩_
data _⊢⟨_⟩_ (Γ : Cx Ty) : Size → Ty → Set where
  var : ∀ {p A}                     → A ∈ Γ → Γ ⊢⟨ p ⟩ A
  lam : ∀ {n A B} {o : Size< n}    → Γ , A ⊢⟨ o ⟩ B → Γ ⊢⟨ n ⟩ A ⊃ B
  app : ∀ {m A B} {l k : Size< m} → Γ ⊢⟨ k ⟩ A ⊃ B → Γ ⊢⟨ l ⟩ A → Γ ⊢⟨ m ⟩ B

mono⊢ : ∀ {m A Γ Γ′} → Γ ⊆ Γ′ → Γ ⊢⟨ m ⟩ A → Γ′ ⊢⟨ m ⟩ A
mono⊢ η (var i)   = var (mono∈ η i)
mono⊢ η (lam t)   = lam (mono⊢ (keep η) t)
mono⊢ η (app t u) = app (mono⊢ η t) (mono⊢ η u)

det : ∀ {i A B Γ} {j : Size< i} → Γ ⊢⟨ j ⟩ A ⊃ B → Γ , A ⊢⟨ i ⟩ B
det t = app (mono⊢ (skip refl⊆) t) (var top)

ccont : ∀ {m A B Γ} → Γ ⊢⟨ ↑ ↑ ↑ ↑ m ⟩ (A ⊃ A ⊃ B) ⊃ A ⊃ B
ccont = lam (lam (app (app (var (pop top)) (var top)) (var top)))

cont : ∀ {m A B Γ} {m′ : Size< m} → (Γ , A) , A ⊢⟨ ↑ ↑ m′ ⟩ B → Γ , A ⊢⟨ ↑ ↑ ↑ ↑ ↑ m ⟩ B
cont {m = m} {m′ = m′} t = det (app {m = ↑ ↑ ↑ ↑ m} ccont (lam (lam t)))

cont′ : ∀ {q A B Γ} {r : Size< q} → (Γ , A) , A ⊢⟨ {!q!} ⟩ B → Γ , A ⊢⟨ {!!} ⟩ B
cont′ t = det (app ccont (lam (lam t)))
