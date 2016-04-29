------------------------------------------------------------------------
-- A small definition of a dependently typed language, using the
-- technique from McBride's "Outrageous but Meaningful Coincidences"
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Prelude

record ⊤ : Set₁ where

record Σ (A : Set₁) (B : A → Set₁) : Set₁ where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

uncurry : ∀ {A : Set₁} {B : A → Set₁} {C : Σ A B → Set₁} →
          ((x : A) (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

record ↑ (A : Set) : Set₁ where
  constructor lift
  field
    lower : A

------------------------------------------------------------------------
-- Contexts

-- The definition of contexts is parametrised by a universe.

module Context (U : Set₁) (El : U → Set₁) where

  mutual

    -- Contexts.

    data Ctxt : Set₁ where
      ε   : Ctxt
      _▻_ : (Γ : Ctxt) → Ty Γ → Ctxt

    -- Types.

    Ty : Ctxt → Set₁
    Ty Γ = Env Γ → U

    -- Environments.

    Env : Ctxt → Set₁
    Env ε       = ⊤
    Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (σ γ)

  -- Variables (de Bruijn indices).

  infix 4 _∋_

  data _∋_ : (Γ : Ctxt) → Ty Γ → Set₁ where
    zero : ∀ {Γ σ}               → Γ ▻ σ ∋ λ γ → σ (proj₁ γ)
    suc  : ∀ {Γ σ τ} (x : Γ ∋ τ) → Γ ▻ σ ∋ λ γ → τ (proj₁ γ)

  -- A lookup function.

  lookup : ∀ {Γ σ} → Γ ∋ σ → (γ : Env Γ) → El (σ γ)
  lookup zero    (γ , v) = v
  lookup (suc x) (γ , v) = lookup x γ

------------------------------------------------------------------------
-- A universe

mutual

  data U : Set₁ where
    set : U
    el  : Set → U
    σ π : (a : U) → (El a → U) → U

  El : U → Set₁
  El set     = Set
  El (el A)  = ↑ A
  El (σ a b) = Σ (El a) λ x → El (b x)
  El (π a b) = (x : El a) → El (b x)

open Context U El

-- Abbreviations.

infixr 20 _⊗_
infixr 10 _⇾_

_⇾_ : U → U → U
a ⇾ b = π a λ _ → b

_⊗_ : U → U → U
a ⊗ b = σ a λ _ → b

-- Example.

raw-somethingU : U
raw-somethingU =
  σ set λ obj →
  σ (el obj ⇾ el obj ⇾ set) λ hom →
  (π (el obj) λ x → el (hom x x))
    ⊗
  (π (el obj) λ x → el (hom x x))

------------------------------------------------------------------------
-- A language

mutual

  infixl 30 _·_
  infix   4 _⊢_

  -- Syntax for types.

  data Type (Γ : Ctxt) : Ty Γ → Set₁ where
    set : Type Γ (λ _ → set)
    el  : (x : Γ ⊢ λ _ → set) → Type Γ (λ γ → el (⟦ x ⟧ γ))
    σ   : ∀ {a b} → Type Γ a → Type (Γ ▻ a) b →
          Type Γ (λ γ → σ (a γ) (λ v → b (γ , v)))
    π   : ∀ {a b} → Type Γ a → Type (Γ ▻ a) b →
          Type Γ (λ γ → π (a γ) (λ v → b (γ , v)))

  -- Terms.

  data _⊢_ (Γ : Ctxt) : Ty Γ → Set₁ where
    var : ∀ {a} → Γ ∋ a → Γ ⊢ a
    ƛ   : ∀ {a b} → Γ ▻ a ⊢ uncurry b →
          Γ ⊢ (λ γ → π (a γ) (λ v → b γ v))
    _·_ : ∀ {a} {b : (γ : Env Γ) → El (a γ) → U} →
          Γ ⊢ (λ γ → π (a γ) (λ v → b γ v)) →
          (t₂ : Γ ⊢ a) → Γ ⊢ (λ γ → b γ (⟦ t₂ ⟧ γ))

  -- The semantics of a term.

  ⟦_⟧ : ∀ {Γ a} → Γ ⊢ a → (γ : Env Γ) → El (a γ)
  ⟦ var x   ⟧ γ = lookup x γ
  ⟦ ƛ t     ⟧ γ = λ v → ⟦ t ⟧ (γ , v)
  ⟦ t₁ · t₂ ⟧ γ = (⟦ t₁ ⟧ γ) (⟦ t₂ ⟧ γ)

-- Example.

raw-something : Type ε (λ _ → raw-somethingU)
raw-something =
   σ set
  (σ (π (el (var zero)) (π (el (var (suc zero))) set))
  (σ (π (el (var (suc zero)))
        (el (var (suc zero) · var zero · var zero)))
     (π (el (var (suc (suc zero))))
        (el (var (suc (suc zero)) · var zero · var zero))
  )))
