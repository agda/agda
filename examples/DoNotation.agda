-- Using do-notation to implement a type checker for simply-typed
-- lambda-calculus.
module _ where

open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.String

-- Preliminaries --

--- Decidable equality ---

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

record Eq (A : Set) : Set where
  field _==_ : (x y : A) → Dec (x ≡ y)

open Eq {{...}}

--- Functors, Applicatives, and Monads ---

record Functor (F : Set → Set) : Set₁ where
  field fmap : ∀ {A B} → (A → B) → F A → F B

open Functor {{...}}

record Applicative (F : Set → Set) : Set₁ where
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    overlap {{super}} : Functor F

open Applicative {{...}}

record Monad (M : Set → Set) : Set₁ where
  field
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    overlap {{super}} : Applicative M
  _>>_ : ∀ {A B} → M A → M B → M B
  m >> m' = m >>= λ _ → m'

open Monad {{...}}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

instance
  FunctorMaybe : Functor Maybe
  fmap {{FunctorMaybe}} f nothing  = nothing
  fmap {{FunctorMaybe}} f (just x) = just (f x)

  ApplicativeMaybe : Applicative Maybe
  pure  {{ApplicativeMaybe}} = just
  _<*>_ {{ApplicativeMaybe}} nothing  _        = nothing
  _<*>_ {{ApplicativeMaybe}} (just _) nothing  = nothing
  _<*>_ {{ApplicativeMaybe}} (just f) (just x) = just (f x)

  MonadMaybe : Monad Maybe
  _>>=_ {{MonadMaybe}} nothing  f = nothing
  _>>=_ {{MonadMaybe}} (just x) f = f x

--- List membership ---

infix 2 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs} → x ∈ x ∷ xs
  suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

rawIndex : ∀ {A} {x : A} {xs} → x ∈ xs → Nat
rawIndex zero    = zero
rawIndex (suc i) = suc (rawIndex i)

-- Simply typed λ-calculus --

infixr 7 _=>_
data Type : Set where
  nat : Type
  _=>_ : Type → Type → Type

--- Decidable equality for Type ---
private
  =>-inj₁ : ∀ {σ₁ σ₂ τ₁ τ₂} → (σ₁ => τ₁) ≡ (σ₂ => τ₂) → σ₁ ≡ σ₂
  =>-inj₁ refl = refl

  =>-inj₂ : ∀ {σ₁ σ₂ τ₁ τ₂} → σ₁ => τ₁ ≡ σ₂ => τ₂ → τ₁ ≡ τ₂
  =>-inj₂ refl = refl

instance
  EqType : Eq Type
  _==_ {{EqType}} nat nat = yes refl
  _==_ {{EqType}} nat (τ => τ₁) = no λ()
  _==_ {{EqType}} (σ => σ₁) nat = no λ()
  _==_ {{EqType}} (σ => σ₁) (τ => τ₁) with σ == τ | σ₁ == τ₁
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no neq   = no λ eq → neq (=>-inj₂ eq)
  ... | no neq   | _        = no λ eq → neq (=>-inj₁ eq)

--- Raw terms ---
data Expr : Set where
  var : Nat → Expr
  app : Expr → Expr → Expr
  lam : Type → Expr → Expr
  lit : Nat → Expr
  suc : Expr

--- Well-typed terms ---
Context = List Type

data Term (Γ : Context) : Type → Set where
  var : ∀ {τ} (x : τ ∈ Γ) → Term Γ τ
  app : ∀ {σ τ} (s : Term Γ (σ => τ)) (t : Term Γ σ) → Term Γ τ
  lam : ∀ σ {τ} (t : Term (σ ∷ Γ) τ) → Term Γ (σ => τ)
  lit : (n : Nat) → Term Γ nat
  suc : Term Γ (nat => nat)

--- Erasing types ---
forgetTypes : ∀ {Γ τ} → Term Γ τ → Expr
forgetTypes (var x)   = var (rawIndex x)
forgetTypes (app s t) = app (forgetTypes s) (forgetTypes t)
forgetTypes (lam σ t) = lam σ (forgetTypes t)
forgetTypes (lit n)   = lit n
forgetTypes suc       = suc

--- Type checking ---

TC = Maybe

typeError : ∀ {A} → TC A
typeError = nothing

data WellTyped (Γ : Context) (e : Expr) : Set where
  ok : (σ : Type) (t : Term Γ σ) → forgetTypes t ≡ e → WellTyped Γ e

data InScope (Γ : Context) (n : Nat) : Set where
  ok : (σ : Type) (i : σ ∈ Γ) → rawIndex i ≡ n → InScope Γ n

infix 2 _∋_
pattern _∋_ σ x = ok σ x refl

lookupVar : ∀ Γ n → TC (InScope Γ n)
lookupVar []      n       = typeError
lookupVar (σ ∷ Γ) zero    = pure (σ ∋ zero)
lookupVar (σ ∷ Γ) (suc n) = do
  τ ∋ i ← lookupVar Γ n
  pure (τ ∋ suc i)

-- Correct-by-construction type inference
infer : ∀ Γ e → TC (WellTyped Γ e)

infer Γ (var x) = do
  τ ∋ i ← lookupVar Γ x
  pure (τ ∋ var i)

infer Γ (app e e₁) = do
  σ => τ ∋ s ← infer Γ e where nat ∋ s → typeError
  σ′     ∋ t ← infer Γ e₁
  yes refl ← pure (σ == σ′) where no _ → typeError
  pure (τ ∋ app s t)

infer Γ (lam σ e) = do
  τ ∋ t ← infer (σ ∷ Γ) e
  pure (σ => τ ∋ lam σ t)

infer Γ (lit x) = pure (nat ∋ lit x)
infer Γ suc     = pure (nat => nat ∋ suc)

-- Check that it works
test : infer [] (lam (nat => nat) (lam nat (app (var 1) (var 0)))) ≡
       pure ((nat => nat) => nat => nat ∋
             lam (nat => nat) (lam nat (app (var (suc zero)) (var zero))))
test = refl
