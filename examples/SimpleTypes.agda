{-

  A simple bidirectional type checker for simply typed lambda calculus which is
  sound by construction.

-}
module SimpleTypes where

infix 10 _==_

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data List (A : Set) : Set where
  ε   : List A
  _,_ : List A -> A -> List A

length : forall {A} -> List A -> Nat
length ε        = zero
length (xs , x) = suc (length xs)

infixl 25 _,_

-- Raw terms

data Expr : Set where
  varʳ : Nat -> Expr
  _•ʳ_ : Expr -> Expr -> Expr
  ƛʳ_  : Expr -> Expr

infixl 90 _•ʳ_
infix  50 ƛʳ_

-- Types

data Type : Set where
  ι : Type
  _⟶_ : Type -> Type -> Type

infixr 40 _⟶_

-- Typed terms

Ctx = List Type

data Var : Ctx -> Type -> Set where
  vz : forall {Γ τ} -> Var (Γ , τ) τ
  vs : forall {Γ τ σ} -> Var Γ τ -> Var (Γ , σ) τ

data Term : Ctx -> Type -> Set where
  var : forall {Γ τ} -> Var Γ τ -> Term Γ τ
  _•_ : forall {Γ τ σ} -> Term Γ (τ ⟶ σ) -> Term Γ τ -> Term Γ σ
  ƛ_  : forall {Γ τ σ} -> Term (Γ , σ) τ -> Term Γ (σ ⟶ τ)

infixl 90 _•_
infix  50 ƛ_

-- Type erasure

⌊_⌋ˣ : forall {Γ τ} -> Var Γ τ -> Nat
⌊ vz   ⌋ˣ = zero
⌊ vs x ⌋ˣ = suc ⌊ x ⌋ˣ

⌊_⌋ : forall {Γ τ} -> Term Γ τ -> Expr
⌊ var v ⌋ = varʳ ⌊ v ⌋ˣ
⌊ s • t ⌋ = ⌊ s ⌋ •ʳ ⌊ t ⌋
⌊ ƛ t   ⌋ = ƛʳ ⌊ t ⌋

-- Type equality

infix 30 _≟_

_≟_ : (σ τ : Type) -> Maybe (σ == τ)
ι       ≟ ι       = just refl
σ₁ ⟶ τ₁ ≟ σ₂ ⟶ τ₂ with σ₁ ≟ σ₂ | τ₁ ≟ τ₂
σ  ⟶ τ  ≟ .σ ⟶ .τ | just refl | just refl = just refl
_  ⟶ _  ≟ _  ⟶ _  | _         | _         = nothing
_       ≟ _       = nothing

-- The type checked view

  -- ok  : forall {Γ τ e} -> Check ⌊ e ⌋ -- unsolved metas with no range!

data Check (Γ : Ctx)(τ : Type) : Expr -> Set where
  ok  : (t : Term Γ τ) -> Check Γ τ ⌊ t ⌋
  bad : {e : Expr} -> Check Γ τ e

data Infer (Γ : Ctx) : Expr -> Set where
  yes : (τ : Type)(t : Term Γ τ) -> Infer Γ ⌊ t ⌋
  no  : {e : Expr} -> Infer Γ e

data Lookup (Γ : Ctx) : Nat -> Set where
  found      : (τ : Type)(x : Var Γ τ) -> Lookup Γ ⌊ x ⌋ˣ
  outofscope : {n : Nat} -> Lookup Γ n

lookup : (Γ : Ctx)(n : Nat) -> Lookup Γ n
lookup ε n = outofscope
lookup (Γ , τ) zero = found τ vz
lookup (Γ , σ) (suc n) with lookup Γ n
lookup (Γ , σ) (suc .(⌊ x ⌋ˣ)) | found τ x  = found τ (vs x)
lookup (Γ , σ) (suc n)         | outofscope = outofscope

infix 20 _⊢_∋_ _⊢_∈

_⊢_∈ : (Γ : Ctx)(e : Expr) -> Infer Γ e

_⊢_∋_ : (Γ : Ctx)(τ : Type)(e : Expr) -> Check Γ τ e
Γ ⊢ ι       ∋ ƛʳ e = bad
Γ ⊢ (σ ⟶ τ) ∋ ƛʳ e with Γ , σ ⊢ τ ∋ e
Γ ⊢ (σ ⟶ τ) ∋ ƛʳ .(⌊ t ⌋) | ok t = ok (ƛ t)
Γ ⊢ (σ ⟶ τ) ∋ ƛʳ _        | bad  = bad
Γ ⊢ τ ∋ e with Γ ⊢ e ∈
Γ ⊢ τ ∋ .(⌊ t ⌋) | yes σ t with τ ≟ σ
Γ ⊢ τ ∋ .(⌊ t ⌋) | yes .τ t | just refl = ok t
Γ ⊢ τ ∋ .(⌊ t ⌋) | yes σ t  | nothing   = bad
Γ ⊢ τ ∋ e | no = bad


Γ ⊢ varʳ i         ∈ with lookup Γ i
Γ ⊢ varʳ .(⌊ x ⌋ˣ) ∈ | found τ x  = yes τ (var x)
Γ ⊢ varʳ _         ∈ | outofscope = no
Γ ⊢ e₁        •ʳ e₂ ∈        with Γ ⊢ e₁ ∈
Γ ⊢ e₁        •ʳ e₂ ∈        | no       = no
Γ ⊢ .(⌊ t₁ ⌋) •ʳ e₂ ∈        | yes ι t₁ = no
Γ ⊢ .(⌊ t₁ ⌋) •ʳ e₂ ∈        | yes (σ ⟶ τ) t₁ with Γ ⊢ σ ∋ e₂
Γ ⊢ .(⌊ t₁ ⌋) •ʳ .(⌊ t₂ ⌋) ∈ | yes (σ ⟶ τ) t₁ | ok t₂ = yes τ (t₁ • t₂)
Γ ⊢ .(⌊ t₁ ⌋) •ʳ _         ∈ | yes (σ ⟶ τ) t₁ | bad   = no
Γ ⊢ ƛʳ e     ∈ = no

-- Proving completeness (for normal terms)

-- Needs magic with

{-
mutual
  data Nf : forall {Γ τ} -> Term Γ τ -> Set where
    ƛ-nf  : forall {Γ σ τ} -> {t : Term (Γ , σ) τ} -> Nf t -> Nf (ƛ t)
    ne-nf : forall {Γ τ} -> {t : Term Γ τ} -> Ne t -> Nf t

  data Ne : forall {Γ τ} -> Term Γ τ -> Set where
    •-ne : forall {Γ σ τ} ->
           {t₁ : Term Γ (σ ⟶ τ)} -> Ne t₁ ->
           {t₂ : Term Γ σ} -> Nf t₂ -> Ne (t₁ • t₂)
    var-ne : forall {Γ τ} -> {x : Var Γ τ} -> Ne (var x)

mutual
  complete-check : forall {Γ τ} -> (t : Term Γ τ) -> Nf t ->
                   Γ ⊢ τ ∋ ⌊ t ⌋ == ok t
  complete-check ._ (ƛ-nf t) = {! !}
  complete-check _ (ne-nf n) with complete-infer _ n
  complete-check t (ne-nf n) | p = {! !}

  complete-infer : forall {Γ τ} -> (t : Term Γ τ) -> Ne t ->
                   Γ ⊢ ⌊ t ⌋ ∈ == yes τ t
  complete-infer t ne = {! !}
-}

-- Testing

test1 = ε ⊢ ι ⟶ ι ∋ ƛʳ varʳ zero
test2 = ε , ι , ι ⟶ ι ⊢ varʳ zero •ʳ varʳ (suc zero) ∈
