
open import Auto.Prelude

mutual
 data Even : ℕ → Set where
  even-0 : Even zero
  even-s : {n : ℕ} → Odd n → Even (succ n)

 data Odd : ℕ → Set where
  odd-1 : Odd (succ zero)
  odd-s : {n : ℕ} → Even n → Odd (succ n)

double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

h0 : ∀ {n} → Even (double n)
h0 {n} = {!-c!}
--h0 {zero} = even-0
--h0 {succ x} = even-s (odd-s h0)


-- ----------------------------

module VecMap where

 map : {X Y : Set} → {n : ℕ} → (X → Y) → Vec X n → Vec Y n
 map f xs = {!-c!}  -- h1
{-
 map f [] = []
 map f (x ∷ x₁) = f x ∷ map f x₁
-}

-- ----------------------------

data Type : Set₁ where
 <_> : Set → Type
 _⇒_ : Type → Type → Type

∥_∥ : Type → Set
∥ < X > ∥ = X
∥ a ⇒ b ∥ = ∥ a ∥ → ∥ b ∥

data Ctx : Set₁ where
 [] : Ctx
 _,_ : Ctx → Type → Ctx

data _∈_ (a : Type) : Ctx → Set₁ where
 zero : ∀ {Γ} → a ∈ (Γ , a)
 succ : ∀ {b Γ} → a ∈ Γ → a ∈ (Γ , b)

data Exp (Γ : Ctx) : Type → Set₁ where
 app : ∀ {α β} → Exp Γ (α ⇒ β) → Exp Γ α → Exp Γ β
 var : ∀ {α} → α ∈ Γ → Exp Γ α
 lam : ∀ {a b} → Exp (Γ , a) b → Exp Γ (a ⇒ b)

data Env : Ctx → Set₁ where
 nil : Env []
 cons : ∀ {Γ a} → ∥ a ∥ → Env Γ → Env (Γ , a)

lookup : ∀ {Γ a} → a ∈ Γ → Env Γ → ∥ a ∥
lookup x σ = {!-c!}  -- h2
{-
lookup {._} {< x >} zero (cons x₁ x₂) = x₁
lookup {._} {< x >} (succ x₁) (cons x₂ x₃) = lookup x₁ x₃
lookup {._} {x ⇒ x₁} zero (cons x₂ x₃) = x₂
lookup {._} {x ⇒ x₁} (succ x₂) (cons x₃ x₄) = lookup x₂ x₄
-}

lookup' : ∀ {Γ a} → a ∈ Γ → Env Γ → ∥ a ∥
lookup' zero (cons x σ) = x
lookup' (succ v) (cons x σ) = lookup' v σ

eval : ∀ {Γ a} → Env Γ → Exp Γ a → ∥ a ∥
--eval σ e = {!-c lookup!}  -- no solution found
eval σ (app e e₁) = {!!}  -- h3
eval σ (var x) = {!lookup'!}  -- h4, -c also works, repeats the solution for lookup
eval σ (lam e) x = {!!}  -- h5
{-
eval σ (app e e₁) = eval σ e (eval σ e₁)
eval σ (var x) = lookup x σ
eval σ (lam e) x = eval (cons x σ) e
-}
