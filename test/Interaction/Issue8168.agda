data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Ty : Set where
  bool : Ty
  _⇒_  : (a b : Ty) → Ty

data Context : Set where
  ε : Context
  _·_ : (Γ : Context) (a : Ty) → Context

module _ where
  private
    variable
      a b : Ty
      Γ Δ : Context

  data Term : (Γ : Context) (a : Ty) → Set where
    var :                                       Term (Γ · a) a
    wk  : (e : Term Γ a)                      → Term (Γ · b) a
    app : (f : Term Γ (a ⇒ b)) (e : Term Γ a) → Term Γ b
    abs : (e : Term (Γ · a) b)                → Term Γ (a ⇒ b)

module One where

  δ : ∀ {a} → ℕ → Term ε {!  !}  -- C-c C-a
  δ zero = abs (abs (app (wk var) (app (wk var) var)))
  δ (suc n) = app (δ n) (δ zero)

  -- error: [ParseError]
  -- in the name _a_61, the part 61 is not valid because it is a literal

  -- N.B.: Solution is (a ⇒ a) ⇒ (a ⇒ a)

module Two where

  δ : ∀ {a} → ℕ → Term ε {!  !}  -- C-c C-a
  δ zero = abs (abs (app (wk var) (app (wk var) var)))
  δ (suc n) = app (δ n) (δ zero)
