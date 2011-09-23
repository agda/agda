
module Pat (BaseType : Set) where

data Ty : Set where
  ι   : BaseType -> Ty
  _⟶_ : Ty -> Ty -> Ty

data Bwd (A : Set) : Set where
  •   : Bwd A
  _◄_ : Bwd A -> A -> Bwd A

infixl 30 _◄_

Ctx = Bwd Ty

data Take {A : Set} : Bwd A -> A -> Bwd A -> Set where
  hd : forall {x xs} -> Take (xs ◄ x) x xs
  tl : forall {x y xs ys} -> Take xs x ys -> Take (xs ◄ y) x (ys ◄ y)

data Pat : Ctx -> Ctx -> Ty -> Ctx -> Set

data Pats : Ctx -> Ty -> Ctx -> Ty -> Set where
  ε : forall {Θ τ} -> Pats Θ τ Θ τ
  _,_ : forall {Θ₁ Θ₂ Θ₃ ρ σ τ} ->
        Pat • Θ₁ ρ Θ₂ -> Pats Θ₂ σ Θ₃ τ ->
        Pats Θ₁ (ρ ⟶ σ) Θ₃ τ

data Pat where
  ƛ    : forall {Δ Θ Θ' σ τ} -> Pat (Δ ◄ σ) Θ τ Θ' ->
         Pat Δ Θ (σ ⟶ τ) Θ'
  _[_] : forall {Θ Θ' Δ σ τ} ->
         Take Θ σ Θ' -> Pats Δ σ • τ -> Pat Δ Θ τ Θ'

