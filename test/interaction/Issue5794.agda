-- Andreas, 2022-09-30, issue #5794, test by Trebor-Huang.
-- Auto crashed due to unbound de Bruijn index.

-- This file is just one mutual block.

data Context : Set
data Type    : Context -> Set
data Var     : ∀ Γ -> Type Γ -> Set

data Context where
    _◂_ : ∀ Γ -> Type Γ -> Context

data Type where
    ⋆   : ∀{Γ} → Type Γ
    var : ∀{Γ} → Var Γ ⋆ -> Type Γ

postulate
    Ren : Context -> Context -> Set
    𝔭   : ∀{Γ α} → Ren (Γ ◂ α) Γ

rent : ∀{Γ Δ} → Ren Δ Γ -> Type Γ -> Type Δ

data Var where
    𝔮 : ∀{Γ α} → Var (Γ ◂ α) (rent 𝔭 α)

fetch : ∀{Γ Δ α} → (ρ : Ren Γ Δ) -> Var Δ α -> Var Γ (rent ρ α)
fetch ρ 𝔮 = {!   !}  -- C-c C-a used to crash here with unbound de Bruijn index

rent ρ ⋆ = ⋆
rent ρ (var i) = {!   !} -- var (fetch ρ i)

-- Current outcome (OK):
-- No solution found
