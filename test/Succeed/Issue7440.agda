
postulate
  X Y Γ Δ : Set
  x : X
  γ : Γ
  δ : Δ

module R (x : X) where
  postulate s : Y

module A (γ : Γ) (let module M₁ = R x) (δ : Δ) (let module M₂ = R x) where
  -- When modules are created or opened in a module telescope we need to
  -- add an anonymous wrapper module (see #1299). If created modules are
  -- opened public it's important that the wrapper module they live in have
  -- the right parameters. Here M₁ should live in a wrapper module with a Γ
  -- parameter and M₂ in one with Γ and Δ.
  open M₁ public renaming (s to s₁)
  open M₂ public renaming (s to s₂)

-- The correct parameters are important so that when we apply A, we pass γ to
-- M₁ and γ δ to M₂.
module B = A γ δ

check₁ : Y
check₁ = B.s₁

check₂ : Y
check₂ = B.s₂
