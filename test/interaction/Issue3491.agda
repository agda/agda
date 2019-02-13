open import Agda.Builtin.Equality

record Box (B : Set) : Set₁ where
  constructor box
  field
    unbox   : B

-- here: .unbox is a valid forced pattern

=box : {B : Set} {Γ₀ Γ₁ : Box B} → Box.unbox Γ₀ ≡ Box.unbox Γ₁ → Γ₀ ≡ Γ₁
=box {Γ₀ = box unbox} {box r} p = ?

open Box public

-- here: .unbox is now the name of a projection and should therefore
-- not be generated

=box' : {B : Set} {Γ₀ Γ₁ : Box B} → unbox Γ₀ ≡ unbox Γ₁ → Γ₀ ≡ Γ₁
=box' {Γ₀ = box unbox} {box r} p = ?
