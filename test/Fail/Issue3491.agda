
data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

record Box (B : Set) : Set₁ where
  constructor box
  field
    unbox   : B
open Box public

=box :{B : Set}{Γ₀ Γ₁ : Box B} → _≡_ {A = B} (unbox Γ₀) (unbox Γ₁) → Γ₀ ≡ Γ₁
=box {b} {box unbox} {box .unbox} refl = ?

-- WAS: internal error at src/full/Agda/TypeChecking/Rules/LHS.hs:294
-- SHOULD: complain about misplaced projection pattern
