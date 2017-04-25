
module _ where

id : (A B : Set₁) → (A → B) → A → B
id _ _ f = f

postulate
  P    : (A : Set₁) → A → Set₁
  cong : (A B : Set₁) (f : A → B) (x : A) → P A x → P B (f x)
  A    : Set

record R₀ (B : Set) : Set₁ where
  constructor mkR₀
  no-eta-equality
  field
    proj₁ : Set
    proj₂ : B

record R₁ (_ : Set) : Set₁ where
  constructor mkR₁
  eta-equality
  field
    p : R₀ A

  X : Set
  X = R₀.proj₁ p

record R₂ (r : R₁ A) : Set₁ where
  constructor mkR₂
  eta-equality
  field
    g : R₀ (R₁.X r)

should-succeed :
  (r₁ : R₁ A) (r₂ : R₂ r₁) →
  P (R₂ r₁) r₂ → P (R₀ (R₁.X r₁)) (R₂.g r₂)
should-succeed r₁ r₂ =
  id (P _ _)
     (P (R₀ (R₁.X r₁)) (R₂.g r₂))
     (cong _ _ R₂.g _)
