
open import Common.Level
open import Common.Prelude
open import Common.Reflection
open import Common.Equality

postulate
  a b : Level

data Check : Set where
  check : (x y : Term) → x ≡ y → Check

pattern _==_ x y = check x y refl

pattern `a = def (quote (a)) []  -- Andreas, 2024-09-27 extra parens ok
pattern `b = def (quote b) []
pattern `suc x = def (quote lsuc) (vArg x ∷ [])
pattern _`⊔_ x y = def (quote _⊔_) (vArg x ∷ vArg y ∷ [])

t₀ = quoteTerm Set₃ == sort (lit 3)
t₁ = quoteTerm (Set a) == sort (set `a)
t₂ = quoteTerm (Set (lsuc b)) == sort (set (`suc `b))
t₃ = quoteTerm (Set (a ⊔ b)) == sort (set (`a `⊔ `b))
