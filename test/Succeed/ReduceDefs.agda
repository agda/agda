open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Equality

pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

macro
  macro₁ : Term -> TC ⊤
  macro₁ goal = do
    u   ← quoteTC ((1 + 2) - 3)
    u'  ← withReduceDefs (true , (quote _+_ ∷ [])) (normalise u)
    qu' ← quoteTC u'
    unify qu' goal

test₁ :
  macro₁ ≡
  def (quote _-_) (vArg (lit (nat 3)) ∷ vArg (lit (nat 3)) ∷ [])
test₁ = refl


macro
  macro₂ : Term -> TC ⊤
  macro₂ goal = do
    u   ← quoteTC ((1 - 2) + 3)
    u'  ← withReduceDefs (false , (quote _+_ ∷ [])) (normalise u)
    qu' ← quoteTC u'
    unify qu' goal

test₂ :
  macro₂ ≡
  def (quote _+_) (vArg (lit (nat 0)) ∷ vArg (lit (nat 3)) ∷ [])
test₂ = refl
