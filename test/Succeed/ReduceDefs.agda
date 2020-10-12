open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Equality

macro
  macro₁ : Term -> TC ⊤
  macro₁ goal = do
    u   ← quoteTC ((1 + 2) - 3)
    u'  ← onlyReduceDefs (quote _+_ ∷ []) (normalise u)
    qu' ← quoteTC u'
    unify qu' goal

test₁ : macro₁ ≡ def (quote _-_)
                   (arg (arg-info visible relevant) (lit (nat 3)) ∷
                    arg (arg-info visible relevant) (lit (nat 3)) ∷ [])
test₁ = refl


macro
  macro₂ : Term -> TC ⊤
  macro₂ goal = do
    u   ← quoteTC ((1 - 2) + 3)
    u'  ← dontReduceDefs (quote _+_ ∷ []) (normalise u)
    qu' ← quoteTC u'
    unify qu' goal

test₂ : macro₂ ≡ def (quote _+_)
                   (arg (arg-info visible relevant) (lit (nat 0)) ∷
                    arg (arg-info visible relevant) (lit (nat 3)) ∷ [])
test₂ = refl
