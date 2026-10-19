open import Agda.Builtin.Equality

data ⊤ : Set where
  tt : ⊤

postulate u : ⊤

f : Set
f with u in e
f | tt = ⊤

-- The `refl` in `f | u | refl` should get generalised over, but neither
-- of the other `refl`s should. Generalising too much or too little results
-- in an ill-typed `with` function.

f' : _≡_ {A = u ≡ u} refl refl → f ≡ ⊤
f' _ with u in e
f' _ | tt = refl
