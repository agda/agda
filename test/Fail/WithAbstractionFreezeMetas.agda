open import Agda.Builtin.Equality

data ⊤ : Set where
  tt : ⊤

postulate u : ⊤

-- Solving metas during the type-based abstraction check causes ?0 to
-- be solved as u, which is not unique (and incidentally results in an
-- ill-typed `with` function because we do not instantiate the type containing
-- this meta before abstracting over u).
-- Instead ?0 should remain unsolved.
h : _≡_ {A = u ≡ u} refl refl
h with u | refl {x = {!!}}
h | tt | e = refl
