-- Andreas, 2019-08-08, issue #3972 (and #3967)

-- In the presence of an unreachable clause, the serializer crashed on a unsolve meta.

-- It seems this issue was fixed along #3966: only the ranges of unreachable clauses
-- are now serialized.

open import Agda.Builtin.Equality public

postulate
  List : Set → Set

data Coo {A} (xs : List A) : Set where
  coo : Coo xs → Coo xs

test : {A : Set} (xs : List A) (z : Coo xs) → Set₁
test xs z = cs xs z refl
  where
  cs : (xs : List _)  -- filling this meta _=A removes the internal error
       (z : Coo xs)
       (eq : xs ≡ xs)
       → Set₁
  cs xs (coo z) refl = Set
  cs xs (coo z) eq = Set  -- unreachable
