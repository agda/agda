
-- Example by Sandro Stucki on the Agda mailing list.

-- If higher-dimensional unification fails and --without-K is not
-- enabled, we should still apply injectivity.

open import Agda.Builtin.Nat

postulate Fin : Nat → Set

data Indexed : Nat → Nat → Set where
  con : ∀ m {n} (i : Fin n) → Indexed (m + n) (m + suc n)

data RelIndexed : ∀ {m n} → Indexed m n → Indexed m n → Set where
  relIdx : ∀ {m n} (i : Fin n) (j : Fin n) → RelIndexed (con m i) (con m j)

test1 : ∀ {m n} {a b : Indexed m n} → RelIndexed a b → Indexed m n
test1 (relIdx {m} i _) = con m i

test2 : ∀ {m n} {a : Indexed m n} → RelIndexed a a → Indexed m n
test2 (relIdx {m} i _) = con m i
