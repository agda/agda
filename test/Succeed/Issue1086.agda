-- Andreas, 2018-06-15, issue #1086
-- Reported by Andrea
-- Fixed by Jesper in https://github.com/agda/agda/commit/242684bca62fabe43e125aefae7526be4b26a135

open import Common.Bool
open import Common.Equality

and : (a b : Bool) → Bool
and true  b = b
and false b = false

test : ∀ a b → and a b ≡ true → a ≡ true
test true true refl = refl

-- Should succeed.
