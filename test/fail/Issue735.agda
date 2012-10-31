-- Andreas, 2012-10-30 Sections
-- Reported by guillaume.brunerie, Oct 24 2012
module Issue735 where

import Common.Level
open import Common.Prelude using (Nat; zero; suc)

module _ {a} (A : Set a) where

  data List : Set a where
    []  : List
    _∷_ : (x : A) (xs : List) → List

module _ {a} {A : Set a} where

    _++_ : List → List → List
    []       ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- should not work, we cannot cut a section in two
-- correct is: List A

test : List Nat
test = (5 ∷ []) ++ (3 ∷ [])
