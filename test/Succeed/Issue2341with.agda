-- Andreas, 2016-12-15, issue #2341
-- `with` needs to abstract also in sort of target type.

-- {-# OPTIONS -v tc.with:100 #-}

open import Agda.Primitive

test : ∀ a → Set (lsuc a)
test a with a
... | w = Set w
