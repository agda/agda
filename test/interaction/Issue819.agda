-- Andreas, 2017-01-18, issue #819, reported by stevana
-- Underscores should be preserved when case-splitting

data List (A : Set) : Set where
  _∷_ : (x : A)(xs : List A) → List A

data ⊥ : Set where

-- Case-splitting on x:
test : List ⊥ → ⊥
test (x ∷ _) = {!x!} -- split on x

-- I think the underscore should be kept.

expected : List ⊥ → ⊥
expected (() ∷ _)

-- Likewise here:

test′ : List ⊥ → List ⊥ → List ⊥ → ⊥
test′ (x ∷ _) ys _ = {!ys x!} -- split on ys and x

expected′ : List ⊥ → List ⊥ → List ⊥ → ⊥
expected′ (() ∷ _) (x ∷ ys) _
