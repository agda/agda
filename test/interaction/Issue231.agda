module Issue231 where

postulate
  A : Set

data List : Set where
  _∷_ : A → List → List

data Any : List → Set where
  there : ∀ {x xs} → Any xs → Any (x ∷ xs)

postulate
  id : (A : Set) → A → A

lemma : (xs : List) → Set → (p : Any xs) → Set
lemma (x ∷ xs) A (there p) with id (Any xs) p
lemma (x ∷ xs) A (there p) | p′ = {!p′!}

-- Before case-split:
-- lemma (x ∷ xs) A (there p) | p′ = {!p′!}
-- After case-split:
-- lemma (A ∷ _) _ (there p) | there y = ?
