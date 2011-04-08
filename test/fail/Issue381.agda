-- {-# OPTIONS -v scope.let:10 #-}

module Issue381 (A : Set) where

data _≡_ (x : A) : A → Set where
  refl : x ≡ x
 
id : A → A
id x = let abstract y = x in y
-- abstract in let should be disallowed

lemma : ∀ x → id x ≡ x
lemma x = refl