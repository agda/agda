-- Andreas, 2011-10-02
{-# OPTIONS --show-implicit #-}
module Issue483a where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

data Empty : Set where

postulate A : Set

abort : .Empty → A
abort ()

test : let X : .Set1 → A
           X = _
       in  (x : Empty) → X Set ≡ abort x
test x = refl

-- this should fail with message like
--
--  Cannot instantiate the metavariable _16 to abort x since it
--  contains the variable x which is not in scope of the metavariable
--  when checking that the expression refl has type _16 _ ≡ abort x
--
-- a solution like X = λ _ → abort x : Set1 → A
-- would be invalid even though x is irrelevant, because there is no
-- term of type Set1 → A
