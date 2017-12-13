-- Andreas, 2017-12-13, issue #2867
-- Parentheses needed when giving module argument

module _ where

module M (A : Set) where
  id : A → A
  id x = x

test : (F : Set → Set) (A : Set) (x : F A) → F A
test F A = λ x → x
  where open M {!F A!}  -- Give this

-- Expected: M (F A)
