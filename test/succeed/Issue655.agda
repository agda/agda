-- Andreas, 2012-07-31, issue reported by Nicolas Pouillard
-- {-# OPTIONS -v tc:100 -v term:100 #-}
-- {-# OPTIONS -v tc.def.alias:20 #-}
-- {-# OPTIONS -v tc:0 -v term:0  #-}
module Issue655 where

-- import Common.Level -- this should not be necessary

module TypeAliases where

  postulate A : Set

  B = A → A

module Ex0 where
 postulate
  f : ∀ {A : Set} → A → A

 yellow = f

 boring : ∀ {A : Set} → A → A
 boring = f

 boring' = λ {A} → f {A}

module Ex1 where
 postulate
  A : Set
  f : ∀ {x : A} → A

 yellow = f

 boring : ∀ {x : A} → A
 boring {x} = f {x}

 boring' = λ {x} → f {x}

module Ex2 where
 postulate
  A : Set
  f : ∀ {B : Set} (x : B) {y : A} → A
  a : A

 yellow = f a

 boring : ∀ {y : A} → A
 boring {y} = f a {y}

 boring' = λ {y} → f a {y}

-- no longer yellow...
