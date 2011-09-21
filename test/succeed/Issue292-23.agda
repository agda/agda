-- Andreas, 2011-09-21, reported by Nisse
-- {-# OPTIONS -v tc.lhs.unify:25 #-}
module Issue292-23 where

data ⊤ : Set where
  tt : ⊤

data D : (A : Set) → A → Set₁ where
  d : (A : Set) (x : A) → D A x

data P : (x : ⊤) → D ⊤ x → Set₁ where
  p : (x : ⊤) → P x (d ⊤ x)

Foo : P tt (d ⊤ tt) → Set₁
Foo (p .tt) = Set
-- should work
-- bug was caused by a use of ureduce instead of reduce