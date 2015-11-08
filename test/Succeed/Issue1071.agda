-- Andreas, 2014-03-03, report and test case by Nisse.

-- {-# OPTIONS -v tc.lhs.unify:60 #-}

module Issue1071 where

postulate
  F : Set → Set

module M (_ : Set₁) where
  postulate A : Set

open M Set

data P : Set → Set₁ where
  c : (R : Set) → P (F R)

data Q : (R : Set) → R → P R → Set₁ where
  d : (R : Set) (f : F R) → Q (F R) f (c R)

Foo : (f' : F A) → Q (F A) f' (c A) → Set₁
Foo ._ (d ._ _) = Set

-- WAS:
-- Refuse to solve heterogeneous constraint f₁ : F A =?= f : F A
-- when checking that the pattern d ._ _ has type Q (F A) f (c A)

-- SHOULD: succeed
