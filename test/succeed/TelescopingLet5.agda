module TelescopingLet5 where

postulate
  A : Set
  a : A

module B (a : A) where
   postulate
     C : Set
-- B.C : (a : A) → Set

module M (open B a) (c : C) where
  postulate cc : C
-- M.cc : (a : B.A a) → B.A a
