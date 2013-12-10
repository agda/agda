module TelescopingLet5 where

postulate
  A : Set
  a : A

module B (a : A) where
   postulate
     C : Set
-- B.C : (a : A) → Set

module N = B a
module M' (open N) (c : C) where
  postulate cc : C
-- M.cc : (a : B.A a) → B.A a

E = let open B a in C

module M (open B a) (x : A) where
  D = C
  postulate cc : C
-- M.cc : (a : B.A a) → B.A a


