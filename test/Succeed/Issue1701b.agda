-- Andreas, 2015-11-10, issue reported by Wolfram Kahl
-- {-# OPTIONS -v scope.mod.inst:30 #-}
-- {-# OPTIONS -v tc.mod.check:10 -v tc.mod.apply:80 -v impossible:10 #-}

postulate
  A : Set
  a : A

module Id (A : Set) (a : A) where
  x = a

module ModParamsToLoose (A : Set) where
  private module M (a : A) where module I = Id A a
  open M public

open ModParamsToLoose A
open I a

y : A
y = x
