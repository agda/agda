-- Andreas, 2019-02-25, issue #3588
-- C-c C-r (refine) produces unqualified constructor, but only
-- a qualified constructor is accepted in this place.

-- {-# OPTIONS -v interaction.intro:100 #-}
-- {-# OPTIONS -v scope.inverse:100 #-}
-- {-# OPTIONS -v toConcrete:50 #-}

module Issue3588 where

module M (_ : Set₁) where

  data D : Set where
    c : D

  data P : D → Set where
    c : P c

open M Set using (D; P)
open M.D

test : P c
test = {!!}  -- C-c C-r

  -- "c" suggested by refine, but rejected by reload or give
  -- correct: P.c
