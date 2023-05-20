-- Andreas, 2023-05-20, issue #6651
-- Do not solve ? : Set₁ to ? = Set if we have LevelUniv.

{-# OPTIONS --level-universe #-}

-- {-# OPTIONS -v tc.term:10 #-}
-- {-# OPTIONS -v tc.term.assign:15 #-}
-- {-# OPTIONS -v tc.conv.sort:35 #-}
-- {-# OPTIONS -v tc.conv:35 #-}
-- {-# OPTIONS -v tc:35 #-}

open import Agda.Primitive

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

L-U : Set₁
L-U = _ -- solves to LevelUniv

L : L-U
L = _ -- solves to Level
-- WAS Error: LevelUniv != Set

foo : L → L
foo ℓ = lsuc ℓ

mutual-block = END
