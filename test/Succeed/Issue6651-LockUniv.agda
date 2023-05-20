-- Andreas, 2023-05-20, issue #6651
-- Do not solve ? : Set₁ to ? = Set if we have LockUniv.

{-# OPTIONS --guarded #-}

-- {-# OPTIONS -v tc.term:10 #-}
-- {-# OPTIONS -v tc.conv.sort:35 #-}
-- {-# OPTIONS -v tc.conv:35 #-}
-- {-# OPTIONS -v tc:45 #-}

open import Agda.Primitive

primitive
  primLockUniv : Set₁

postulate
  Tick : primLockUniv

BEGIN = Set₁
END   = Set

mutual-block : BEGIN

L-U : Set₁
L-U = _ -- solves to primLockUniv

T : L-U
T = _ -- solves to Tick

foo : T → Tick
foo t = t

mutual-block = END
