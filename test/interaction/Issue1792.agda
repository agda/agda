-- Andreas, 2016-02-04
-- Printing of overapplied operator patterns

-- Expected results see comments.

-- {-# OPTIONS -v reify.clause:60 #-}

_fun : (A : Set) → Set
_fun = {!!}
-- C-c C-c RET gives
--
-- A fun = ?


_nofun : (A : Set₁) (B : Set₁) → Set₁
_nofun = {!!}
-- C-c C-c RET gives
--
-- (A nofun) B = ?

module Works where

  record Safe : Set₁ where
    field <_>safe : Set
  open Safe

  mixfix : Safe
  mixfix = {!!}
  -- C-c C-c RET gives
  --
  --   < mixfix >safe

record Safe : Set₁ where
  field <_>safe : Set → Set
open Safe

mixfix : Safe
< mixfix >safe = {!!}
-- C-c C-c RET gives
--
--   < mixfix >safe x

_+_ : (A B C : Set) → Set
_+_ = {!!}
-- C-c C-c RET gives
--
--   (A + B) C = ?

-_ : (A B : Set) →  Set
-_ = {!!}
-- C-c C-c RET gives
--
--   (- A) B = ?

data D : Set where
  _*_ : (x y z : D) → D

splitP : D → D
splitP d = {! d!}
-- C-c C-c [d RET] gives
--
--   splitP ((d * d₁) d₂) = ?
