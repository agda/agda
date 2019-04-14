-- Andreas, Ulf, AIM XXIX, 2019-03-18, issue #3597

-- Eta-expansion of record metas disregards freezing.
-- Meta occurs check is then insufficient, leading to cyclic assignment.

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v tc.meta:40 #-}
-- {-# OPTIONS -v tc.meta.assign:100 #-}
-- {-# OPTIONS -v tc.meta.eta:100 #-}

postulate P : (A : Set) → (a : A) → Set

record R : Set₁ where
  constructor c
  -- no-eta-equality -- WORKS without eta
  field
    A : Set
    a : A
    p : P A a → P A a

C : R
C = {!!}

module M = R C

test : P {!!} M.a → P {!!} M.a
test x = M.p x

-- WAS: cyclic assignment
--   C  = _5
--  _7 := _5 .A
--  _9 := _5 .A
--  _5 := c _10 _11 _12
-- _10 := C .A

-- NOW: frozed metas are eta-expanded to records of frozen metas
