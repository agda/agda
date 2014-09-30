-- {-# OPTIONS -v tc.lhs.shadow:30 #-}

{-# OPTIONS --copatterns #-}

module PatternShadowsConstructor4 where

module A where

  data B : Set where
    x : B

  data C : Set where
    c : B → C

open A using (C; c)

record R : Set where
  field
    fst : C → C
    snd : A.B
open R

r : R
fst r (c x) = x
snd r       = A.B.x
