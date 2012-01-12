-- {-# OPTIONS -v tc.rec.proj:50 #-}
module IrrelevantProjections where

import Common.Irrelevance  

record [_] (A : Set) : Set where
  field
    .inflate : A

open [_] using (inflate)

.proj : ∀ {A} → [ A ] → A
proj x = inflate x
