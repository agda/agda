-- Andreas, 2019-03-18, AIM XXIX, issue #3631 reported by rrose1
-- Performance regression in 2.5.4 due to new sort handling

{-# OPTIONS --no-universe-polymorphism #-}  -- needed for the performance problem

-- {-# OPTIONS -v 10 -v tc.cc:15 -v tc.cc.type:60 -v tc.cover:100 #-}
-- {-# OPTIONS -v tc.cc.type:80 #-}

module _ where

  module M
    (X : Set)
    (x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  : X)
    (x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : X)
    (x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : X)
    where
    f : X
    f = x0

-- Should check quickly.
