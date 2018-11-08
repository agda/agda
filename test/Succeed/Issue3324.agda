-- Andreas, 2018-10-27, issue #3324 reported by Guillaume Brunerie
-- Missing 'reduce' leads to arbitrary rejection of pattern matching on props

{-# OPTIONS --prop #-}

-- {-# OPTIONS -v tc.cover:60 #-}

data Unit : Prop where
  tt : Unit

-- Works
f : {A : Set} → Unit → Unit
f tt = tt

-- Should work
g : Unit → Unit
g tt = tt
