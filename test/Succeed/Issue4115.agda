-- Issue #4115 reported by Guillaume Brunerie

{-# OPTIONS --prop #-}

data Unit : Set where
  tt : Unit

postulate
  P : Prop

{-# TERMINATING #-}
p : P
p = p

works : Unit → P
works b = p

-- WAS: Agda loops during injectivity analysis of `loops`
loops : Unit → P
loops tt = p
