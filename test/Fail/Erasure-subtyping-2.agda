{-# OPTIONS --erasure #-}

f : {A B : Set} → (@0 A → B) → A → B
f g = λ (@0 x) → g x
