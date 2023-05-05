{-# OPTIONS --erasure #-}

f : {A B : Set} → (@0 A → B) → A → B
f g = g
