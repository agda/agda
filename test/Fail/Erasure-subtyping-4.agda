{-# OPTIONS --erasure #-}

f : {A B : Set} → (A → B) → @0 A → B
f g x = g x
