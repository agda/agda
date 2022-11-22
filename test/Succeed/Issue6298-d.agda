{-# OPTIONS --erased-cubical --safe -vtc.lhs.top:30 #-}

data I : Set where

data D : I → Set where
  c : (x : I) → D x

@0 f : (@0 x : I) → D x → D x
f .x (c x) = c x
