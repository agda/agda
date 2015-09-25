-- 2011-10-04 Andreas
{-# OPTIONS --experimental-irrelevance --show-irrelevant #-}
module TerminationOnIrrelevant where

data ⊥ : Set where

data Empty : Set where
  c : Empty → Empty

d : Empty → Empty
d (c x) = x

f : .Empty → ⊥
f (c x) = f x

g : .Empty → ⊥
g (c x) = g x

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

-- the following would loop if we evaluated f x to f (d x)
mayloop : .(x y : Empty) → f x ≡ g y
mayloop x y = refl
