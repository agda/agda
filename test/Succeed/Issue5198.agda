
module _ (_ : Set) where

open import Imports.Issue5198 Set

data D : Set where
  r : D

F : D → Set₂
F r = R

f : {d : D} → F d → F d
f x = x

_ : R
_ = f record {A = Set}
