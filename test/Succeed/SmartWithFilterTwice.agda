{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool renaming (true to tt; false to ff)
open import Agda.Builtin.List renaming (_∷_ to _,-_)

variable
  A B : Set _
  f : A → B
  xs ys : List _
  x y : A

ap : (f : A → B) → x ≡ y → f x ≡ f y
ap f refl = refl

filter : (A → Bool) → List A → List A
filter {A = A} f []        = []
filter {A = A} f (x ,- xs) with f x
... | tt = x ,- filter f xs
... | ff = filter f xs

filter-twice : filter f (filter f xs) ≡ filter f xs
filter-twice {xs = []} = refl
filter-twice {f = f} {xs = x ,- xs} with f x
... | ff = filter-twice {xs = xs}
... | tt = ap (x ,-_) (filter-twice {xs = xs})
