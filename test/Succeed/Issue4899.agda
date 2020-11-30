{-# OPTIONS --cubical #-}

open import Agda.Builtin.Equality

data Unit : Set where
  unit : Unit

f : (x : Unit) → _ -- x ≡ x
g : (x : Unit) → x ≡ x

f unit = refl
g x = f x
