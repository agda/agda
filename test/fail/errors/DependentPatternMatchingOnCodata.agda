module DependentPatternMatchingOnCodata where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

codata D : Set where
  d : D → D

e : D
e = d e

force : D → D
force (d x) = d x

force-eq : (x : D) → x ≡ force x
force-eq (d x) = refl

p : e ≡ d e
p = force-eq e
