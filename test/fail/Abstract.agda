
module Abstract where

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true  = false
not false = true

abstract
  Answer : Set
  Answer = Bool

  yes : Answer
  yes = true

  no : Answer
  no = false

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

data Box : Set where
  [_] : Answer → Box

bad-box : Box
bad-box = [ true ]