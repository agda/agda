-- 2012-10-20 Andreas
module Issue721a where

data Bool : Set where
  false true : Bool

record Foo (b : Bool) : Set where
  field
    _*_ : Bool → Bool → Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

test : (F : Foo false) (x : Bool) → let open Foo F in _*_ x ≡ (λ x → x)
test F x = x
-- Don't want to see .Issue632._.* in the error message
