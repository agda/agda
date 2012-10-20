-- 2012-10-20 Andreas
module Issue721b where

data Bool : Set where
  false true : Bool

record Foo (b : Bool) : Set where
  field
    _*_ : Bool → Bool → Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

test : (F : Foo false) → let open Foo F in (x : Bool) → _*_ x ≡ (λ x → x)
test F x = x
  where open Foo F
-- Don't want to see any anonymous module
