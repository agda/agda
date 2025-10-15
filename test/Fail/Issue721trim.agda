module Issue721trim where

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
-- See 721b, #8038: copy trimming applies here and the error message
-- should mention F Foo.*, not an anonymous module
