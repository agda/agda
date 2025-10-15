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

-- Re. #8038: if the copy of _*_ from the anonymous module in the where
-- clause (not used) is trimmed, we might see
--
--   Bool !=< (F Foo.* x) ≡ (λ x₁ → x₁)
--
-- in the error message (see Issue721trim). In interactive development a
-- user wouldn't see that, but it still doesn't mention the anonymous
-- module.
_ = ?
