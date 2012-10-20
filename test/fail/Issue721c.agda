-- 2012-10-20 Andreas
module Issue721c where

data Bool : Set where
  false true : Bool

record Foo (b : Bool) : Set where
  field
    _*_ : Bool → Bool → Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record ∃ {A : Set} (B : A → Set) : Set where
  constructor pack
  field fst : A
        snd : B fst

dontExpandTooMuch : (F : Foo false) → ∃ λ t → t ≡ t
dontExpandTooMuch F = pack t t
  where open Foo F
        d = λ x → x * x
        t = d (d (d (d true)))
-- t should not be expanded in the error message
