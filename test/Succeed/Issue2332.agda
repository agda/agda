
record R : Set₁
 where
  field
    _f_ : Set → Set

postulate A : Set

I₁ : R
I₁ R.f x = A
