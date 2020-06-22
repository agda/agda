-- Andreas, 2016-06-01, issue 1997 reported by Andres

{-# OPTIONS --rewriting --confluence-check #-}

infix  4 _≡_
infixl 6 _+_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

plus0 : (x : ℕ) → x + zero ≡ x
plus0 zero    = refl
plus0 (suc x) = cong suc (plus0 x)

{-# REWRITE plus0 #-}
{-# REWRITE plus0 #-}

-- Should complain about duplicate rewrite rule
