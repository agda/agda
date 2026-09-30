{-# OPTIONS --show-irrelevant #-}

postulate
  A : Set
  f : .A → A

data _≡_ (x : A) : A → Set where
  refl : x ≡ x

mutual
  X : .A → A
  X = _

  Y : A → A
  Y = {!λ x → x!}

  Z : A → A
  Z = {!λ x → x!}

  test : ∀ x → X (Y x) ≡ f (Z x)
  test x = refl
