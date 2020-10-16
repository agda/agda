{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.List

postulate
  A : Set
  nilA : A
  consA : A → List A → A
  w/e : {x y : A} → x ≡ y

data D : List A → Set where
  nil  : D []
  cons : (x : A) (xs : List A) → D (x ∷ xs)

foo : ∀ {xs} (d : D xs)
      (let f : D xs → A
           f = λ where nil         → nilA
                       (cons y ys) → consA y ys) →
      f d ≡ nilA
foo nil        = {!!}
foo (cons _ _) = w/e
