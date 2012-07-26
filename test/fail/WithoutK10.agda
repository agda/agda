{-# OPTIONS --without-K --show-implicit #-}

module WithoutK10 where

data Unit : Set where
  unit : Unit

data D {A : Set} (f : Unit → A) : A → Set where
  d : ∀ {x} → D f x

Foo : ∀ {A} {x : A} → D (let f = λ { unit → x } in f) x → Set₁
Foo d = Set
