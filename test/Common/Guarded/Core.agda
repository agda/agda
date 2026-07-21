{-# OPTIONS --guarded --cubical=compatible #-}
module Common.Guarded.Core where

open import Agda.Primitive
open import Agda.Primitive.Guarded

private
  variable
    l : Level
    A B : Set l

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

data gStream (A : Set) : Set where
  cons : (x : A) (xs : ▹ gStream A) → gStream A

map-gStream : ∀ {A B : Set} → (A → B) → gStream A → gStream B
map-gStream f = löb \ map-gStream' → \ { (cons a as) → cons (f a) \ α → map-gStream' α (as α) }
