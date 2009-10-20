------------------------------------------------------------------------
-- Vectors parameterised on types in Set₁
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.Vec1 where

infixr 5 _∷_

open import Data.Nat
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin; zero; suc)

------------------------------------------------------------------------
-- The type

data Vec₁ (a : Set₁) : ℕ → Set₁ where
  []  : Vec₁ a zero
  _∷_ : ∀ {n} (x : a) (xs : Vec₁ a n) → Vec₁ a (suc n)

------------------------------------------------------------------------
-- Some operations

head : ∀ {a n} → Vec₁ a (1 + n) → a
head (x ∷ xs) = x

tail : ∀ {a n} → Vec₁ a (1 + n) → Vec₁ a n
tail (x ∷ xs) = xs

[_] : ∀ {a} → a → Vec₁ a 1
[ x ] = x ∷ []

infixr 5 _++_

_++_ : ∀ {a m n} → Vec₁ a m → Vec₁ a n → Vec₁ a (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b n} → (a → b) → Vec₁ a n → Vec₁ b n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

map₀₁ : ∀ {a b n} → (a → b) → Vec a n → Vec₁ b n
map₀₁ f []       = []
map₀₁ f (x ∷ xs) = f x ∷ map₀₁ f xs

map₁₀ : ∀ {a b n} → (a → b) → Vec₁ a n → Vec b n
map₁₀ f []       = []
map₁₀ f (x ∷ xs) = f x ∷ map₁₀ f xs

concat : ∀ {a m n} → Vec₁ (Vec₁ a m) n → Vec₁ a (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

infixr 5 _++'_

data SplitAt {a : Set1} (m : ℕ) {n : ℕ} : Vec₁ a (m + n) → Set1 where
  _++'_ : (xs : Vec₁ a m) (ys : Vec₁ a n) → SplitAt m (xs ++ ys)

splitAt : ∀ {a} m {n} (xs : Vec₁ a (m + n)) → SplitAt m xs
splitAt zero    xs                = [] ++' xs
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | ys ++' zs = (x ∷ ys) ++' zs

take : ∀ {a} m {n} → Vec₁ a (m + n) → Vec₁ a m
take m xs with splitAt m xs
take m .(xs ++ ys) | xs ++' ys = xs

drop : ∀ {a} m {n} → Vec₁ a (m + n) → Vec₁ a n
drop m xs with splitAt m xs
drop m .(xs ++ ys) | xs ++' ys = ys

lookup : ∀ {a n} → Fin n → Vec₁ a n → a
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs