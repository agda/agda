------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

infixr 5 _++_

open import Data.Nat
open import Data.Nat.Properties
open ℕ-semiringSolver
open import Data.Fin
import Data.List as List
open List using ([_])
open import Data.Product
open import Logic
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The vector type along with some operations

open import Data.Vec.Core public

------------------------------------------------------------------------
-- Boring lemmas

private
 abstract

  lem₁ : forall n k -> n * k + k ≡ k + n * k
  lem₁ n k = prove (n ∷ k ∷ [])
                   (N :* K :+ K)
                   (K :+ N :* K)
                   ≡-refl
    where N = var fz; K = var (fs fz)

  lem₂ : forall m n -> m + n * m ≡ n * m + m
  lem₂ m n = prove (m ∷ n ∷ [])
                   (M :+ N :* M)
                   (N :* M :+ M)
                   ≡-refl
    where M = var fz; N = var (fs fz)

------------------------------------------------------------------------
-- Some operations

head : forall {a n} -> Vec a (1 + n) -> a
head (x ∷ xs) = x

tail : forall {a n} -> Vec a (1 + n) -> Vec a n
tail (x ∷ xs) = xs

singleton : forall {a} -> a -> Vec a 1
singleton x = x ∷ []

_++_ : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : forall {a b n} -> (a -> b) -> Vec a n -> Vec b n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

zipWith :  forall {a b c n}
        -> (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWith _⊕_ []       []       = []
zipWith _⊕_ (x ∷ xs) (y ∷ ys) = (x ⊕ y) ∷ zipWith _⊕_ xs ys

zip : forall {a b n} -> Vec a n -> Vec b n -> Vec (a × b) n
zip = zipWith _,_

replicate : forall {a n} -> a -> Vec a n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

foldr :  forall {a b : Set} {m}
      -> (a -> b -> b) -> b -> Vec a m -> b
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

concat : forall {a m n} -> Vec (Vec a m) n -> Vec a (n * m)
concat                 []                   = []
concat {a = a} {m = m} (_∷_ {n = n} xs xss) =
  ≡-subst (Vec a) (lem₂ m n) (xs ++ concat xss)

take : forall {a n} (i : Fin (suc n)) -> Vec a n -> Vec a (toℕ i)
take fz      xs       = []
take (fs ()) []
take (fs i)  (x ∷ xs) = x ∷ take i xs

drop : forall {a n} (i : Fin (suc n)) -> Vec a n -> Vec a (n ∸ toℕ i)
drop fz      xs       = xs
drop (fs ()) []
drop (fs i)  (x ∷ xs) = drop i xs

splitAt : forall {a} m {n} -> Vec a (m + n) -> Vec a m × Vec a n
splitAt zero    xs       = ([] , xs)
splitAt (suc m) (x ∷ xs) with splitAt m xs
... | (ys , zs) = (x ∷ ys , zs)

group : forall {a n} -> (k : ℕ) -> Vec a (n * k) -> Vec (Vec a k) n
group         {n = zero}  k [] = []
group {a = a} {n = suc n} k xs
  with splitAt k (≡-subst (Vec a) (lem₁ n k) xs)
... | (ys , zs) = ys ∷ group {n = n} k zs

sum : forall {n} -> Vec ℕ n -> ℕ
sum = foldr _+_ 0

toList : forall {a n} -> Vec a n -> [ a ]
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : forall {a} -> (xs : [ a ]) -> Vec a (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs
