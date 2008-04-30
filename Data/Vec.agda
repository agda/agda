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
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The vector type along with some operations

open import Data.Vec.Core public

------------------------------------------------------------------------
-- Boring lemmas

private

  lem₃ : forall m -> m + 0 ≡ m
  lem₃ m = prove (m ∷ []) (M :+ con 0) M ≡-refl
    where M = var fz

  lem₄ : forall m n -> m + (1 + n) ≡ (1 + m) + n
  lem₄ m n = prove (m ∷ n ∷ [])
                   (M :+ (con 1 :+ N))
                   ((con 1 :+ M) :+ N)
                   ≡-refl
    where M = var fz; N = var (fs fz)

  cast : forall {a n₁ n₂} -> n₁ ≡ n₂ -> Vec a n₁ -> Vec a n₂
  cast {a = a} = ≡-subst (Vec a)

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
foldr _⊕_ n []       = n
foldr _⊕_ n (x ∷ xs) = x ⊕ foldr _⊕_ n xs

foldr₁ :  forall {a : Set} {m}
       -> (a -> a -> a) -> Vec a (suc m) -> a
foldr₁ _⊕_ (x ∷ [])         = x
foldr₁ _⊕_ (x ∷ xs@(_ ∷ _)) = x ⊕ foldr₁ _⊕_ xs

foldl :  forall {a b : Set} {m}
      -> (b -> a -> b) -> b -> Vec a m -> b
foldl _⊕_ n []       = n
foldl _⊕_ n (x ∷ xs) = foldl _⊕_ (n ⊕ x) xs

foldl₁ :  forall {a : Set} {m}
       -> (a -> a -> a) -> Vec a (suc m) -> a
foldl₁ _⊕_ (x ∷ xs) = foldl _⊕_ x xs

concat : forall {a m n} -> Vec (Vec a m) n -> Vec a (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

take : forall {a n} (i : Fin (suc n)) -> Vec a n -> Vec a (toℕ i)
take fz      xs       = []
take (fs ()) []
take (fs i)  (x ∷ xs) = x ∷ take i xs

drop : forall {a n} (i : Fin (suc n)) -> Vec a n -> Vec a (n - i)
drop fz      xs       = xs
drop (fs ()) []
drop (fs i)  (x ∷ xs) = drop i xs

splitAt : forall {a} m {n} -> Vec a (m + n) -> Vec a m × Vec a n
splitAt zero    xs       = ([] , xs)
splitAt (suc m) (x ∷ xs) with splitAt m xs
... | (ys , zs) = (x ∷ ys , zs)

group : forall {a n} -> (k : ℕ) -> Vec a (n * k) -> Vec (Vec a k) n
group {n = zero}  k [] = []
group {n = suc n} k xs with splitAt k xs
... | (ys , zs) = ys ∷ group k zs

revApp : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
revApp         []                 ys = ys
revApp {n = n} (_∷_ {n = m} x xs) ys =
  cast (lem₄ m n) (revApp xs (x ∷ ys))

reverse : forall {a n} -> Vec a n -> Vec a n
reverse {n = n} xs = cast (lem₃ n) (revApp xs [])

sum : forall {n} -> Vec ℕ n -> ℕ
sum = foldr _+_ 0

toList : forall {a n} -> Vec a n -> [ a ]
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : forall {a} -> (xs : [ a ]) -> Vec a (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

init : forall {a n} -> Vec a (suc n) -> Vec a n
init (x ∷ [])         = []
init (x ∷ xs@(_ ∷ _)) = x ∷ init xs

last : forall {a n} -> Vec a (suc n) -> a
last (x ∷ [])         = x
last (x ∷ xs@(_ ∷ _)) = last xs
