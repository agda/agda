------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

open import Data.Nat
open import Data.Fin
import Data.List as List
open List using ([_])
open import Data.Product

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data Vec (a : Set) : ℕ -> Set where
  []  : Vec a zero
  _∷_ : forall {n} -> a -> Vec a n -> Vec a (suc n)

infix 4 _∈_ _[_]=_

data _∈_ {a : Set} : a -> {n : ℕ} -> Vec a n -> Set where
  here  : forall {n} {x}   {xs : Vec a n} -> x ∈ x ∷ xs
  there : forall {n} {x y} {xs : Vec a n} -> x ∈ xs -> x ∈ y ∷ xs

data _[_]=_ {a : Set} : {n : ℕ} -> Vec a n -> Fin n -> a -> Set where
  here  : forall {n}     {x}   {xs : Vec a n} -> x ∷ xs [ zero ]= x
  there : forall {n} {i} {x y} {xs : Vec a n} ->
          xs [ i ]= x -> y ∷ xs [ suc i ]= x

------------------------------------------------------------------------
-- Some operations

lookup : forall {a n} -> Fin n -> Vec a n -> a
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs

head : forall {a n} -> Vec a (1 + n) -> a
head (x ∷ xs) = x

tail : forall {a n} -> Vec a (1 + n) -> Vec a n
tail (x ∷ xs) = xs

singleton : forall {a} -> a -> Vec a 1
singleton x = x ∷ []

infixr 5 _++_

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

foldr :  forall {a} (b : ℕ -> Set) {m}
      -> (forall {n} -> a -> b n -> b (suc n))
      -> b zero
      -> Vec a m -> b m
foldr b _⊕_ n []       = n
foldr b _⊕_ n (x ∷ xs) = x ⊕ foldr b _⊕_ n xs

foldr₁ :  forall {a : Set} {m}
       -> (a -> a -> a) -> Vec a (suc m) -> a
foldr₁ _⊕_ (x ∷ [])     = x
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

foldl :  forall {a : Set} (b : ℕ -> Set) {m}
      -> (forall {n} -> b n -> a -> b (suc n))
      -> b zero
      -> Vec a m -> b m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (\n -> b (suc n)) _⊕_ (n ⊕ x) xs

foldl₁ :  forall {a : Set} {m}
       -> (a -> a -> a) -> Vec a (suc m) -> a
foldl₁ _⊕_ (x ∷ xs) = foldl _ _⊕_ x xs

concat : forall {a m n} -> Vec (Vec a m) n -> Vec a (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

take : forall {a n} (i : Fin (suc n)) -> Vec a n -> Vec a (toℕ i)
take zero     xs       = []
take (suc ()) []
take (suc i)  (x ∷ xs) = x ∷ take i xs

drop : forall {a n} (i : Fin (suc n)) -> Vec a n -> Vec a (n - i)
drop zero     xs       = xs
drop (suc ()) []
drop (suc i)  (x ∷ xs) = drop i xs

infixr 5 _++'_

data SplitAt {a : Set} (m : ℕ) {n : ℕ} : Vec a (m + n) -> Set where
  _++'_ : (xs : Vec a m) (ys : Vec a n) -> SplitAt m (xs ++ ys)

splitAt : forall {a} m {n} (xs : Vec a (m + n)) -> SplitAt m xs
splitAt zero    xs                = [] ++' xs
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | ys ++' zs = (x ∷ ys) ++' zs

data Group {a : Set} (n k : ℕ) : Vec a (n * k) -> Set where
  concat' : (xss : Vec (Vec a k) n) -> Group n k (concat xss)

group : forall {a} n k (xs : Vec a (n * k)) -> Group n k xs
group zero    k []                  = concat' []
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | ys ++' zs with group n k zs
group (suc n) k .(ys ++ concat zss) | ys ++' ._ | concat' zss = concat' (ys ∷ zss)

reverse : forall {a n} -> Vec a n -> Vec a n
reverse {a} = foldl (Vec a) (\rev x -> x ∷ rev) []

sum : forall {n} -> Vec ℕ n -> ℕ
sum = foldr _ _+_ 0

toList : forall {a n} -> Vec a n -> [ a ]
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : forall {a} -> (xs : [ a ]) -> Vec a (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : forall {a n} -> Vec a n -> a -> Vec a (1 + n)
[]       ∷ʳ y = singleton y
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

infixl 5 _∷ʳ'_

data InitLast {a : Set} (n : ℕ) : Vec a (1 + n) -> Set where
  _∷ʳ'_ : (xs : Vec a n) -> (x : a) -> InitLast n (xs ∷ʳ x)

initLast : forall {a n} (xs : Vec a (1 + n)) -> InitLast n xs
initLast {n = zero}  (x ∷ [])         = [] ∷ʳ' x
initLast {n = suc n} (x ∷ xs)         with initLast xs
initLast {n = suc n} (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y

init : forall {a n} -> Vec a (1 + n) -> Vec a n
init xs with initLast xs
init .(ys ∷ʳ y) | ys ∷ʳ' y = ys

last : forall {a n} -> Vec a (1 + n) -> a
last xs with initLast xs
last .(ys ∷ʳ y) | ys ∷ʳ' y = y
