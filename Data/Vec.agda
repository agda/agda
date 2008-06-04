------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------

module Data.Vec where

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

  lem₂ : forall n -> 1 + n ≡ n + 1
  lem₂ n = prove (n ∷ []) (con 1 :+ N) (N :+ con 1) ≡-refl
    where N = var fz

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

infixr 5 _++_

_++_ : forall {a m n} -> Vec a m -> Vec a n -> Vec a (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixl 5 _∷ʳ_

-- Snoc.

_∷ʳ_ : forall {a n} -> Vec a n -> a -> Vec a (n + 1)
xs ∷ʳ x = xs ++ singleton x

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
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

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

infixl 5 _∷ʳ'_

data InitLast {a : Set} (n : ℕ) : Vec a (n + 1) -> Set where
  _∷ʳ'_ : (xs : Vec a n) -> (x : a) -> InitLast n (xs ∷ʳ x)

initLast : forall {a} n (xs : Vec a (n + 1)) -> InitLast n xs
initLast zero    (x ∷ [])         = [] ∷ʳ' x
initLast (suc n) (x ∷ xs)         with initLast n xs
initLast (suc n) (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y

-- Note that the following two implementations are complicated (since
-- the index of the input is (1 + n) instead of (n + 1)):

private
 module Unused where

  init : forall {a n} -> Vec a (suc n) -> Vec a n
  init {n = n} xs with cast (lem₂ n) xs | initLast n (cast (lem₂ n) xs)
  init xs | .(ys ∷ʳ y) | ys ∷ʳ' y = ys

  last : forall {a n} -> Vec a (suc n) -> a
  last {n = n} xs with cast (lem₂ n) xs | initLast n (cast (lem₂ n) xs)
  last xs | .(ys ∷ʳ y) | ys ∷ʳ' y = y

-- So the following recursive definitions are used instead:

init : forall {a n} -> Vec a (suc n) -> Vec a n
init (x ∷ [])     = []
init (x ∷ y ∷ ys) = x ∷ init (y ∷ ys)

last : forall {a n} -> Vec a (suc n) -> a
last (x ∷ [])     = x
last (x ∷ y ∷ ys) = last (y ∷ ys)
