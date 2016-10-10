-- {-# OPTIONS -v tc.constr.add:45 #-}

module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

==_] : ∀ {a} {A : Set a} (x : A) → x ≡ x
== x ] = refl

[ : ∀ {a} {A : Set a} (x : A) {y : A} → x ≡ y → A
[ x refl = x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

infixr 5 _∷_
data Vec {a} (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷[_]_
pattern _∷[_]_ x n xs = _∷_ {n} x xs

module _ {a} {A : Set a} where

  id : A → A
  id x = x

  len : ∀ {n} → Vec A n → Nat
  len {n} _ = n

  module _ {b} {B : Set b} where

    map : ∀ {n} → (A → B) → Vec A n → Vec B n
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    const : A → B → A
    const x _ = x

    _!>_ : A → B → B
    _ !> x = x

module SomeParameters {a} (n : Nat) (A : Set a) (xs : Vec A n) (ys : Vec A (n * 2)) where

  simpleRefine : Vec A n → Nat
  simpleRefine []            = [ n == 0 ]
  simpleRefine (x ∷[ m ] xs) = [ n == suc m ]

  moreComplex : Vec A n → Nat
  moreComplex [] = 0
  moreComplex (z ∷ zs) with map id xs
  moreComplex (z ∷ zs) | x ∷ [] = [ n == 1 ] + [ 2 == len ys ]
  moreComplex (z ∷ zs) | x ∷ x₁ ∷[ k ] xs′ with [ n == 2 + k ] !> map id zs
  moreComplex (z ∷ zs) | x ∷ x₁ ∷ xs′ | z₁ ∷ [] = [ n == 2 ]
  moreComplex (z ∷ zs) | x ∷ x₁ ∷ xs′ | z₁ ∷ z₂ ∷[ k ] zs′ =
    let n+_ = λ m → [ n == 3 + k ] + m
        n+k = n+ k
    in case [ n+k == 3 + k + k ] of λ i →
       let n+i = [ n == 3 + k ] + i in
       case map id zs′ of λ where
         []              → [ (n+ i) == 3 + i ] + [ n+k == 3 ] + [ n+i == 3 + i ]
         (z₃ ∷[ j ] zs″) →
           let _ = [ n      == 4 + j ]
               _ = [ k      == 1 + j ]
               _ = [ n+k    == 4 + j + (1 + j) ]
               _ = [ (n+ i) == 4 + j + i ]
           in
           [ (len xs′) == 2 + j ] +
           [ (len ys) == (4 + j) * 2 ]
