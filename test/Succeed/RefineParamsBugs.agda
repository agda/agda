-- Various small test cases that failed at some point or another
-- during the development of the parameter refinement feature.

module _ where

open import Agda.Primitive
open import Agda.Builtin.Nat hiding (_<_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List

[_≡_] : ∀ {a} {A : Set a} (x y : A) → x ≡ y → A
[ x ≡ y ] refl = x

pattern ! = refl

module CoPatterns where
  record R : Set where
    field b : Nat
  open R

  sharp : Nat → R
  sharp n = f n
    where
      f : Nat → R
      b (f m) = m

  r₁ : (n : Nat) → R
  b (r₁ n) = n

  module _ (n : Nat) where
    r : R
    b r = n

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  data T : Nat → Set where
    zero : T zero
    suc  : ∀ {n} → T n → T (suc n)

  module _ (A : Set) where
    ex : Σ Nat T
    fst ex = suc zero
    snd ex = suc zero

module SimpleWith where
  module P (A : Set) where

    f : Nat → Nat
    f zero = 0
    f (suc n) with n
    f (suc n) | z = z

module MergeSort where
  data Vec (A : Set) : Nat → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  module Sort (A : Set) where

    merge : ∀ {n} → Vec A n → Vec A zero
    merge [] = []
    merge (x ∷ xs) = merge xs

module LetPatternBinding where
  record Wrap : Set where
    constructor wrap
    field wrapped : Nat

  fails : Wrap → Nat
  fails w = let wrap n = w in n

  record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    constructor _,_
    field fst : A
          snd : B

  module _ (A B : Set) where

    const : A → B → A
    const x _ = x

    plus : A × B → A
    plus p = let a , b = p in const a b

module RefineStuff where
  module _ (x y : Nat) where

    foo : x ≡ suc y → Nat
    foo refl = y

  bar : (x y : Nat) → x ≡ y → Nat
  bar x y refl = y

  test : foo 2 1 refl ≡ 1
  test = refl


module Projections where
  module _ (X : Set) where

    record ∃ (a : Set) : Set where
      field
        witness : a

    f : ∃ X → X
    f r = ∃.witness r

module Delay where
  data Vec (A : Set) : Nat → Set where
     _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  data Unit : Set where
    unit : Unit

  record DNat : Set₁ where
    field
      D     : Set
      force : D → Nat
  open DNat

  nonNil : ∀ {n} → Vec Unit n → Nat
  nonNil (i ∷ is) = suc (force f i)
    where
      f : DNat
      D     f      = Unit
      force f unit = zero

module Folds where

  foldr : {A B : Set} → (A → B → B) → B → List A → B
  foldr f z []       = z
  foldr f z (x ∷ xs) = f x (foldr f z xs)

  foldl : {A B : Set} → (B → A → B) → B → List A → B
  foldl f z []       = z
  foldl f z (x ∷ xs) = foldl f (f z x) xs

  module FoldAssoc
    {A : Set}(_∙_ : A → A → A)
    (assoc : ∀ x y z → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))) where

    smashr = foldr _∙_
    smashl = foldl _∙_

    postulate
      foldl-plus : ∀ z₁ z₂ xs → smashl (z₁ ∙ z₂) xs ≡ (z₁ ∙ smashl z₂ xs)

    foldr=foldl : ∀ ∅ → (∀ x → (∅ ∙ x) ≡ (x ∙ ∅)) →
                  List _ → Set
    foldr=foldl ∅ id []       = Nat
    foldr=foldl ∅ id (x ∷ xs) rewrite id x
                                     | foldl-plus x ∅ xs
                              = Nat

module With where
  data Vec (A : Set) : Nat → Set where
    []  : Vec A 0
    _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

  idV : ∀ {A n} → Vec A n → Vec A n
  idV [] = []
  idV (x ∷ xs) = x ∷ idV xs

  len : ∀ {A n} → Vec A n → Nat
  len {n = n} _ = n

  module _ (n : Nat) (xs : Vec Nat n) where

    f : Vec Nat n → Nat
    f [] = 0
    f (x ∷ ys) with idV ys
    f (x ∷ ys) | []     = [ n ≡ 1 ] !
    f (x ∷ ys) | z ∷ zs = [ n ≡ suc (suc (len zs)) ] !

module NestedWith where

  data Vec (A : Set) : Nat → Set where
    []  : Vec A 0
    cons : ∀ n → A → Vec A n → Vec A (suc n)

  module _ (X Y : Set) where

    f : ∀ n → Vec Nat n → Nat
    f _ [] = 0
    f .(suc m) (cons m x xs) with x
    f n (cons m x xs) | 0 = [ n ≡ suc m ] !
    f n (cons m x xs) | y with xs
    f n (cons m x xs) | y | []          = [ n ≡ 1 ] !
    f n (cons m x xs) | z | cons k y ys = [ n ≡ suc (suc k) ] !

module LetCase where
  record _×_ (A B : Set) : Set where
    constructor _,_
    field fst : A
          snd : B

  case_of_ : {A B : Set} → A → (A → B) → B
  case x of f = f x

  g : Nat × Nat → Nat
  g p = let a , b = p in
        case b of λ where
          zero    → a
          (suc b) → a


  f : Nat × (Nat × Nat) → Nat
  f p =
    let a , q = p
        b , c = q
    in  a + b + c

  module _ {a} {A : Set a} where
    h : List A → Nat → Nat → Nat
    h [] = λ _ _ → 0
    h (x ∷ xs) =
      let ys = xs in
      λ n → λ where m → h ys n m
