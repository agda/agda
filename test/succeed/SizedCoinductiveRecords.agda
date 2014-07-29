{-# OPTIONS --copatterns --sized-types --experimental-irrelevance #-}
-- {-# OPTIONS --show-implicit --show-irrelevant #-}
-- {-# OPTIONS -v tc.polarity:10 -v tc.pos:15 -v tc.size.solve:100 #-}

module SizedCoinductiveRecords where

open import Common.Size

{- THIS WOULD BE A BETTER TYPING FOR sizeSuc, but it requires builtin Size<
sizeSuc : (i : Size) → Size< (↑ (↑ i))
sizeSuc i = ↑ i
-}

-- Subtyping for Size<

emb< : {i : Size} → Size< i → Size
emb< {i} j = j

-- Use Size< hypotheses

data Empty : {i : Size} → Set where
  empty : {i : Size} → Empty {i} → Empty {↑ i}

subEmpty : {i : Size}{j : Size< i} → Empty {j} → Empty {i}
subEmpty x = x

-- SHOULD FAIL:
-- fail : {i : Size}{j : Size< i} → Empty {i} → Empty {j}
-- fail x = x

-- Covariance for Size<

co : {i : Size}{j : Size< i} → Size< j → Size< i
co k = k

-- Contravariance for bounded quantification

Bounded : Size → Set
Bounded i = (j : Size< i) → Empty {j}

contra : {i : Size}{j : Size< i} → Bounded i → Bounded j
contra k = k

-- sized naturals

data Nat {i : Size} : Set where
  zero : Nat
  suc  : {j : Size< i} → Nat {j} → Nat

-- polarity of successor

data Bool : Set where
  true false : Bool

-- a natural number

one : Nat
one = suc {i = ∞} zero

mySuc : {i : Size} → Nat {i} → Nat {↑ i}
mySuc x = suc x

pred : {i : Size} → Nat {↑ i} → Nat {i}
pred zero = zero
pred (suc n) = n

shift : {i : Size} → (Nat → Nat {↑ i}) → Nat → Nat {i}
shift f n = pred (f (suc n))

{- Does not type check
loop : {i : Size} → Nat {i} → (Nat → Nat {i}) → Set
loop (suc n) f = loop n (shift f)
loop zero      = Nat
-}

data ⊥ : Set where
record ⊤ : Set where

mono : {i : Size}{j : Size< i} → Nat {j} → Nat {i}
mono n = n

id : {i : Size} → Nat {i} → Nat {i}
id (zero) = zero
id (suc n) = suc (id n)

monus : {i : Size} → Nat {i} → Nat → Nat {i}
monus x zero = x
monus zero y = zero
monus (suc x) (suc y) = monus x y

div : {i : Size} → Nat {i} → Nat → Nat {i}
div zero    y = zero
div (suc x) y = suc (div (monus x y) y)

postulate _∪_ : {i : Size} → Size< i → Size< i → Size< i

{-
max : {i : Size} → Nat {i} → Nat {i} → Nat {i}
max zero n = n
max m zero = m
max {i} (suc {j = j} m) (suc {j = k} n) = suc {j = j ∪ k} (max {j ∪ k} m n)
-}

-- omega inst

{- DOES NOT MAKE SENSE:
omegaBad' : (F : Size → Set) (i : Size) (j : Size< i)
            (f : (k : Size< (↑ j)) → F k) → F j
omegaBad' F i j f = f j
-}

-- fix

A : Size → Set
A i = Nat {i} → Nat

{-# NO_TERMINATION_CHECK #-}
fix : (f : (i : Size) → ((j : Size< i) → A j) → A i) → (i : Size) → A i
fix f i zero        = zero
fix f i (suc {j} n) = f i (λ j → fix f j) (suc n)

-- forever : {i : Size} → ({j : Size< i} → Nat {i} → Nat {j}) → Nat {i} → ⊥
-- forever {i} f n = forever f (f {{!!}} n)

-- sized streams

module STREAM where

  record Stream (A : Set) {i : Size} : Set where
    coinductive
    constructor _∷_
    field
      head : A
      tail : {j : Size< i} → Stream A {j}
  open Stream

  map : {A B : Set}(f : A → B){i : Size} → Stream A {i} → Stream B {i}
  head (map f s) = f (head s)
  tail (map f s) = map f (tail s)

  -- stream antitone

  anti : {A : Set}{i : Size}{j : Size< i} → Stream A {i} → Stream A {j}
  anti s = s

  anti' : {A : Set}{i : Size}{j : Size< i} → (Stream A {j} → A) → (Stream A {i} → A)
  anti' f = f

-- Spanning tree

data List (A : Set) {i : Size} : Set where
  []  : List A
  _∷_ : {j : Size< i}(x : A)(xs : List A {j}) → List A

map : {A B : Set}(f : A → B){i : Size} → List A {i} → List B {i}
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

module Graph (I : Set)(adj : I → List I) where

  record Span {i : Size} : Set where
    coinductive
    constructor span
    field
      root  : I
      nodes : {j : Size< i} → List (Span {j})
  open Span

  tree : {i : Size} → I → Span {i}
  root  (tree root) = root
  nodes (tree root) = map (tree) (adj root)
