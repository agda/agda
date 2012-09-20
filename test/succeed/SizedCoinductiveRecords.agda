{-# OPTIONS --copatterns --sized-types --experimental-irrelevance #-}
{-# OPTIONS --show-implicit --show-irrelevant #-}
{-# OPTIONS -v tc.polarity:10 -v tc.pos:15 -v tc.size.solve:100 #-}
module SizedCoinductiveRecords where

open import Common.Size

postulate
  Size< : ..(_ : Size) → Set
{-# BUILTIN SIZELT Size< #-}

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

data Nat ..{i : Size} : Set where
  zero : Nat
  suc  : .{j : Size< i} → Nat {j} → Nat

mono : {i : Size}{j : Size< i} → Nat {j} → Nat {i}
mono n = n

id : .{i : Size} → Nat {i} → Nat {i}
id (zero) = zero
id (suc n) = suc (id n)

monus : .{i : Size} → Nat {i} → Nat → Nat {i}
monus x zero = x
monus zero y = zero
monus (suc x) (suc y) = monus x y

div : .{i : Size} → Nat {i} → Nat → Nat {i}
div zero    y = zero
div (suc x) y = suc (div (monus x y) y)

-- sized streams

module STREAM where

  record Stream (A : Set) ..{i : Size} : Set where
    coinductive
    constructor _∷_
    field
      head : A
      tail : .{j : Size< i} → Stream A {j}
  open Stream

  map : {A B : Set}(f : A → B).{i : Size} → Stream A {i} → Stream B {i}
  head (map f s) = f (head s)
  tail (map f s) = map f (tail s)

  -- stream antitone

  anti : {A : Set}{i : Size}{j : Size< i} → Stream A {i} → Stream A {j}
  anti s = s

  anti' : {A : Set}{i : Size}{j : Size< i} → (Stream A {j} → A) → (Stream A {i} → A)
  anti' f = f

-- Spanning tree

data List (A : Set) ..{i : Size} : Set where
  []  : List A
  _∷_ : .{j : Size< i}(x : A)(xs : List A {j}) → List A

map : {A B : Set}(f : A → B).{i : Size} → List A {i} → List B {i}
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

module Graph (I : Set)(adj : I → List I) where

  record Span ..{i : Size} : Set where
    coinductive
    constructor span
    field
      root  : I
      nodes : {j : Size< i} → List (Span {j})
  open Span

  {-# NO_TERMINATION_CHECK #-}
  tree : {i : Size} → I → Span {i}
  root  (tree root) = root
  nodes (tree root) = map (tree) (adj root)
  -- nodes (tree root) = λ {j} → map (tree {j}) (adj root)
