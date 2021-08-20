{-# OPTIONS --guardedness --cubical #-}

module Issue2799 where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

record Stream (A : Set) : Set where
  coinductive
  constructor _,_
  field
    head : A
    tail : Stream A

open Stream

mapS : ∀ {A B} → (A → B) → Stream A → Stream B
head (mapS f xs) = f (head xs)
tail (mapS f xs) = mapS f (tail xs)


mapS-id : ∀ {A} {xs : Stream A} → mapS (λ x → x) xs ≡ xs
head (mapS-id {xs = xs} i) = head xs
tail (mapS-id {xs = xs} i) = mapS-id {xs = tail xs} i
