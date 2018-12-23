{-# OPTIONS --guardedness --cubical #-}

module Issue2799 where

open import Agda.Primitive.Cubical

postulate
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

{-# BUILTIN PATHP        PathP     #-}

_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ _ → A)

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
