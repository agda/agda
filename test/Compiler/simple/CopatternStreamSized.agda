{-# OPTIONS --copatterns #-}

open import Common.Size
open import Common.Prelude
open import Common.Product renaming (proj₁ to fst; proj₂ to snd)

record Stream (i : Size) (A : Set) : Set where
  coinductive
  field force : ∀{j : Size< i} → A × Stream j A
open Stream

head : ∀{i A} → Stream (↑ i) A →  A
head s = fst (force s)

tail : ∀{i A} → Stream (↑ i) A → Stream i A
tail s = snd (force s)

smap : ∀{i A B} (f : A → B) → Stream i A → Stream i B
force (smap f s) with force s
... | a , as = f a , smap f as

scanl : ∀{i A B} (f : B → A → B) (b : B) (s : Stream i A) → Stream i B
force (scanl f b s) with force s
... | a , as = b , scanl f (f b a) as

_!_ : ∀{A} (s : Stream _ A) (n : Nat) → A
s ! zero  = head s
s ! suc n = tail s ! n

_!!_ : ∀{A} (s : Stream _ A) (n : Nat) → A
s !! n with force s
_ !! zero  | a , as = a
_ !! suc n | a , as = as !! n

nats : ∀{i} → Stream i Nat
force nats = 0 , smap suc nats

sums : Stream _ Nat
sums = scanl (_+_) 0 (tail nats)

main : IO Unit
main = printNat (sums ! 10)
-- Expected output, due to Gauss: 55
