{-# OPTIONS --cubical-compatible --erasure #-}

open import Agda.Builtin.Equality
postulate
  A : Set
  B : A → Set

data H (@0 A : Set) : Set where
  con : (@0 x : A) →  H A

data G : Set where
  con : (@0 x : A) → (@0 b : B x) → G

data D : Set where
  con : (@0 x : A) → B x → D
