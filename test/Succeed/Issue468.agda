
module Issue468 where

data Unit : Set where
 nothing : Unit

data Maybe (A : Set) : Set where
 nothing : Maybe A
 just    : A → Maybe A

data P : (R : Set) → Maybe R → Set₁ where
 p : (R : Set) (x : R) → P R (just x)

works : P Unit (just _)
works = p _ nothing

fails : Unit → P Unit (just _)
fails x = p _ nothing
