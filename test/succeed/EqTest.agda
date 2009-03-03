module EqTest where

data _≡_ {a : Set} (x : a) : a -> Set where
  refl : x ≡ x

data Maybe (a : Set) : Set where
  just    : a -> Maybe a
  nothing : Maybe a

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_≟_ : (x y : ℕ) -> Maybe (x ≡ y)
suc m  ≟ suc n with m ≟ n
suc .n ≟ suc n |    just refl = just refl
suc m  ≟ suc n |    nothing   = nothing
zero   ≟ suc _ = nothing
suc m  ≟ zero  = nothing
zero   ≟ zero  = just refl
