module Issue637 where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

infixl 60 _+_
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (n + m)

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

`1 = suc zero
`2 = suc `1
`3 = suc `2
`4 = `2 + `2
`8 = `4 + `4
`16 = `8 + `8
`32 = `16 + `16
`50 = `32 + `16 + `2
`64 = `32 + `32
`100 = `64 + `32 + `4
`200 = `100 + `100
`400 = `200 + `200
`800 = `400 + `400
`1000 = `800 + `200
`2000 = `1000 + `1000
`4000 = `2000 + `2000

prf : `16 ≡ (`4 + (`4 + `8))
prf = refl

infixr 40 _∷_
data Vec : Nat → Set where
  [] : Vec zero
  _∷_ : ∀ {n} → Nat → Vec n → Vec (suc n)

fromN : ∀ {n} → Nat → Vec n
fromN {zero} _ = []
fromN {suc n} x = x ∷ fromN (suc x)

sum : ∀ {n} → Vec n → Nat
sum [] = zero
sum (n ∷ ns) = n + sum ns

prf₁ : sum (fromN {`100} `1) ≡ (`4000 + `1000 + `50)
prf₁ = refl
