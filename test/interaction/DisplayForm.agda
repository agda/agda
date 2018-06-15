
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

plus : Nat → Nat → Nat
plus zero b = b
plus (suc a) b = suc (plus a b)

infixl 6 _+_
_+_ = plus

{-# DISPLAY suc n = 1 + n #-}
{-# DISPLAY plus a b = a + b #-}

postulate
  T : {A : Set} → A → Set

test₁ : ∀ a b → T (plus (suc a) b)
test₁ a b = {!!}

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 4 _∷_

[_] : ∀ {A} → A → Vec A (suc zero)
[ x ] = x ∷  []

{-# DISPLAY Vec._∷_ x Vec.[] = [ x ] #-}

test₂ : (n : Nat) → T (n Vec.∷ [])
test₂ n = {!!}

append : ∀ {A : Set} {n m} → Vec A n → Vec A m → Vec A (n + m)
append []       ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

infixr 4 _++_
_++_ = append

{-# DISPLAY append xs ys = xs ++ ys #-}
{-# DISPLAY append xs (y Vec.∷ ys) = xs ++ [ y ] ++ ys #-}

test₃ : ∀ {n} (xs ys : Vec Nat n) → T (append xs (n ∷ ys))
test₃ {n} xs ys = {!!}
