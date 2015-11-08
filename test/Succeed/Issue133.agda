
module Issue133 where

data Nat : Set where
  zz : Nat
  ss : Nat → Nat

data _==_ {X : Set}(x : X) : X → Set where
  refl : x == x

data Zero : Set where

data Eq? (x : Nat) : Nat → Set where
  same : Eq? x x
  diff : {y : Nat} → (x == y → Zero) → Eq? x y

-- This failed before due to absurd lambda checking not getting
-- postponed.
ioo : {y : Nat} → Eq? zz (ss y)
ioo {y} = diff λ ()

foo : {y : Nat} → zz == ss y → Zero
foo ()

goo : {y : Nat} → zz == ss y → Zero
goo = λ ()

hoo : {y : Nat}{X : Set} → ((zz == ss y → Zero) → X) → X
hoo boo = boo λ ()

