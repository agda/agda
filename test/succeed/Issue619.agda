
open import Common.Reflect
open import Common.Prelude
open import Common.Equality

data Maybe A : Set where
  nothing : Maybe A
  just : A → Maybe A

_<$>_ : ∀ {A B} → (A → B) → Maybe A → Maybe B
f <$> just x  = just (f x)
f <$> nothing = nothing

_==_ = primQNameEquality

-- This is awkward!
awkwardUnquoteNat : Term → Maybe Nat
awkwardUnquoteNat (con z []) =
  if z == quote Nat.zero
  then just 0
  else nothing
awkwardUnquoteNat (con s (arg _ n ∷ [])) =
  if s == quote Nat.suc
  then suc <$> awkwardUnquoteNat n
  else nothing
awkwardUnquoteNat v = nothing

testAwkward : just 10 ≡ awkwardUnquoteNat (quoteTerm 10)
testAwkward = refl

-- This is nicer!
pattern `zero  = con (quote Nat.zero) []
pattern `suc n = con (quote Nat.suc) (arg _ n ∷ [])

unquoteNat : Term → Maybe Nat
unquoteNat `zero    = just zero
unquoteNat (`suc n) = suc <$> unquoteNat n
unquoteNat _        = nothing

test : just 10 ≡ unquoteNat (quoteTerm 10)
test = refl
