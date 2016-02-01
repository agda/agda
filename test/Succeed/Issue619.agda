
open import Common.Reflection
open import Common.Prelude hiding (_<$>_)
open import Common.Equality

_<$>_ : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
f <$> just x  = just (f x)
f <$> nothing = nothing

_==_ = primQNameEquality

-- This is awkward!
awkwardUnquoteBool : Term → Maybe Bool
awkwardUnquoteBool (con c []) =
  if c == quote true then just true
  else if c == quote false then just false
  else nothing
awkwardUnquoteBool v = nothing

testAwkward : just false ≡ awkwardUnquoteBool (quoteTerm false)
testAwkward = refl

-- This is nicer!
pattern `false = con (quote false) []
pattern `true  = con (quote true) []

unquoteBool : Term → Maybe Bool
unquoteBool `false = just false
unquoteBool `true  = just true
unquoteBool _      = nothing

test : just true ≡ unquoteBool (quoteTerm true)
test = refl
