-- Testing that unquoting the reflection constructs work.
module UnquoteQuote where

open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Common.Product

q-zero : Term
q-zero = quoteTerm zero

qq-zero : Term
qq-zero = quoteTerm q-zero

qqq-zero : Term
qqq-zero = quoteTerm qq-zero

qqq-zero′ : Term
qqq-zero′ = quote-term qq-zero

double-unquote : unquote (unquote-term qq-zero []) ≡ 0
double-unquote = refl

triple-unquote : unquote (unquote-term (unquote-term qqq-zero []) []) ≡ 0
triple-unquote = refl

triple-unquote′ : unquote (unquote-term (unquote-term qqq-zero′ []) []) ≡ 0
triple-unquote′ = refl

pattern vArg x = arg (argInfo visible relevant) x

-- We can now define a version of the tactic keyword

`tactic : QName → Term
`tactic x = quote-goal (abs "g" (unquote-term (def x (vArg (var 0 []) ∷ [])) []))

default-tactic : Term → Term
default-tactic (def (quote Nat) []) = quoteTerm 42
default-tactic (def (quote Bool) []) = quoteTerm false
default-tactic _ = lit (string "bad type for default")

default : Term
default = `tactic (quote default-tactic)

defbool : Bool
defbool = unquote default

defnat : Nat
defnat = unquote default

ok : (defbool ≡ false) × (defnat ≡ 42)
ok = refl , refl
