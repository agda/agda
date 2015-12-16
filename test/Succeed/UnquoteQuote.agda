-- Testing that unquoting the reflection constructs work.
module UnquoteQuote where

open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Common.Product
open import Common.TC

q-zero : Term
q-zero = quoteTerm zero

qq-zero : Term
qq-zero = quoteTerm q-zero

qqq-zero : Term
qqq-zero = quoteTerm qq-zero

qqq-zero′ : Term
qqq-zero′ = quote-term qq-zero

`give : Term → Term
`give v = unquote-term (def (quote give) (arg (argInfo visible relevant) v ∷ [])) []

double-unquote : unquote (give (`give qq-zero)) ≡ 0
double-unquote = refl

triple-unquote : unquote (give (`give (`give qqq-zero))) ≡ 0
triple-unquote = refl

triple-unquote′ : unquote (give (`give (`give qqq-zero′))) ≡ 0
triple-unquote′ = refl

pattern vArg x = arg (argInfo visible relevant) x

-- We can now define a version of the tactic keyword
-- Not right now. TODO: do this in the new TC style.
{-
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
-}
