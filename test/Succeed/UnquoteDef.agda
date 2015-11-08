
module UnquoteDef where

open import Common.Reflection
open import Common.Prelude

module Target where
  mutual
    even : Nat → Bool
    even zero    = true
    even (suc n) = odd n

    odd : Nat → Bool
    odd zero    = false
    odd (suc n) = even n

pattern vArg x = arg (argInfo visible relevant) x

pattern `false = con (quote false) []
pattern `true  = con (quote true) []
pattern `zero  = con (quote zero) []
pattern `suc n = con (quote suc) (vArg n ∷ [])

pattern el- a = el unknown a
pattern _`→_ a b = pi (vArg (el- a)) (abs "A" (el- b))
pattern `Nat = def (quote Nat) []
pattern `Bool = def (quote Bool) []

-- Simple non-mutual case
`id : QName → FunDef
`id f = funDef (el- (`Nat `→ `Nat))
        ( clause (vArg `zero            ∷ []) `zero
        ∷ clause (vArg (`suc (var "n")) ∷ []) (`suc (def f (vArg (var 0 []) ∷ [])))
        ∷ [])

`idType = el- (`Nat `→ `Nat)

`idDef : QName → List Clause
`idDef f =
   clause (vArg `zero            ∷ []) `zero
 ∷ clause (vArg (`suc (var "n")) ∷ []) (`suc (def f (vArg (var 0 []) ∷ [])))
 ∷ []

-- id : Nat → Nat
-- unquoteDef id = `idDef id

-- Now for the mutal ones
`evenOdd : Term → QName → List Clause
`evenOdd base step =
    clause (vArg `zero            ∷ []) base
  ∷ clause (vArg (`suc (var "n")) ∷ []) (def step (vArg (var 0 []) ∷ []))
  ∷ []

even odd : Nat → Bool
unquoteDef even = `evenOdd `true  (quote odd)
unquoteDef odd  = `evenOdd `false (quote even)
