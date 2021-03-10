
module UnquoteDef where

open import Common.Reflection
open import Common.Prelude
open import Agda.Builtin.Sigma

module Target where
  mutual
    even : Nat → Bool
    even zero    = true
    even (suc n) = odd n

    odd : Nat → Bool
    odd zero    = false
    odd (suc n) = even n

pattern `false = con (quote false) []
pattern `true  = con (quote true) []
pattern `zero  = con (quote zero) []
pattern `suc n = con (quote suc) (vArg n ∷ [])

pattern _`→_ a b = pi (vArg a) (abs "A" b)
pattern `Nat = def (quote Nat) []
pattern `Bool = def (quote Bool) []

`idType = `Nat `→ `Nat

-- Simple non-mutual case
`id : QName → FunDef
`id f = funDef `idType
        ( clause []                       (vArg `zero          ∷ []) `zero
        ∷ clause (("n" , vArg `Nat) ∷ []) (vArg (`suc (var 0)) ∷ []) (`suc (def f (vArg (var 0 []) ∷ [])))
        ∷ [])

`idDef : QName → List Clause
`idDef f =
   clause []                       (vArg `zero          ∷ []) `zero
 ∷ clause (("n" , vArg `Nat) ∷ []) (vArg (`suc (var 0)) ∷ []) (`suc (def f (vArg (var 0 []) ∷ [])))
 ∷ []

-- Andreas, 2016-07-17
-- Also testing effect of abstract on unquoteDef.

abstract
  id : Nat → Nat
  unquoteDef id = defineFun id (`idDef id)
  -- This raised the UselessAbstract error in error.
  -- Should work.

-- Now for the mutal ones
`evenOdd : Term → QName → List Clause
`evenOdd base step =
    clause []                       (vArg `zero          ∷ []) base
  ∷ clause (("n" , vArg `Nat) ∷ []) (vArg (`suc (var 0)) ∷ []) (def step (vArg (var 0 []) ∷ []))
  ∷ []

_>>_ : TC ⊤ → TC ⊤ → TC ⊤
m >> m₁ = bindTC m λ _ → m₁

even odd : Nat → Bool
unquoteDef even odd =
  defineFun even (`evenOdd `true  odd) >>
  defineFun odd  (`evenOdd `false even)
