
open import Common.Reflection
open import Common.Prelude
open import Common.Equality
open import Agda.Builtin.Sigma

pattern `Nat = def (quote Nat) []
pattern _`→_ a b = pi (vArg a) (abs "_" b)
pattern `Set     = sort (lit 0)
pattern `⊥       = def (quote ⊥) []

pattern `zero  = con (quote zero) []
pattern `suc n = con (quote suc) (vArg n ∷ [])

prDef : FunDef
prDef =
  funDef (`Nat `→ `Nat)
       ( clause [] [] (extLam ( clause [] (vArg `zero ∷ []) `zero
                              ∷ clause (("x" , vArg `Nat) ∷ []) (vArg (`suc (var 0)) ∷ []) (var 0 [])
                              ∷ []) [])
       ∷ [] )

magicDef : FunDef
magicDef =
  funDef (pi (hArg `Set) (abs "A" (`⊥ `→ var 1 [])))
       ( clause [] [] (extLam ( absurdClause (("()" , vArg `⊥) ∷ []) (vArg absurd ∷ [])
                              ∷ []) [])
       ∷ [] )

unquoteDecl magic = define (vArg magic) magicDef

checkMagic : {A : Set} → ⊥ → A
checkMagic = magic

unquoteDecl pr = define (vArg pr) prDef

magic′ : {A : Set} → ⊥ → A
magic′ = unquote (give (extLam (absurdClause (("()" , vArg `⊥) ∷ []) (vArg absurd ∷ []) ∷ []) []))

module Pred (A : Set) where
  unquoteDecl pr′ = define (vArg pr′) prDef

check : pr 10 ≡ 9
check = refl

check′ : Pred.pr′ ⊥ 10 ≡ 9
check′ = refl
