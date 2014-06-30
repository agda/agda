
open import Common.Reflect
open import Common.Prelude
open import Common.Equality

pattern vArg x = arg (arginfo visible relevant) x
pattern hArg x = arg (arginfo hidden  relevant) x

pattern `el x = el (lit 0) x
pattern `Nat = `el (def (quote Nat) [])
pattern _`→_ a b = `el (pi (vArg a) b)
pattern `Set      = el (lit 1) (sort (lit 0))
pattern `⊥       = `el (def (quote ⊥) [])

pattern `zero  = con (quote zero) []
pattern `suc n = con (quote suc) (vArg n ∷ [])

prDef : FunDef
prDef =
  funDef (`Nat `→ `Nat)
       ( clause [] (ext-lam ( clause (vArg `zero ∷ []) `zero
                            ∷ clause (vArg (`suc var) ∷ []) (var 0 [])
                            ∷ []) [])
       ∷ [] )

magicDef : FunDef
magicDef =
  funDef (el (lit 1) (pi (hArg `Set) (`⊥ `→ `el (var 1 []))))
       ( clause [] (ext-lam ( absurd-clause (vArg absurd ∷ [])
                            ∷ []) [])
       ∷ [] )

unquoteDecl magic = magicDef

checkMagic : {A : Set} → ⊥ → A
checkMagic = magic

unquoteDecl pr = prDef

magic′ : {A : Set} → ⊥ → A
magic′ = unquote (ext-lam (absurd-clause (vArg absurd ∷ []) ∷ []) [])

module Pred (A : Set) where
  unquoteDecl pr′ = prDef

check : pr 10 ≡ 9
check = refl

check′ : Pred.pr′ ⊥ 10 ≡ 9
check′ = refl
