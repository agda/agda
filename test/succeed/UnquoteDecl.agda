
module UnquoteDecl where

open import Common.Prelude
open import Common.Reflection
open import Common.Equality

infixr 3 _`⇒_
pattern vArg x = arg (argInfo visible relevant) x
pattern `el a = el (lit 0) a
pattern _`⇒_ a b = `el (pi (vArg a) (abs "_" b))
pattern `Nat = `el (def (quote Nat) [])

unquoteDecl x =
  funDef `Nat (clause [] (quoteTerm 15) ∷ [])

y = x + 4

-- unquoteDecl loop = funDef `Nat (clause [] (def (quote loop) []) ∷ [])

pattern `zero  = con (quote zero) []
pattern `suc n = con (quote suc) (vArg n ∷ [])

-- Note that in the body of the unquote, 'plus' really means 'quote plus'.
unquoteDecl plus =
  funDef (`Nat `⇒ `Nat `⇒ `Nat)
         ( clause (vArg (con (quote zero) []) ∷ vArg (var "y") ∷ []) (var 0 [])
         ∷ clause (vArg (con (quote suc) (vArg (var "x") ∷ [])) ∷ vArg (var "y") ∷ [])
                  (`suc (def plus (vArg (var 1 []) ∷ vArg (var 0 []) ∷ [])))
         ∷ [])

prf : plus 1 1 ≡ 2
prf = refl

magicDef : FunDef
magicDef =
  funDef (`el (def (quote ⊥) []) `⇒ `Nat)
         (absurdClause (vArg absurd ∷ []) ∷ [])

unquoteDecl magic = magicDef
