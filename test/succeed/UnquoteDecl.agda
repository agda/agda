
module UnquoteDecl where

open import Common.Prelude
open import Common.Reflection
open import Common.Equality

infixr 3 _`⇒_
pattern vArg x = arg (arginfo visible relevant) x
pattern `el a = el (lit 0) a
pattern _`⇒_ a b = `el (pi (vArg a) b)
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
         ( clause (vArg (con (quote zero) []) ∷ vArg var ∷ []) (var 0 [])
         ∷ clause (vArg (con (quote suc) (vArg var ∷ [])) ∷ vArg var ∷ [])
                  (`suc (def plus (vArg (var 1 []) ∷ vArg (var 0 []) ∷ [])))
         ∷ [])

prf : plus 1 1 ≡ 2
prf = refl

magicDef : FunDef
magicDef =
  funDef (`el (def (quote ⊥) []) `⇒ `Nat)
         (absurd-clause (vArg absurd ∷ []) ∷ [])

unquoteDecl magic = magicDef
