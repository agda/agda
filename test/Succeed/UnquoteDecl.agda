
module UnquoteDecl where

open import Common.Prelude
open import Common.Reflection
open import Common.Equality
open import Agda.Builtin.Sigma

infixr 3 _`⇒_
pattern _`⇒_ a b = pi (vArg a) (abs "_" b)
pattern `Nat = def (quote Nat) []

unquoteDecl x =
  define (vArg x) (funDef `Nat (clause [] [] (quoteTerm 15) ∷ []))

y = x + 4

-- unquoteDecl loop = define loop (funDef `Nat (clause [] (def (quote loop) []) ∷ []))

pattern `zero  = con (quote zero) []
pattern `suc n = con (quote suc) (vArg n ∷ [])

-- Note that in the body of the unquote, 'plus' really means 'quote plus'.
unquoteDecl plus =
  define (vArg plus) (
  funDef (`Nat `⇒ `Nat `⇒ `Nat)
         ( clause (("y" , vArg unknown) ∷ []) (vArg (con (quote zero) []) ∷ vArg (var 0) ∷ []) (var 0 [])
         ∷ clause (("y" , vArg unknown) ∷ ("x" , vArg unknown) ∷ [])
                  (vArg (con (quote suc) (vArg (var 1) ∷ [])) ∷ vArg (var 0) ∷ [])
                  (`suc (def plus (vArg (var 1 []) ∷ vArg (var 0 []) ∷ [])))
         ∷ []))

prf : plus 1 1 ≡ 2
prf = refl

magicDef : FunDef
magicDef =
  funDef (def (quote ⊥) [] `⇒ `Nat)
         (absurdClause (("()" , vArg unknown) ∷ []) (vArg absurd ∷ []) ∷ [])

unquoteDecl magic = define (vArg magic) magicDef
