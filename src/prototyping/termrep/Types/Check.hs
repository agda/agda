
module Types.Check where

import qualified Syntax.Abstract as A
import Terms.Interface
import Types.Monad

infer :: TermRep r => A.Expr -> TC (Term r, Type r)
infer e = undefined

check :: TermRep r => A.Expr -> Type r -> TC (Term r)
check e t = case A.elimView e of
  A.ElimV e els -> undefined
  A.NoElim e    -> undefined
