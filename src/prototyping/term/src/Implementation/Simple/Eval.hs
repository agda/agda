
module Implementation.Simple.Eval where

import Types.Blocked
import Implementation.Simple.Term
import Implementation.Simple.Monad

whnf :: Term -> TC (Blocked Term)
whnf (Term v) = case v of
  App (Meta x) es -> do
    i <- getMetaInst x
    case i of
      Open{}   -> return $ NotBlocked (Term v)
      Inst _ v -> whnf $ elim' v es
  _ -> return $ NotBlocked (Term v)

