
module Agda.TypeChecking.Empty where

import Control.Applicative

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Reduce

import Agda.Utils.Permutation
import Agda.Utils.Size

-- | Make sure that a type is empty.
isEmptyType :: MonadTCM tcm => Type -> tcm ()
isEmptyType t = noConstraints $ isEmptyTypeC t

isEmptyTypeC :: MonadTCM tcm => Type -> tcm Constraints
isEmptyTypeC t = do
  tb <- reduceB t
  let t = ignoreBlocking tb
  case unEl <$> tb of
    NotBlocked MetaV{} -> buildConstraint (IsEmpty t)
    Blocked{}          -> buildConstraint (IsEmpty t)
    _                  -> do
      tel0 <- getContextTelescope
      let tel = telFromList $ telToList tel0 ++ [defaultArg ("_", t)]
          ps  = [ Arg h r $ VarP x | Arg h r (x, _) <- telToList tel ]

      r <- split Inductive tel (idP $ size tel) ps 0

      case r of
        Left err  -> typeError $ ShouldBeEmpty t []
        Right []  -> return []
        Right cs  -> typeError $ ShouldBeEmpty t $ map (unArg . last . scPats) cs
