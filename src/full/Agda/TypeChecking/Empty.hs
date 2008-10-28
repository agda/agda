
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
  t <- reduce t
  case unEl t of
    MetaV _ _  -> buildConstraint (IsEmpty t)
    BlockedV _ -> buildConstraint (IsEmpty t)
    _          -> do
      tel0 <- getContextTelescope
      let tel = telFromList $ telToList tel0 ++ [Arg NotHidden ("_", t)]
          ps  = [ Arg h $ VarP x | Arg h (x, _) <- telToList tel ]

      r <- split tel (idP $ size tel) ps 0

      case r of
        Left err  -> typeError $ ShouldBeEmpty t []
        Right []  -> return []
        Right cs  -> typeError $ ShouldBeEmpty t $ map (unArg . last . scPats) cs

