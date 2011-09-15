
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
isReallyEmptyType :: Type -> TCM ()
isReallyEmptyType t = noConstraints $ isEmptyType t

isEmptyType :: Type -> TCM ()
isEmptyType t = do
  tb <- reduceB t
  let t = ignoreBlocking tb
  case unEl <$> tb of
    -- if t is blocked or a meta, we cannot decide emptyness now. postpone
    NotBlocked MetaV{} -> addConstraint (IsEmpty t)
    Blocked{}          -> addConstraint (IsEmpty t)
    _                  -> do
    -- from the current context xs:ts, create a pattern list
    -- xs _ : ts t and try to split on _ (the last variable)
      tel0 <- getContextTelescope
      let gamma = telToList tel0 ++ [defaultArg ("_", t)]
          ps    = [ Arg h r $ VarP x | Arg h r (x, _) <- gamma ]
          tel   = telFromList gamma

      r <- split Inductive tel (idP $ size tel) ps 0

      case r of
        Left err  -> typeError $ ShouldBeEmpty t []
        Right []  -> return ()
        Right cs  -> typeError $ ShouldBeEmpty t $ map (unArg . last . scPats) cs
