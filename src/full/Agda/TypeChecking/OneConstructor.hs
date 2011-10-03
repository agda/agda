-- Andreas, 2011-10-03, cut and paste from Empty.hs
module Agda.TypeChecking.OneConstructor where

import Control.Applicative

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Permutation
import Agda.Utils.Size

-- | Make sure that a type has exactly one constructor.
hasReallyOneConstructor :: Type -> TCM ()
hasReallyOneConstructor t = noConstraints $ hasOneConstructor t

hasOneConstructor :: Type -> TCM ()
hasOneConstructor t = do
  tb <- reduceB t
  let t = ignoreBlocking tb
  case unEl <$> tb of
    -- if t is blocked or a meta, we cannot decide emptyness now. postpone
    NotBlocked MetaV{} -> addConstraint (HasOneConstructor t)
    Blocked{}          -> addConstraint (HasOneConstructor t)
    _                  -> do
    -- from the current context xs:ts, create a pattern list
    -- xs _ : ts t and try to split on _ (the last variable)
      tel0 <- getContextTelescope
      let gamma = telToList tel0 ++ [defaultArg ("_", t)]
          ps    = [ Arg h r $ VarP x | Arg h r (x, _) <- gamma ]
          tel   = telFromList gamma

      r <- split Inductive tel (idP $ size tel) ps 0

      case r of
        Left err  -> case err of
          CantSplit c tel us vs _ -> traceCall (CheckHasOneConstructor t) $ typeError $ CoverageCantSplitOn c tel us vs
          _                       -> typeError $ ShouldHaveOneConstructor t Nothing
        Right [c]  -> return ()
        Right cs  -> typeError $ ShouldHaveOneConstructor t $ Just $ map (unArg . last . scPats) cs
