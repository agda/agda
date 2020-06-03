-- | Checking definitions of typed/untyped pattern synonyms

module Agda.TypeChecking.Rules.PatternSynDef where

import Data.Void

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Info

import Agda.TypeChecking.Monad

checkPatternSynDef :: QName -> Maybe (A.DefInfo, A.Expr) -> [Arg BindName] ->
                      A.Pattern' Void -> TCM ()
checkPatternSynDef name Nothing as rhs = ?
checkPatternSynDef name (Just (i, e)) as rhs = ?

checkTyped :: QName -> A.DefInfo -> Type -> [Arg BindName] ->
              A.Pattern' Void -> TCM ()
checkTyped name i ty as rhs = do
  TelV tel bty <- telViewUpTo (length as) ty
  unless (size tel == length as) $ genericError "pattern syn telescope not right"

-- telViewUpToArgs :: [Arg BindName] -> Type -> m TelView
-- telViewUpToArgs [] t = return $ TelV EmptyTel t
-- telViewUpToArgs (Arg i n : as) t = do
--   t <- reduce t
--   case argInfoHiding a, unEl t of
--     NotHidden, Pi ta tb | NotHidden == getHiding ta ->
--       absV ?
--     _ -> return $ TelV EmptyTel t
--   where
--     absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

checkLHS :: QName -> Type -> [Arg BindName] -> (Type -> TCM a) -> TCM a
checkLHS name ty [] k = k ty
checkLHS name ty (Arg i n : as) k = do
  ty <- reduce ty
  case argInfoHiding i, unEl t of
    NotHidden, Pi ta tb | visible ta ->
      lambdaAddContext (unBind n) (absName tb) ta $
        underAbstractionAbs ta tb $ \tb -> checkLHS name tb as k
