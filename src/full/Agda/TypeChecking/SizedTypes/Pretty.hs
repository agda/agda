
module Agda.TypeChecking.SizedTypes.Pretty where

import Control.Monad
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base.Types
import Agda.TypeChecking.Monad.Builtin (HasBuiltins, builtinSizeInf, getBuiltin')
import Agda.TypeChecking.Monad.Context (unsafeModifyContext, contextNames)
import Agda.TypeChecking.Monad.SizedTypes
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.SizedTypes.Syntax

import Agda.Utils.Function
import Agda.Utils.Impossible

-- | Turn a size expression into a term.
unSizeExpr :: HasBuiltins m => DBSizeExpr -> m Term
unSizeExpr a =
  case a of
    Infty         -> fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSizeInf
    Rigid r (O n) -> do
      unless (n >= 0) __IMPOSSIBLE__
      sizeSuc n $ var $ rigidIndex r
    Flex (SizeMeta x es) (O n) -> do
      unless (n >= 0) __IMPOSSIBLE__
      sizeSuc n $ MetaV x $ map (Apply . defaultArg . var) es
    Const{} -> __IMPOSSIBLE__

instance PrettyTCM SizeMeta where
  prettyTCM (SizeMeta x es) = prettyTCM (MetaV x $ map (Apply . defaultArg . var) es)

-- | Assumes we are in the right context.
instance PrettyTCM (SizeConstraint) where
  prettyTCM (Constraint a cmp b) = do
    u <- unSizeExpr a
    v <- unSizeExpr b
    prettyTCM u <+> pretty cmp <+> prettyTCM v

instance PrettyTCM HypSizeConstraint where
  prettyTCM (HypSizeConstraint cxt _ hs c) =
    unsafeModifyContext (const cxt) $ do
      let cxtNames = contextNames cxt
      -- text ("[#cxt=" ++ show (size cxt) ++ "]") <+> do
      prettyList (map prettyTCM cxtNames) <+> do
        applyUnless (null hs)
          ((hcat (punctuate ", " $ map prettyTCM hs) <+> "|-") <+>)
          (prettyTCM c)
