{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Agda.TypeChecking.Unquote where

import Control.Applicative
import Control.Monad.State (runState, get, put)
import Control.Monad.Writer (execWriterT, tell)
import Control.Monad.Trans (lift)

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Reflected as R
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Translation.InternalToAbstract

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Datatypes ( getConHead )
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.Monad ( ifM )
import Agda.Utils.Permutation ( Permutation(Perm), compactP )
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

#include "undefined.h"

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

agdaTypeType :: TCM Type
agdaTypeType = El (mkType 0) <$> primAgdaType

qNameType :: TCM Type
qNameType = El (mkType 0) <$> primQName

type UnquoteM = ExceptionT UnquoteError TCM

runUnquoteM :: UnquoteM a -> TCM (Either UnquoteError a)
runUnquoteM = runExceptionT

isCon :: ConHead -> TCM Term -> UnquoteM Bool
isCon con tm = do t <- lift tm
                  case ignoreSharing t of
                    Con con' _ -> return (con == con')
                    _ -> return False

reduceQuotedTerm :: Term -> UnquoteM Term
reduceQuotedTerm t = ifBlocked t
                       (\m _ -> throwException $ BlockedOnMeta m)
                       (\  t -> return t)


class Unquote a where
  unquote :: I.Term -> UnquoteM a

unquoteH :: Unquote a => I.Arg Term -> UnquoteM a
unquoteH a | isHidden a && isRelevant a =
    unquote $ unArg a
unquoteH a = throwException $ BadVisibility "hidden"  a

unquoteN :: Unquote a => I.Arg Term -> UnquoteM a
unquoteN a | notHidden a && isRelevant a =
    unquote $ unArg a
unquoteN a = throwException $ BadVisibility "visible" a

choice :: Monad m => [(m Bool, m a)] -> m a -> m a
choice [] dflt = dflt
choice ((mb, mx) : mxs) dflt = ifM mb mx $ choice mxs dflt

ensureDef :: QName -> UnquoteM QName
ensureDef x = do
  i <- (theDef <$> getConstInfo x) `catchError` \_ -> return Axiom  -- for recursive unquoteDecl
  case i of
    Constructor{} -> do
      def <- lift $ prettyTCM =<< primAgdaTermDef
      con <- lift $ prettyTCM =<< primAgdaTermCon
      throwException $ ConInsteadOfDef x (show def) (show con)
    _ -> return x

ensureCon :: QName -> UnquoteM QName
ensureCon x = do
  i <- (theDef <$> getConstInfo x) `catchError` \_ -> return Axiom  -- for recursive unquoteDecl
  case i of
    Constructor{} -> return x
    _ -> do
      def <- lift $ prettyTCM =<< primAgdaTermDef
      con <- lift $ prettyTCM =<< primAgdaTermCon
      throwException $ DefInsteadOfCon x (show def) (show con)

pickName :: R.Type -> String
pickName a =
  case R.unEl a of
    R.Pi{}   -> "f"
    R.Sort{} -> "A"
    R.Def d _ | c:_ <- show (qnameName d),
              isAlpha c -> [toLower c]
    _        -> "_"

instance Unquote R.ArgInfo where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [h,r] -> do
        choice
          [(c `isCon` primArgArgInfo, ArgInfo <$> unquoteN h <*> unquoteN r <*> return [])]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "ArgInfo" t

instance Unquote a => Unquote (R.Arg a) where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [info,x] -> do
        choice
          [(c `isCon` primArgArg, Arg <$> unquoteN info <*> unquoteN x)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Arg" t

-- Andreas, 2013-10-20: currently, post-fix projections are not part of the
-- quoted syntax.
instance Unquote R.Elim where
  unquote t = R.Apply <$> unquote t

instance Unquote Integer where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Lit (LitInt _ n) -> return n
      _ -> throwException $ NotALiteral "Integer" t

instance Unquote Double where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Lit (LitFloat _ x) -> return x
      _ -> throwException $ NotALiteral "Float" t

instance Unquote Char where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Lit (LitChar _ x) -> return x
      _ -> throwException $ NotALiteral "Char" t

instance Unquote Str where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Lit (LitString _ x) -> return (Str x)
      _ -> throwException $ NotALiteral "String" t

unquoteString :: Term -> UnquoteM String
unquoteString x = unStr <$> unquote x

unquoteNString :: I.Arg Term -> UnquoteM String
unquoteNString x = unStr <$> unquoteN x

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [x,xs] -> do
        choice
          [(c `isCon` primCons, (:) <$> unquoteN x <*> unquoteN xs)]
          __IMPOSSIBLE__
      Con c [] -> do
        choice
          [(c `isCon` primNil, return [])]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "List" t

instance Unquote Hiding where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primHidden,  return Hidden)
          ,(c `isCon` primInstance, return Instance)
          ,(c `isCon` primVisible, return NotHidden)]
          __IMPOSSIBLE__
      Con c vs -> __IMPOSSIBLE__
      _        -> throwException $ NotAConstructor "Hiding" t

instance Unquote Relevance where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primRelevant,   return Relevant)
          ,(c `isCon` primIrrelevant, return Irrelevant)]
          __IMPOSSIBLE__
      Con c vs -> __IMPOSSIBLE__
      _        -> throwException $ NotAConstructor "Relevance" t

instance Unquote QName where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Lit (LitQName _ x) -> return x
      _                  -> throwException $ NotALiteral "QName" t

instance Unquote a => Unquote (R.Abs a) where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [x,y] -> do
        choice
          [(c `isCon` primAbsAbs, R.Abs <$> (hint <$> unquoteNString x) <*> unquoteN y)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Abs" t

    where hint x | not (null x) = x
                 | otherwise    = "_"

instance Unquote a => Unquote (R.Dom a) where
  unquote t = domFromArg <$> unquote t

instance Unquote R.Sort where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primAgdaSortUnsupported, return R.UnknownS)]
          __IMPOSSIBLE__
      Con c [u] -> do
        choice
          [(c `isCon` primAgdaSortSet, R.SetS <$> unquoteN u)
          ,(c `isCon` primAgdaSortLit, R.LitS <$> unquoteN u)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Sort" t

instance Unquote R.Type where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [s, u] -> do
        choice
          [(c `isCon` primAgdaTypeEl, R.El <$> unquoteN s <*> unquoteN u)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Type" t

instance Unquote Literal where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [x] ->
        choice
          [ (c `isCon` primAgdaLitNat,    LitInt    noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitFloat,  LitFloat  noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitChar,   LitChar   noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitString, LitString noRange <$> unquoteNString x)
          , (c `isCon` primAgdaLitQName,  LitQName  noRange <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Literal" t

instance Unquote R.Term where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [] ->
        choice
          [(c `isCon` primAgdaTermUnsupported, return R.Unknown)]
          __IMPOSSIBLE__

      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaTermSort,   R.Sort <$> unquoteN x)
          , (c `isCon` primAgdaTermLit,    R.Lit  <$> unquoteN x) ]
          __IMPOSSIBLE__

      Con c [x, y] ->
        choice
          [ (c `isCon` primAgdaTermVar,    R.Var    <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermCon,    R.Con    <$> (ensureCon =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermDef,    R.Def    <$> (ensureDef =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermLam,    R.Lam    <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermPi,     mkPi     <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermExtLam, R.ExtLam <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
        where
          mkPi :: R.Dom R.Type -> R.Abs R.Type -> R.Term
          -- TODO: implement Free for reflected syntax so this works again
          --mkPi a (R.Abs "_" b) = R.Pi a (R.Abs x b)
          --  where x | 0 `freeIn` b = pickName (unDom a)
          --          | otherwise    = "_"
          mkPi a (R.Abs "_" b) = R.Pi a (R.Abs (pickName (unDom a)) b)
          mkPi a b = R.Pi a b

      Con{} -> __IMPOSSIBLE__
      Lit{} -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Term" t

instance Unquote R.Pattern where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [ (c `isCon` primAgdaPatAbsurd, return R.AbsurdP)
          , (c `isCon` primAgdaPatDot,    return R.DotP)
          ] __IMPOSSIBLE__
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaPatVar,  R.VarP  <$> unquoteNString x)
          , (c `isCon` primAgdaPatProj, R.ProjP <$> unquoteN x)
          , (c `isCon` primAgdaPatLit,  R.LitP  <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaPatCon, R.ConP <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Pattern" t

instance Unquote R.Clause where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaClauseAbsurd, R.AbsurdClause <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaClauseClause, R.Clause <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Clause" t

instance Unquote R.Definition where
  unquote t = do
    t <- reduceQuotedTerm t
    case ignoreSharing t of
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaFunDefCon, R.FunDef <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Pattern" t
