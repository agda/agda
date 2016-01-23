{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards     #-}

module Agda.TypeChecking.Unquote where

import Control.Applicative
import Control.Monad.State (evalState, get, put)
import Control.Monad.Writer (execWriterT, tell)
import Control.Monad.Trans (lift)

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
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

import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.Monad ( ifM )
import Agda.Utils.Permutation ( Permutation(Perm) )
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

#include "undefined.h"

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

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

{-unquoteFailedGeneric :: String -> UnquoteM a
unquoteFailedGeneric msg = typeError . GenericError $ "Unable to unquote the " ++ msg

unquoteFailed :: String -> String -> Term -> TCM a
unquoteFailed kind msg t = do doc <- prettyTCM t
                              unquoteFailedGeneric $ "term (" ++ show doc ++ ") of type " ++ kind ++ ".\nReason: " ++ msg ++ "."
-}
class Unquote a where
  unquote :: Term -> UnquoteM a

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

pickName :: Type -> String
pickName a =
  case unEl a of
    Pi{}   -> "f"
    Sort{} -> "A"
    Def d _ | c:_ <- show (qnameName d),
              isAlpha c -> [toLower c]
    _    -> "_"

instance Unquote I.ArgInfo where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [h,r] -> do
        choice
          [(c `isCon` primArgArgInfo, ArgInfo <$> unquoteN h <*> unquoteN r <*> return [])]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "ArgInfo" t

instance Unquote a => Unquote (I.Arg a) where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [info,x] -> do
        choice
          [(c `isCon` primArgArg, Arg <$> unquoteN info <*> unquoteN x)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Arg" t

-- Andreas, 2013-10-20: currently, post-fix projections are not part of the
-- quoted syntax.
instance Unquote a => Unquote (Elim' a) where
  unquote t = Apply <$> unquote t

instance Unquote Integer where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitInt _ n) -> return n
      _ -> throwException $ NotALiteral "Integer" t

instance Unquote Double where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitFloat _ x) -> return x
      _ -> throwException $ NotALiteral "Float" t

instance Unquote Char where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitChar _ x) -> return x
      _ -> throwException $ NotALiteral "Char" t

instance Unquote Str where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitString _ x) -> return (Str x)
      _ -> throwException $ NotALiteral "String" t

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- lift $ reduce t
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
    t <- lift $ reduce t
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
    t <- lift $ reduce t
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
    t <- lift $ reduce t
    case ignoreSharing t of
      Lit (LitQName _ x) -> return x
      _                  -> throwException $ NotALiteral "QName" t

instance Unquote ConHead where
  unquote t = lift . getConHead =<< ensureCon =<< unquote t

instance Unquote a => Unquote (Abs a) where
  unquote t = Abs "_" <$> unquote t

instance Unquote Sort where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [(c `isCon` primAgdaSortUnsupported, pure $ Type $ Max [Plus 0 $ UnreducedLevel $ hackReifyToMeta])]
          __IMPOSSIBLE__
      Con c [u] -> do
        choice
          [(c `isCon` primAgdaSortSet, Type <$> unquoteN u)
          ,(c `isCon` primAgdaSortLit, Type . levelMax . (:[]) . ClosedLevel <$> unquoteN u)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Sort" t

instance Unquote Level where
  unquote l = Max . (:[]) . Plus 0 . UnreducedLevel <$> unquote l

instance Unquote Type where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [s, u] -> do
        choice
          [(c `isCon` primAgdaTypeEl, El <$> unquoteN s <*> unquoteN u)]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Type" t

instance Unquote Literal where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x] ->
        choice
          [ (c `isCon` primAgdaLitNat,    LitInt    noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitFloat,  LitFloat  noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitChar,   LitChar   noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitString, LitString noRange . unStr <$> unquoteN x)
          , (c `isCon` primAgdaLitQName,  LitQName  noRange <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Literal" t

instance Unquote Term where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] ->
        choice
          [(c `isCon` primAgdaTermUnsupported, pure hackReifyToMeta)]
          __IMPOSSIBLE__

      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaTermSort,   Sort <$> unquoteN x)
          , (c `isCon` primAgdaTermLit,    Lit <$> unquoteN x) ]
          __IMPOSSIBLE__

      Con c [x, y] ->
        choice
          [ (c `isCon` primAgdaTermVar, Var <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermCon, Con <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermDef, Def <$> (ensureDef =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermLam, Lam <$> (flip setHiding defaultArgInfo <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermPi,  mkPi <$> (domFromArg <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermExtLam, mkExtLam <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
        where
          mkExtLam = ExtLam
          mkPi a (Abs _ b) = Pi a (Abs x b)
            where x | 0 `freeIn` b = pickName (unDom a)
                    | otherwise    = "_"
          mkPi _ NoAbs{} = __IMPOSSIBLE__

      Con{} -> __IMPOSSIBLE__
      Lit{} -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Term" t

instance Unquote Pattern where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [] -> do
        choice
          [ (c `isCon` primAgdaPatVar,    pure (VarP "x"))
          , (c `isCon` primAgdaPatAbsurd, pure (VarP "()"))
          , (c `isCon` primAgdaPatDot,    pure (DotP hackReifyToMeta))
          ] __IMPOSSIBLE__
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaPatProj, ProjP <$> unquoteN x)
          , (c `isCon` primAgdaPatLit,  LitP  <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaPatCon, flip ConP noConPatternInfo <$> unquoteN x <*> (map (fmap unnamed) <$> unquoteN y)) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Pattern" t

data UnquotedFunDef = UnQFun Type [Clause]

instance Unquote Clause where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x] -> do
        choice
          [ (c `isCon` primAgdaClauseAbsurd, mkClause Nothing <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaClauseClause, checkClause =<< mkClause . Just <$> unquoteN y <*> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Clause" t
    where
      mkClause :: Maybe Term -> [I.Arg Pattern] -> I.Clause
      mkClause b ps0 =
        Clause { clauseRange     = noRange
               , clauseTel       = dummyTel n'
               , clausePerm      = Perm n vs
               , namedClausePats = ps
               , clauseBody      = mkBody n b
               , clauseType      = Nothing }
        where
          ps = map (fmap unnamed) ps0
          n  = vars True ps  -- with dot patterns
          n' = vars False ps -- without dot patterns
          dummyTel 0 = EmptyTel
          dummyTel n = ExtendTel dummyDom (Abs "x" $ dummyTel (n - 1))
          mkBody 0 b = maybe NoBody Body b
          mkBody n b = Bind $ Abs "x" $ mkBody (n - 1) b
          vars d ps = sum $ map (vars' d . namedArg) ps
          vars' d (ConP _ _ ps) = vars d ps
          vars' d VarP{}      = 1
          vars' d DotP{}      = if d then 1 else 0
          vars' d LitP{}      = 0
          vars' d ProjP{}     = 0

          vs = evalState (execWriterT $ mapM_ (computePerm . namedArg) ps) 0
          next = do n <- get; put (n + 1); return n

          computePerm (ConP _ _ ps) = mapM_ (computePerm . namedArg) ps
          computePerm VarP{}        = tell . (:[]) =<< next
          computePerm DotP{}        = () <$ next
          computePerm LitP{}        = return ()
          computePerm ProjP{}       = return ()

      checkClause :: I.Clause -> UnquoteM I.Clause
      checkClause cl@Clause{ clausePerm = Perm n vs , clauseBody = body } = do
        let freevs    = allFreeVars $ fromMaybe __IMPOSSIBLE__ $ getBody body
            propervs  = Set.fromList $ map ((n-1)-) vs
            dottedvs  = Set.difference (Set.fromList [0..n-1]) propervs
            offending = Set.intersection freevs dottedvs
        Agda.TypeChecking.Monad.reportSDoc "tc.unquote.clause.dotvars" 30 $ vcat
          [ text $ "checkClause "
          , nest 2 $ text $ "free vars:      " ++ show freevs
          , nest 2 $ text $ "dotted vars:    " ++ show dottedvs
          , nest 2 $ text $ "offending vars: " ++ show offending
          ]
        if Set.null offending
          then return cl
          else throwException $ RhsUsesDottedVar (Set.toList offending) t

instance Unquote UnquotedFunDef where
  unquote t = do
    t <- lift $ reduce t
    case ignoreSharing t of
      Con c [x, y] -> do
        choice
          [ (c `isCon` primAgdaFunDefCon, UnQFun <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ -> __IMPOSSIBLE__
      _ -> throwException $ NotAConstructor "Pattern" t

reifyUnquoted :: Reify a e => a -> TCM e
reifyUnquoted = nowReifyingUnquoted . disableDisplayForms . withShowAllArguments . reify
