{-# LANGUAGE CPP               #-}

module Agda.TypeChecking.Unquote where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ((<>))
#endif

import Control.Arrow (first, second)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Monad.Trans (lift)

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Traversable (traverse)
import Data.Word

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Reflected as R
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Info
import Agda.Syntax.Translation.ReflectedToAbstract

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Primitive

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term
import {-# SOURCE #-} Agda.TypeChecking.Rules.Def

import Agda.Utils.Except
  ( mkExceptT
  , MonadError(catchError, throwError)
  , ExceptT
  , runExceptT
  )
import Agda.Utils.Either
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.String ( Str(Str), unStr )
import qualified Agda.Interaction.Options.Lenses as Lens

#include "undefined.h"
import Agda.Utils.Impossible

agdaTermType :: TCM Type
agdaTermType = El (mkType 0) <$> primAgdaTerm

agdaTypeType :: TCM Type
agdaTypeType = agdaTermType

qNameType :: TCM Type
qNameType = El (mkType 0) <$> primQName

data Dirty = Dirty | Clean
  deriving (Eq)

-- Keep track of the original context. We need to use that when adding new
-- definitions. Also state snapshot from last commit and whether the state is
-- dirty (definitions have been added).
type UnquoteState = (Dirty, TCState)
type UnquoteM = ReaderT Context (StateT UnquoteState (WriterT [QName] (ExceptT UnquoteError TCM)))

type UnquoteRes a = Either UnquoteError ((a, UnquoteState), [QName])

unpackUnquoteM :: UnquoteM a -> Context -> UnquoteState -> TCM (UnquoteRes a)
unpackUnquoteM m cxt s = runExceptT $ runWriterT $ runStateT (runReaderT m cxt) s

packUnquoteM :: (Context -> UnquoteState -> TCM (UnquoteRes a)) -> UnquoteM a
packUnquoteM f = ReaderT $ \ cxt -> StateT $ \ s -> WriterT $ mkExceptT $ f cxt s

runUnquoteM :: UnquoteM a -> TCM (Either UnquoteError (a, [QName]))
runUnquoteM m = do
  cxt <- asksTC envContext
  s   <- getTC
  z   <- unpackUnquoteM m cxt (Clean, s)
  case z of
    Left err              -> return $ Left err
    Right ((x, _), decls) -> Right (x, decls) <$ mapM_ isDefined decls
  where
    isDefined x = do
      def <- theDef <$> getConstInfo x
      case def of
        Function{funClauses = []} -> genericError $ "Missing definition for " ++ prettyShow x
        _       -> return ()

liftU1 :: (TCM (UnquoteRes a) -> TCM (UnquoteRes b)) -> UnquoteM a -> UnquoteM b
liftU1 f m = packUnquoteM $ \ cxt s -> f (unpackUnquoteM m cxt s)

liftU2 :: (TCM (UnquoteRes a) -> TCM (UnquoteRes b) -> TCM (UnquoteRes c)) -> UnquoteM a -> UnquoteM b -> UnquoteM c
liftU2 f m1 m2 = packUnquoteM $ \ cxt s -> f (unpackUnquoteM m1 cxt s) (unpackUnquoteM m2 cxt s)

inOriginalContext :: UnquoteM a -> UnquoteM a
inOriginalContext m =
  packUnquoteM $ \ cxt s ->
    modifyContext (const cxt) $ unpackUnquoteM m cxt s

isCon :: ConHead -> TCM Term -> UnquoteM Bool
isCon con tm = do t <- liftTCM tm
                  case t of
                    Con con' _ _ -> return (con == con')
                    _ -> return False

isDef :: QName -> TCM Term -> UnquoteM Bool
isDef f tm = do
  t <- liftTCM $ etaContract =<< normalise =<< tm
  case t of
    Def g _ -> return (f == g)
    _       -> return False

reduceQuotedTerm :: Term -> UnquoteM Term
reduceQuotedTerm t = do
  b <- ifBlocked t {-then-} (\ m _ -> pure $ Left  m)
                   {-else-} (\ _ t -> pure $ Right t)
  case b of
    Left m  -> do s <- gets snd; throwError $ BlockedOnMeta s m
    Right t -> return t

class Unquote a where
  unquote :: I.Term -> UnquoteM a

unquoteN :: Unquote a => Arg Term -> UnquoteM a
unquoteN a | visible a && isRelevant a =
    unquote $ unArg a
unquoteN a = throwError $ BadVisibility "visible" a

choice :: Monad m => [(m Bool, m a)] -> m a -> m a
choice [] dflt = dflt
choice ((mb, mx) : mxs) dflt = ifM mb mx $ choice mxs dflt

ensureDef :: QName -> UnquoteM QName
ensureDef x = do
  i <- either (const Axiom) theDef <$> getConstInfo' x  -- for recursive unquoteDecl
  case i of
    Constructor{} -> do
      def <- liftTCM $ prettyTCM =<< primAgdaTermDef
      con <- liftTCM $ prettyTCM =<< primAgdaTermCon
      throwError $ ConInsteadOfDef x (show def) (show con)
    _ -> return x

ensureCon :: QName -> UnquoteM QName
ensureCon x = do
  i <- either (const Axiom) theDef <$> getConstInfo' x  -- for recursive unquoteDecl
  case i of
    Constructor{} -> return x
    _ -> do
      def <- liftTCM $ prettyTCM =<< primAgdaTermDef
      con <- liftTCM $ prettyTCM =<< primAgdaTermCon
      throwError $ DefInsteadOfCon x (show def) (show con)

pickName :: R.Type -> String
pickName a =
  case a of
    R.Pi{}   -> "f"
    R.Sort{} -> "A"
    R.Def d _ | c:_ <- show (qnameName d),
              isAlpha c -> [toLower c]
    _        -> "_"

-- TODO: reflect Quantity
instance Unquote Modality where
  unquote t = (`Modality` defaultQuantity) <$> unquote t

instance Unquote ArgInfo where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [h,r] <- allApplyElims es -> do
        choice
          [(c `isCon` primArgArgInfo,
              ArgInfo <$> unquoteN h <*> unquoteN r <*> pure Reflected <*> pure unknownFreeVariables)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "arg info" t

instance Unquote a => Unquote (Arg a) where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [info,x] <- allApplyElims es -> do
        choice
          [(c `isCon` primArgArg, Arg <$> unquoteN info <*> unquoteN x)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "arg" t

-- Andreas, 2013-10-20: currently, post-fix projections are not part of the
-- quoted syntax.
instance Unquote R.Elim where
  unquote t = R.Apply <$> unquote t

instance Unquote Bool where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] ->
        choice [ (c `isCon` primTrue,  pure True)
               , (c `isCon` primFalse, pure False) ]
               __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "boolean" t

instance Unquote Integer where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitNat _ n) -> return n
      _ -> throwError $ NonCanonical "integer" t

instance Unquote Word64 where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitWord64 _ n) -> return n
      _ -> throwError $ NonCanonical "word64" t

instance Unquote Double where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitFloat _ x) -> return x
      _ -> throwError $ NonCanonical "float" t

instance Unquote Char where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitChar _ x) -> return x
      _ -> throwError $ NonCanonical "char" t

instance Unquote Str where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitString _ x) -> return (Str x)
      _ -> throwError $ NonCanonical "string" t

unquoteString :: Term -> UnquoteM String
unquoteString x = unStr <$> unquote x

unquoteNString :: Arg Term -> UnquoteM String
unquoteNString x = unStr <$> unquoteN x

data ErrorPart = StrPart String | TermPart R.Term | NamePart QName

instance PrettyTCM ErrorPart where
  prettyTCM (StrPart s) = text s
  prettyTCM (TermPart t) = prettyTCM t
  prettyTCM (NamePart x) = prettyTCM x

instance Unquote ErrorPart where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x] <- allApplyElims es ->
        choice [ (c `isCon` primAgdaErrorPartString, StrPart  <$> unquoteNString x)
               , (c `isCon` primAgdaErrorPartTerm,   TermPart <$> unquoteN x)
               , (c `isCon` primAgdaErrorPartName,   NamePart <$> unquoteN x) ]
               __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "error part" t

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x,xs] <- allApplyElims es -> do
        choice
          [(c `isCon` primCons, (:) <$> unquoteN x <*> unquoteN xs)]
          __IMPOSSIBLE__
      Con c _ [] -> do
        choice
          [(c `isCon` primNil, return [])]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "list" t

instance Unquote Hiding where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] -> do
        choice
          [(c `isCon` primHidden,  return Hidden)
          ,(c `isCon` primInstance, return (Instance NoOverlap))
          ,(c `isCon` primVisible, return NotHidden)]
          __IMPOSSIBLE__
      Con c _ vs -> __IMPOSSIBLE__
      _        -> throwError $ NonCanonical "visibility" t

instance Unquote Relevance where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] -> do
        choice
          [(c `isCon` primRelevant,   return Relevant)
          ,(c `isCon` primIrrelevant, return Irrelevant)]
          __IMPOSSIBLE__
      Con c _ vs -> __IMPOSSIBLE__
      _        -> throwError $ NonCanonical "relevance" t

instance Unquote QName where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitQName _ x) -> return x
      _                  -> throwError $ NonCanonical "name" t

instance Unquote a => Unquote (R.Abs a) where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x,y] <- allApplyElims es -> do
        choice
          [(c `isCon` primAbsAbs, R.Abs <$> (hint <$> unquoteNString x) <*> unquoteN y)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "abstraction" t

    where hint x | not (null x) = x
                 | otherwise    = "_"

instance Unquote MetaId where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitMeta r f x) -> liftTCM $ do
        live <- (f ==) <$> getCurrentPath
        unless live $ do
            m <- fromMaybe __IMPOSSIBLE__ <$> lookupModuleFromSource f
            typeError . GenericDocError =<<
              sep [ "Can't unquote stale metavariable"
                  , pretty m <> "." <> pretty x ]
        return x
      _ -> throwError $ NonCanonical "meta variable" t

instance Unquote a => Unquote (Dom a) where
  unquote t = domFromArg <$> unquote t

instance Unquote R.Sort where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] -> do
        choice
          [(c `isCon` primAgdaSortUnsupported, return R.UnknownS)]
          __IMPOSSIBLE__
      Con c _ es | Just [u] <- allApplyElims es -> do
        choice
          [(c `isCon` primAgdaSortSet, R.SetS <$> unquoteN u)
          ,(c `isCon` primAgdaSortLit, R.LitS <$> unquoteN u)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "sort" t

instance Unquote Literal where
  unquote t = do
    t <- reduceQuotedTerm t
    let litMeta r x = do
          file <- getCurrentPath
          return $ LitMeta r file x
    case t of
      Con c _ es | Just [x] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaLitNat,    LitNat    noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitFloat,  LitFloat  noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitChar,   LitChar   noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitString, LitString noRange <$> unquoteNString x)
          , (c `isCon` primAgdaLitQName,  LitQName  noRange <$> unquoteN x)
          , (c `isCon` primAgdaLitMeta,   litMeta   noRange =<< unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "literal" t

instance Unquote R.Term where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] ->
        choice
          [ (c `isCon` primAgdaTermUnsupported, return R.Unknown) ]
          __IMPOSSIBLE__

      Con c _ es | Just [x] <- allApplyElims es -> do
        choice
          [ (c `isCon` primAgdaTermSort,      R.Sort      <$> unquoteN x)
          , (c `isCon` primAgdaTermLit,       R.Lit       <$> unquoteN x) ]
          __IMPOSSIBLE__

      Con c _ es | Just [x, y] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaTermVar,     R.Var     <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermCon,     R.Con     <$> (ensureCon =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermDef,     R.Def     <$> (ensureDef =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermMeta,    R.Meta    <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermLam,     R.Lam     <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermPi,      mkPi      <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermExtLam,  R.ExtLam  <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
        where
          mkPi :: Dom R.Type -> R.Abs R.Type -> R.Term
          -- TODO: implement Free for reflected syntax so this works again
          --mkPi a (R.Abs "_" b) = R.Pi a (R.Abs x b)
          --  where x | 0 `freeIn` b = pickName (unDom a)
          --          | otherwise    = "_"
          mkPi a (R.Abs "_" b) = R.Pi a (R.Abs (pickName (unDom a)) b)
          mkPi a b = R.Pi a b

      Con{} -> __IMPOSSIBLE__
      Lit{} -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "term" t

instance Unquote R.Pattern where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] -> do
        choice
          [ (c `isCon` primAgdaPatAbsurd, return R.AbsurdP)
          , (c `isCon` primAgdaPatDot,    return R.DotP)
          ] __IMPOSSIBLE__
      Con c _ es | Just [x] <- allApplyElims es -> do
        choice
          [ (c `isCon` primAgdaPatVar,  R.VarP  <$> unquoteNString x)
          , (c `isCon` primAgdaPatProj, R.ProjP <$> unquoteN x)
          , (c `isCon` primAgdaPatLit,  R.LitP  <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ es | Just [x, y] <- allApplyElims es -> do
        choice
          [ (c `isCon` primAgdaPatCon, R.ConP <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "pattern" t

instance Unquote R.Clause where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x] <- allApplyElims es -> do
        choice
          [ (c `isCon` primAgdaClauseAbsurd, R.AbsurdClause <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ es | Just [x, y] <- allApplyElims es -> do
        choice
          [ (c `isCon` primAgdaClauseClause, R.Clause <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "clause" t

-- Unquoting TCM computations ---------------------------------------------

-- | Argument should be a term of type @Term → TCM A@ for some A. Returns the
--   resulting term of type @A@. The second argument is the term for the hole,
--   which will typically be a metavariable. This is passed to the computation
--   (quoted).
unquoteTCM :: I.Term -> I.Term -> UnquoteM I.Term
unquoteTCM m hole = do
  qhole <- liftTCM $ quoteTerm hole
  evalTCM (m `apply` [defaultArg qhole])

evalTCM :: I.Term -> UnquoteM I.Term
evalTCM v = do
  v <- reduceQuotedTerm v
  liftTCM $ reportSDoc "tc.unquote.eval" 90 $ "evalTCM" <+> prettyTCM v
  let failEval = throwError $ NonCanonical "type checking computation" v

  case v of
    I.Def f [] ->
      choice [ (f `isDef` primAgdaTCMGetContext, tcGetContext)
             , (f `isDef` primAgdaTCMCommit,     tcCommit) ]
             failEval
    I.Def f [u] ->
      choice [ (f `isDef` primAgdaTCMInferType,          tcFun1 tcInferType          u)
             , (f `isDef` primAgdaTCMNormalise,          tcFun1 tcNormalise          u)
             , (f `isDef` primAgdaTCMReduce,             tcFun1 tcReduce             u)
             , (f `isDef` primAgdaTCMGetType,            tcFun1 tcGetType            u)
             , (f `isDef` primAgdaTCMGetDefinition,      tcFun1 tcGetDefinition      u)
             , (f `isDef` primAgdaTCMIsMacro,            tcFun1 tcIsMacro            u)
             , (f `isDef` primAgdaTCMFreshName,          tcFun1 tcFreshName          u) ]
             failEval
    I.Def f [u, v] ->
      choice [ (f `isDef` primAgdaTCMUnify,      tcFun2 tcUnify      u v)
             , (f `isDef` primAgdaTCMCheckType,  tcFun2 tcCheckType  u v)
             , (f `isDef` primAgdaTCMDeclareDef, uqFun2 tcDeclareDef u v)
             , (f `isDef` primAgdaTCMDeclarePostulate, uqFun2 tcDeclarePostulate u v)
             , (f `isDef` primAgdaTCMDefineFun,  uqFun2 tcDefineFun  u v) ]
             failEval
    I.Def f [l, a, u] ->
      choice [ (f `isDef` primAgdaTCMReturn,      return (unElim u))
             , (f `isDef` primAgdaTCMTypeError,   tcFun1 tcTypeError   u)
             , (f `isDef` primAgdaTCMQuoteTerm,   tcQuoteTerm (unElim u))
             , (f `isDef` primAgdaTCMUnquoteTerm, tcFun1 (tcUnquoteTerm (mkT (unElim l) (unElim a))) u)
             , (f `isDef` primAgdaTCMBlockOnMeta, uqFun1 tcBlockOnMeta u)
             , (f `isDef` primAgdaTCMDebugPrint,  tcFun3 tcDebugPrint l a u)
             , (f `isDef` primAgdaTCMNoConstraints, tcNoConstraints (unElim u))
             ]
             failEval
    I.Def f [_, _, u, v] ->
      choice [ (f `isDef` primAgdaTCMCatchError,    tcCatchError    (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMWithNormalisation, tcWithNormalisation (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMExtendContext, tcExtendContext (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMInContext,     tcInContext     (unElim u) (unElim v)) ]
             failEval
    I.Def f [_, _, _, _, m, k] ->
      choice [ (f `isDef` primAgdaTCMBind, tcBind (unElim m) (unElim k)) ]
             failEval
    _ -> failEval
  where
    unElim = unArg . fromMaybe __IMPOSSIBLE__ . isApplyElim
    tcBind m k = do v <- evalTCM m
                    evalTCM (k `apply` [defaultArg v])

    process :: (InstantiateFull a, Normalise a) => a -> TCM a
    process v = do
      norm <- viewTC eUnquoteNormalise
      if norm then normalise v else instantiateFull v

    mkT l a = El s a
      where s = Type $ Max [Plus 0 $ UnreducedLevel l]

    -- Don't catch Unquote errors!
    tcCatchError :: Term -> Term -> UnquoteM Term
    tcCatchError m h =
      liftU2 (\ m1 m2 -> m1 `catchError` \ _ -> m2) (evalTCM m) (evalTCM h)

    tcWithNormalisation :: Term -> Term -> UnquoteM Term
    tcWithNormalisation b m = do
      v <- unquote b
      liftU1 (locallyTC eUnquoteNormalise $ const v) (evalTCM m)

    uqFun1 :: Unquote a => (a -> UnquoteM b) -> Elim -> UnquoteM b
    uqFun1 fun a = do
      a <- unquote (unElim a)
      fun a

    tcFun1 :: Unquote a => (a -> TCM b) -> Elim -> UnquoteM b
    tcFun1 fun = uqFun1 (liftTCM . fun)

    uqFun2 :: (Unquote a, Unquote b) => (a -> b -> UnquoteM c) -> Elim -> Elim -> UnquoteM c
    uqFun2 fun a b = do
      a <- unquote (unElim a)
      b <- unquote (unElim b)
      fun a b

    uqFun3 :: (Unquote a, Unquote b, Unquote c) => (a -> b -> c -> UnquoteM d) -> Elim -> Elim -> Elim -> UnquoteM d
    uqFun3 fun a b c = do
      a <- unquote (unElim a)
      b <- unquote (unElim b)
      c <- unquote (unElim c)
      fun a b c

    tcFun2 :: (Unquote a, Unquote b) => (a -> b -> TCM c) -> Elim -> Elim -> UnquoteM c
    tcFun2 fun = uqFun2 (\ x y -> liftTCM (fun x y))

    tcFun3 :: (Unquote a, Unquote b, Unquote c) => (a -> b -> c -> TCM d) -> Elim -> Elim -> Elim -> UnquoteM d
    tcFun3 fun = uqFun3 (\ x y z -> liftTCM (fun x y z))

    tcFreshName :: Str -> TCM Term
    tcFreshName s = do
      m <- currentModule
      quoteName . qualify m <$> freshName_ (unStr s)

    tcUnify :: R.Term -> R.Term -> TCM Term
    tcUnify u v = do
      (u, a) <- inferExpr        =<< toAbstract_ u
      v      <- flip checkExpr a =<< toAbstract_ v
      equalTerm a u v
      primUnitUnit

    tcBlockOnMeta :: MetaId -> UnquoteM Term
    tcBlockOnMeta x = do
      s <- gets snd
      throwError (BlockedOnMeta s x)

    tcCommit :: UnquoteM Term
    tcCommit = do
      dirty <- gets fst
      when (dirty == Dirty) $
        typeError $ GenericError "Cannot use commitTC after declaring new definitions."
      s <- getTC
      modify (second $ const s)
      liftTCM primUnitUnit

    tcTypeError :: [ErrorPart] -> TCM a
    tcTypeError err = typeError . GenericDocError =<< fsep (map prettyTCM err)

    tcDebugPrint :: Str -> Integer -> [ErrorPart] -> TCM Term
    tcDebugPrint (Str s) n msg = do
      reportSDoc s (fromIntegral n) $ fsep (map prettyTCM msg)
      primUnitUnit

    tcNoConstraints :: Term -> UnquoteM Term
    tcNoConstraints m = liftU1 noConstraints (evalTCM m)

    tcInferType :: R.Term -> TCM Term
    tcInferType v = do
      (_, a) <- inferExpr =<< toAbstract_ v
      quoteType =<< process a

    tcCheckType :: R.Term -> R.Type -> TCM Term
    tcCheckType v a = do
      a <- isType_ =<< toAbstract_ a
      e <- toAbstract_ v
      v <- checkExpr e a
      quoteTerm =<< process v

    tcQuoteTerm :: Term -> UnquoteM Term
    tcQuoteTerm v = liftTCM $ quoteTerm =<< process v

    tcUnquoteTerm :: Type -> R.Term -> TCM Term
    tcUnquoteTerm a v = do
      e <- toAbstract_ v
      v <- checkExpr e a
      return v

    tcNormalise :: R.Term -> TCM Term
    tcNormalise v = do
      (v, _) <- inferExpr =<< toAbstract_ v
      quoteTerm =<< normalise v

    tcReduce :: R.Term -> TCM Term
    tcReduce v = do
      (v, _) <- inferExpr =<< toAbstract_ v
      quoteTerm =<< reduce =<< instantiateFull v

    tcGetContext :: UnquoteM Term
    tcGetContext = liftTCM $ do
      as <- map (fmap snd) <$> getContext
      as <- etaContract =<< process as
      buildList <*> mapM quoteDom as

    extendCxt :: Arg R.Type -> UnquoteM a -> UnquoteM a
    extendCxt a m = do
      a <- liftTCM $ traverse (isType_ <=< toAbstract_) a
      liftU1 (addContext (domFromArg a :: Dom Type)) m

    tcExtendContext :: Term -> Term -> UnquoteM Term
    tcExtendContext a m = do
      a <- unquote a
      extendCxt a (evalTCM m)

    tcInContext :: Term -> Term -> UnquoteM Term
    tcInContext c m = do
      c <- unquote c
      liftU1 inTopContext $ go c (evalTCM m)
      where
        go :: [Arg R.Type] -> UnquoteM Term -> UnquoteM Term
        go []       m = m
        go (a : as) m = go as (extendCxt a m)

    constInfo :: QName -> TCM Definition
    constInfo x = either err return =<< getConstInfo' x
      where err _ = genericError $ "Unbound name: " ++ prettyShow x

    tcGetType :: QName -> TCM Term
    tcGetType x = quoteType . defType =<< constInfo x

    tcIsMacro :: QName -> TCM Term
    tcIsMacro x = do
      true  <- primTrue
      false <- primFalse
      let qBool True  = true
          qBool False = false
      qBool . isMacro . theDef <$> constInfo x

    tcGetDefinition :: QName -> TCM Term
    tcGetDefinition x = quoteDefn =<< constInfo x

    setDirty :: UnquoteM ()
    setDirty = modify (first $ const Dirty)

    tcDeclareDef :: Arg QName -> R.Type -> UnquoteM Term
    tcDeclareDef (Arg i x) a = inOriginalContext $ do
      setDirty
      let r = getRelevance i
      when (hidden i) $ liftTCM $ typeError . GenericDocError =<<
        "Cannot declare hidden function" <+> prettyTCM x
      tell [x]
      liftTCM $ do
        reportSDoc "tc.unquote.decl" 10 $ sep
          [ "declare" <+> prettyTCM x <+> ":"
          , nest 2 $ prettyTCM a
          ]
        a <- isType_ =<< toAbstract_ a
        alreadyDefined <- isRight <$> getConstInfo' x
        when alreadyDefined $ genericError $ "Multiple declarations of " ++ prettyShow x
        addConstant x $ defaultDefn i x a emptyFunction
        when (isInstance i) $ addTypedInstance x a
        primUnitUnit

    tcDeclarePostulate :: Arg QName -> R.Type -> UnquoteM Term
    tcDeclarePostulate (Arg i x) a = inOriginalContext $ do
      clo <- commandLineOptions
      when (Lens.getSafeMode clo) $ liftTCM $ typeError . GenericDocError =<<
        "Cannot postulate '" <+> prettyTCM x <+> ":" <+> prettyTCM a <+> "' with safe flag"
      setDirty
      let r = getRelevance i
      when (hidden i) $ liftTCM $ typeError . GenericDocError =<<
        "Cannot declare hidden function" <+> prettyTCM x
      tell [x]
      liftTCM $ do
        reportSDoc "tc.unquote.decl" 10 $ sep
          [ "declare Postulate" <+> prettyTCM x <+> ":"
          , nest 2 $ prettyTCM a
          ]
        a <- isType_ =<< toAbstract_ a
        alreadyDefined <- isRight <$> getConstInfo' x
        when alreadyDefined $ genericError $ "Multiple declarations of " ++ prettyShow x
        addConstant x $ defaultDefn i x a Axiom
        when (isInstance i) $ addTypedInstance x a
        primUnitUnit

    tcDefineFun :: QName -> [R.Clause] -> UnquoteM Term
    tcDefineFun x cs = inOriginalContext $ (setDirty >>) $ liftTCM $ do
      whenM (isLeft <$> getConstInfo' x) $
        genericError $ "Missing declaration for " ++ prettyShow x
      cs <- mapM (toAbstract_ . QNamed x) cs
      reportSDoc "tc.unquote.def" 10 $ vcat $ map prettyA cs
      let i = mkDefInfo (nameConcrete $ qnameName x) noFixity' PublicAccess ConcreteDef noRange
      checkFunDef NotDelayed i x cs
      primUnitUnit
