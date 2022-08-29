
module Agda.TypeChecking.Unquote where

import Control.Arrow          ( first, second, (&&&) )
import Control.Monad          ( (<=<), liftM2 )
import Control.Monad.Except   ( MonadError(..), ExceptT(..), runExceptT )
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.Reader   ( ReaderT(..), runReaderT )
import Control.Monad.State    ( gets, modify, StateT(..), runStateT )
import Control.Monad.Writer   ( MonadWriter(..), WriterT(..), runWriterT )
import Control.Monad.Trans    ( lift )

import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word

import System.Directory (doesFileExist, getPermissions, executable)
import System.Process ( readProcessWithExitCode )
import System.Exit ( ExitCode(..) )

import Agda.Syntax.Common hiding ( Nat )
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Reflected as R
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Translation.ReflectedToAbstract
import Agda.Syntax.Scope.Base (KindOfName(ConName, DataName))

import Agda.Interaction.Library ( ExeName )
import Agda.Interaction.Options ( optTrustedExecutables, optAllowExec )

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance ( workOnTypes )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.ReconstructParameters
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.InstanceArguments ( getInstanceCandidates )

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term
import {-# SOURCE #-} Agda.TypeChecking.Rules.Def
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl
import Agda.TypeChecking.Rules.Data

import Agda.Utils.Either
import Agda.Utils.Lens
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Interaction.Options.Lenses as Lens

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
packUnquoteM f = ReaderT $ \ cxt -> StateT $ \ s -> WriterT $ ExceptT $ f cxt s

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
    unsafeModifyContext (const cxt) $ unpackUnquoteM m cxt s

isCon :: ConHead -> TCM Term -> UnquoteM Bool
isCon con tm = do t <- liftTCM tm
                  case t of
                    Con con' _ _ -> return (con == con')
                    _ -> return False

isDef :: QName -> TCM Term -> UnquoteM Bool
isDef f tm = loop <$> liftTCM tm
  where
    loop (Def g _) = f == g
    loop (Lam _ b) = loop $ unAbs b
    loop _         = False

reduceQuotedTerm :: Term -> UnquoteM Term
reduceQuotedTerm t = locallyReduceAllDefs $ do
  ifBlocked t {-then-} (\ m _ -> do s <- gets snd; throwError $ BlockedOnMeta s m)
              {-else-} (\ _ t -> return t)

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
  i <- either (const defaultAxiom) theDef <$> getConstInfo' x  -- for recursive unquoteDecl
  case i of
    Constructor{} -> do
      def <- liftTCM $ prettyTCM =<< primAgdaTermDef
      con <- liftTCM $ prettyTCM =<< primAgdaTermCon
      throwError $ ConInsteadOfDef x (show def) (show con)
    _ -> return x

ensureCon :: QName -> UnquoteM QName
ensureCon x = do
  i <- either (const defaultAxiom) theDef <$> getConstInfo' x  -- for recursive unquoteDecl
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
    R.Def d _
      | c : cs  <- prettyShow (qnameName d),
        Just lc <- reallyToLower c,
        not (null cs) || isUpper c -> [lc]
    _        -> "_"
  where
    -- Heuristic (see #5048 for some discussion):
    -- If first character can be `toLower`ed use that, unless the name has only one character and is
    -- already lower case. (to avoid using the same name for the type and the bound variable).
    reallyToLower c
      | toUpper lc /= lc = Just lc
      | otherwise        = Nothing
      where lc = toLower c

-- TODO: reflect Cohesion
instance Unquote Modality where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [r,q] <- allApplyElims es ->
        choice
          [(c `isCon` primModalityConstructor,
              Modality <$> unquoteN r
                       <*> unquoteN q
                       <*> pure defaultCohesion)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "modality" t

instance Unquote ArgInfo where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [h,m] <- allApplyElims es ->
        choice
          [(c `isCon` primArgArgInfo,
              ArgInfo <$> unquoteN h
                      <*> unquoteN m
                      <*> pure Reflected
                      <*> pure unknownFreeVariables
                      <*> pure defaultAnnotation)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "arg info" t

instance Unquote a => Unquote (Arg a) where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [info,x] <- allApplyElims es ->
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
      Lit (LitNat n) -> return n
      _ -> throwError $ NonCanonical "integer" t

instance Unquote Word64 where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitWord64 n) -> return n
      _ -> throwError $ NonCanonical "word64" t

instance Unquote Double where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitFloat x) -> return x
      _ -> throwError $ NonCanonical "float" t

instance Unquote Char where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitChar x) -> return x
      _ -> throwError $ NonCanonical "char" t

instance Unquote Text where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitString x) -> return x
      _ -> throwError $ NonCanonical "string" t

unquoteString :: Term -> UnquoteM String
unquoteString x = T.unpack <$> unquote x

unquoteNString :: Arg Term -> UnquoteM Text
unquoteNString = unquoteN

data ErrorPart = StrPart String | TermPart A.Expr | PattPart A.Pattern | NamePart QName

instance PrettyTCM ErrorPart where
  prettyTCM (StrPart s)  = text s
  prettyTCM (TermPart t) = prettyTCM t
  prettyTCM (PattPart p) = prettyTCM p
  prettyTCM (NamePart x) = prettyTCM x

-- | We do a little bit of work here to make it possible to generate nice
--   layout for multi-line error messages. Specifically we split the parts
--   into lines (indicated by \n in a string part) and vcat all the lines.
prettyErrorParts :: [ErrorPart] -> TCM Doc
prettyErrorParts = vcat . map (hcat . map prettyTCM) . splitLines
  where
    splitLines [] = []
    splitLines (StrPart s : ss) =
      case break (=='\n') s of
        (s0, '\n' : s1) -> [StrPart s0] : splitLines (StrPart s1 : ss)
        (s0, "")        -> consLine (StrPart s0) (splitLines ss)
        _               -> __IMPOSSIBLE__
    splitLines (p@TermPart{} : ss) = consLine p (splitLines ss)
    splitLines (p@PattPart{} : ss) = consLine p (splitLines ss)
    splitLines (p@NamePart{} : ss) = consLine p (splitLines ss)

    consLine l []        = [[l]]
    consLine l (l' : ls) = (l : l') : ls


instance Unquote ErrorPart where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x] <- allApplyElims es ->
        choice [ (c `isCon` primAgdaErrorPartString, StrPart . T.unpack <$> unquoteNString x)
               , (c `isCon` primAgdaErrorPartTerm,   TermPart <$> ((liftTCM . toAbstractWithoutImplicit) =<< (unquoteN x :: UnquoteM R.Term)))
               , (c `isCon` primAgdaErrorPartPatt,   PattPart <$> ((liftTCM . toAbstractWithoutImplicit) =<< (unquoteN x :: UnquoteM R.Pattern)))
               , (c `isCon` primAgdaErrorPartName,   NamePart <$> unquoteN x) ]
               __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "error part" t

instance Unquote a => Unquote [a] where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x,xs] <- allApplyElims es ->
        choice
          [(c `isCon` primCons, (:) <$> unquoteN x <*> unquoteN xs)]
          __IMPOSSIBLE__
      Con c _ [] ->
        choice
          [(c `isCon` primNil, return [])]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "list" t

instance (Unquote a, Unquote b) => Unquote (a, b) where
  unquote t = do
    t <- reduceQuotedTerm t
    SigmaKit{..} <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
    case t of
      Con c _ es | Just [x,y] <- allApplyElims es ->
        choice
          [(pure (c == sigmaCon), (,) <$> unquoteN x <*> unquoteN y)]
          __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "pair" t

instance Unquote Hiding where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] ->
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
      Con c _ [] ->
        choice
          [(c `isCon` primRelevant,   return Relevant)
          ,(c `isCon` primIrrelevant, return Irrelevant)]
          __IMPOSSIBLE__
      Con c _ vs -> __IMPOSSIBLE__
      _        -> throwError $ NonCanonical "relevance" t

instance Unquote Quantity where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] ->
        choice
          [(c `isCon` primQuantityω, return $ Quantityω QωInferred)
          ,(c `isCon` primQuantity0, return $ Quantity0 Q0Inferred)]
          __IMPOSSIBLE__
      Con c _ vs -> __IMPOSSIBLE__
      _        -> throwError $ NonCanonical "quantity" t

instance Unquote QName where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitQName x) -> return x
      _ -> throwError $ NonCanonical "name" t

instance Unquote a => Unquote (R.Abs a) where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x,y] <- allApplyElims es ->
        choice
          [(c `isCon` primAbsAbs, R.Abs <$> (hint . T.unpack <$> unquoteNString x) <*> unquoteN y)]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "abstraction" t

    where hint x | not (null x) = x
                 | otherwise    = "_"

instance Unquote MetaId where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Lit (LitMeta f x) -> liftTCM $ do
        live <- (f ==) <$> getCurrentPath
        unless live $ do
            m <- fromMaybe __IMPOSSIBLE__ <$> lookupModuleFromSource f
            typeError . GenericDocError =<<
              sep [ "Can't unquote stale metavariable"
                  , pretty m <> "._" <> pretty (metaId x) ]
        return x
      _ -> throwError $ NonCanonical "meta variable" t

instance Unquote a => Unquote (Dom a) where
  unquote t = domFromArg <$> unquote t

instance Unquote R.Sort where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ [] ->
        choice
          [(c `isCon` primAgdaSortUnsupported, return R.UnknownS)]
          __IMPOSSIBLE__
      Con c _ es | Just [u] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaSortSet, R.SetS <$> unquoteN u)
          , (c `isCon` primAgdaSortLit, R.LitS <$> unquoteN u)
          , (c `isCon` primAgdaSortProp, R.PropS <$> unquoteN u)
          , (c `isCon` primAgdaSortPropLit, R.PropLitS <$> unquoteN u)
          , (c `isCon` primAgdaSortInf, R.InfS <$> unquoteN u)
          ]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "sort" t

instance Unquote Literal where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaLitNat,    LitNat    <$> unquoteN x)
          , (c `isCon` primAgdaLitFloat,  LitFloat  <$> unquoteN x)
          , (c `isCon` primAgdaLitChar,   LitChar   <$> unquoteN x)
          , (c `isCon` primAgdaLitString, LitString <$> unquoteNString x)
          , (c `isCon` primAgdaLitQName,  LitQName  <$> unquoteN x)
          , (c `isCon` primAgdaLitMeta,   LitMeta   <$> getCurrentPath <*> unquoteN x) ]
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

      Con c _ es | Just [x] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaTermSort,      R.Sort      <$> unquoteN x)
          , (c `isCon` primAgdaTermLit,       R.Lit       <$> unquoteN x)
          ]
          __IMPOSSIBLE__

      Con c _ es | Just [x, y] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaTermVar,     R.Var     <$> (fromInteger <$> unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermCon,     R.Con     <$> (ensureCon =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermDef,     R.Def     <$> (ensureDef =<< unquoteN x) <*> unquoteN y)
          , (c `isCon` primAgdaTermMeta,    R.Meta    <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermLam,     R.Lam     <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermPi,      mkPi      <$> unquoteN x <*> unquoteN y)
          , (c `isCon` primAgdaTermExtLam,  R.ExtLam  <$> (List1.fromList __IMPOSSIBLE__ <$> unquoteN x) <*> unquoteN y)
          ]
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
      Con c _ es | Just [x] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaPatVar,    R.VarP    . fromInteger <$> unquoteN x)
          , (c `isCon` primAgdaPatAbsurd, R.AbsurdP . fromInteger <$> unquoteN x)
          , (c `isCon` primAgdaPatDot,    R.DotP  <$> unquoteN x)
          , (c `isCon` primAgdaPatProj,   R.ProjP <$> unquoteN x)
          , (c `isCon` primAgdaPatLit,    R.LitP  <$> unquoteN x) ]
          __IMPOSSIBLE__
      Con c _ es | Just [x, y] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaPatCon, R.ConP <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ _ -> __IMPOSSIBLE__
      _ -> throwError $ NonCanonical "pattern" t

instance Unquote R.Clause where
  unquote t = do
    t <- reduceQuotedTerm t
    case t of
      Con c _ es | Just [x, y] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaClauseAbsurd, R.AbsurdClause <$> unquoteN x <*> unquoteN y) ]
          __IMPOSSIBLE__
      Con c _ es | Just [x, y, z] <- allApplyElims es ->
        choice
          [ (c `isCon` primAgdaClauseClause, R.Clause <$> unquoteN x <*> unquoteN y <*> unquoteN z) ]
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
      choice [ (f `isDef` primAgdaTCMGetContext,       tcGetContext)
             , (f `isDef` primAgdaTCMCommit,           tcCommit)
             ]
             failEval
    I.Def f [u] ->
      choice [ (f `isDef` primAgdaTCMInferType,                  tcFun1 tcInferType                  u)
             , (f `isDef` primAgdaTCMNormalise,                  tcFun1 tcNormalise                  u)
             , (f `isDef` primAgdaTCMReduce,                     tcFun1 tcReduce                     u)
             , (f `isDef` primAgdaTCMGetType,                    tcFun1 tcGetType                    u)
             , (f `isDef` primAgdaTCMGetDefinition,              tcFun1 tcGetDefinition              u)
             , (f `isDef` primAgdaTCMFormatErrorParts,           tcFun1 tcFormatErrorParts           u)
             , (f `isDef` primAgdaTCMIsMacro,                    tcFun1 tcIsMacro                    u)
             , (f `isDef` primAgdaTCMFreshName,                  tcFun1 tcFreshName                  u)
             , (f `isDef` primAgdaTCMGetInstances,               uqFun1 tcGetInstances               u)
             ]
             failEval
    I.Def f [u, v] ->
      choice [ (f `isDef` primAgdaTCMUnify,      tcFun2 tcUnify      u v)
             , (f `isDef` primAgdaTCMCheckType,  tcFun2 tcCheckType  u v)
             , (f `isDef` primAgdaTCMDeclareDef, uqFun2 tcDeclareDef u v)
             , (f `isDef` primAgdaTCMDeclarePostulate, uqFun2 tcDeclarePostulate u v)
             , (f `isDef` primAgdaTCMDefineData, uqFun2 tcDefineData u v)
             , (f `isDef` primAgdaTCMDefineFun,  uqFun2 tcDefineFun  u v)
             , (f `isDef` primAgdaTCMQuoteOmegaTerm, tcQuoteTerm (sort $ Inf IsFibrant 0) (unElim v))
             ]
             failEval
    I.Def f [l, a, u] ->
      choice [ (f `isDef` primAgdaTCMReturn,      return (unElim u))
             , (f `isDef` primAgdaTCMTypeError,   tcFun1 tcTypeError   u)
             , (f `isDef` primAgdaTCMQuoteTerm,   tcQuoteTerm (mkT (unElim l) (unElim a)) (unElim u))
             , (f `isDef` primAgdaTCMUnquoteTerm, tcFun1 (tcUnquoteTerm (mkT (unElim l) (unElim a))) u)
             , (f `isDef` primAgdaTCMBlockOnMeta, uqFun1 tcBlockOnMeta u)
             , (f `isDef` primAgdaTCMDebugPrint,  tcFun3 tcDebugPrint l a u)
             , (f `isDef` primAgdaTCMNoConstraints, tcNoConstraints (unElim u))
             , (f `isDef` primAgdaTCMWithReconsParams, tcWithReconsParams (unElim u))
             , (f `isDef` primAgdaTCMDeclareData, uqFun3 tcDeclareData l a u)
             , (f `isDef` primAgdaTCMRunSpeculative, tcRunSpeculative (unElim u))
             , (f `isDef` primAgdaTCMExec, tcFun3 tcExec l a u)
             ]
             failEval
    I.Def f [_, _, u, v] ->
      choice [ (f `isDef` primAgdaTCMCatchError,    tcCatchError    (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMWithNormalisation, tcWithNormalisation (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMInContext,     tcInContext     (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMOnlyReduceDefs, tcOnlyReduceDefs (unElim u) (unElim v))
             , (f `isDef` primAgdaTCMDontReduceDefs, tcDontReduceDefs (unElim u) (unElim v))
             ]
             failEval
    I.Def f [_, _, u, v, w] ->
      choice [ (f `isDef` primAgdaTCMExtendContext, tcExtendContext (unElim u) (unElim v) (unElim w))
             ]
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
      where s = Type $ atomicLevel l

    -- Don't catch Unquote errors!
    tcCatchError :: Term -> Term -> UnquoteM Term
    tcCatchError m h =
      liftU2 (\ m1 m2 -> m1 `catchError` \ _ -> m2) (evalTCM m) (evalTCM h)

    tcWithNormalisation :: Term -> Term -> UnquoteM Term
    tcWithNormalisation b m = do
      v <- unquote b
      liftU1 (locallyTC eUnquoteNormalise $ const v) (evalTCM m)

    tcOnlyReduceDefs = tcDoReduceDefs OnlyReduceDefs
    tcDontReduceDefs = tcDoReduceDefs DontReduceDefs

    tcWithReconsParams :: Term -> UnquoteM Term
    tcWithReconsParams m = liftU1 locallyReconstructed $ evalTCM m

    tcDoReduceDefs :: (Set QName -> ReduceDefs) -> Term -> Term -> UnquoteM Term
    tcDoReduceDefs reduceDefs v m = do
      qs <- unquote v
      let defs = reduceDefs $ Set.fromList qs
      liftU1 (locallyTC eReduceDefs (<> defs)) (evalTCM m)

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

    tcFreshName :: Text -> TCM Term
    tcFreshName s = do
      whenM (viewTC eCurrentlyElaborating) $
        typeError $ GenericError "Not supported: declaring new names from an edit-time macro"
      m <- currentModule
      quoteName . qualify m <$> freshName_ (T.unpack s)

    tcUnify :: R.Term -> R.Term -> TCM Term
    tcUnify u v = do
      (u, a) <- locallyReduceAllDefs $ inferExpr        =<< toAbstract_ u
      v      <- locallyReduceAllDefs $ flip checkExpr a =<< toAbstract_ v
      equalTerm a u v
      primUnitUnit

    tcBlockOnMeta :: MetaId -> UnquoteM Term
    tcBlockOnMeta x = do
      s <- gets snd
      throwError (BlockedOnMeta s $ unblockOnMeta x)

    tcCommit :: UnquoteM Term
    tcCommit = do
      dirty <- gets fst
      when (dirty == Dirty) $
        liftTCM $ typeError $ GenericError "Cannot use commitTC after declaring new definitions."
      s <- getTC
      modify (second $ const s)
      liftTCM primUnitUnit

    tcFormatErrorParts :: [ErrorPart] -> TCM Term
    tcFormatErrorParts msg = quoteString . prettyShow <$> prettyErrorParts msg

    tcTypeError :: [ErrorPart] -> TCM a
    tcTypeError err = typeError . GenericDocError =<< prettyErrorParts err

    tcDebugPrint :: Text -> Integer -> [ErrorPart] -> TCM Term
    tcDebugPrint s n msg = do
      reportSDoc (T.unpack s) (fromIntegral n) $ prettyErrorParts msg
      primUnitUnit

    tcNoConstraints :: Term -> UnquoteM Term
    tcNoConstraints m = liftU1 noConstraints (evalTCM m)

    tcInferType :: R.Term -> TCM Term
    tcInferType v = do
      r <- isReconstructed
      (_, a) <- inferExpr =<< toAbstract_ v
      if r then do
        a <- process a
        a <- locallyReduceAllDefs $ reconstructParametersInType a
        reportSDoc "tc.reconstruct" 50 $ "Infer after reconstruct:"
          <+> pretty a
        locallyReconstructed (quoteType a)
      else
        quoteType =<< process a

    tcCheckType :: R.Term -> R.Type -> TCM Term
    tcCheckType v a = do
      r <- isReconstructed
      a <- workOnTypes $ locallyReduceAllDefs $ isType_ =<< toAbstract_ a
      e <- toAbstract_ v
      v <- checkExpr e a
      if r then do
        v <- process v
        v <- locallyReduceAllDefs $ reconstructParameters a v
        locallyReconstructed (quoteTerm v)
      else
        quoteTerm =<< process v

    tcQuoteTerm :: Type -> Term -> UnquoteM Term
    tcQuoteTerm a v = liftTCM $ do
      r <- isReconstructed
      if r then do
        v <- process v
        v <- locallyReduceAllDefs $ reconstructParameters a v
        locallyReconstructed (quoteTerm v)
      else
        quoteTerm =<< process v

    tcUnquoteTerm :: Type -> R.Term -> TCM Term
    tcUnquoteTerm a v = do
      e <- toAbstract_ v
      checkExpr e a

    tcNormalise :: R.Term -> TCM Term
    tcNormalise v = do
      r <- isReconstructed
      (v, t) <- locallyReduceAllDefs $ inferExpr  =<< toAbstract_ v
      if r then do
        v <- normalise v
        t <- normalise t
        v <- locallyReduceAllDefs $ reconstructParameters' defaultAction t v
        reportSDoc "tc.reconstruct" 50 $ "Normalise reconstruct:" <+> pretty v
        locallyReconstructed $ quoteTerm v
      else
       quoteTerm =<< normalise v

    tcReduce :: R.Term -> TCM Term
    tcReduce v = do
      r <- isReconstructed
      (v, t) <- locallyReduceAllDefs $ inferExpr =<< toAbstract_ v
      if r then do
        v <- reduce =<< instantiateFull v
        t <- reduce =<< instantiateFull t
        v <- locallyReduceAllDefs $ reconstructParameters' defaultAction t v
        reportSDoc "tc.reconstruct" 50 $ "Reduce reconstruct:" <+> pretty v
        locallyReconstructed $ quoteTerm v
      else
        quoteTerm =<< reduce =<< instantiateFull v

    tcGetContext :: UnquoteM Term
    tcGetContext = liftTCM $ do
      r <- isReconstructed
      as <- map (nameToArgName . fst . unDom &&& fmap snd) <$> getContext
      as <- etaContract =<< process as
      if r then do
        as <- recons (reverse as)
        let as' = reverse as
        locallyReconstructed $ buildList <*> mapM quoteDomWithName as'
      else
        buildList <*> mapM quoteDomWithName as
      where
        recons :: [(ArgName, Dom Type)] -> TCM [(ArgName, Dom Type)]
        recons []                        = return []
        recons ((s, d@Dom {unDom=t}):ds) = do
          t <- locallyReduceAllDefs $ reconstructParametersInType t
          let d' = d{unDom=t}
          ds' <- addContext (s, d') $ recons ds
          return $ (s, d'):ds'

        quoteDomWithName :: (ArgName, Dom Type) -> TCM Term
        quoteDomWithName (x, t) = toTerm <*> pure (T.pack x, t)

    extendCxt :: Text -> Arg R.Type -> UnquoteM a -> UnquoteM a
    extendCxt s a m = do
      a <- workOnTypes $ locallyReduceAllDefs $ liftTCM $ traverse (isType_ <=< toAbstract_) a
      liftU1 (addContext (s, domFromArg a :: Dom Type)) m

    tcExtendContext :: Term -> Term -> Term -> UnquoteM Term
    tcExtendContext s a m = do
      s <- unquote s
      a <- unquote a
      fmap (strengthen impossible) $ extendCxt s a $ do
        v <- evalTCM $ raise 1 m
        when (freeIn 0 v) $ liftTCM $ genericDocError =<<
          hcat ["Local variable '", prettyTCM (var 0), "' escaping in result of extendContext:"]
            <?> prettyTCM v
        return v

    tcInContext :: Term -> Term -> UnquoteM Term
    tcInContext c m = do
      c <- unquote c
      liftU1 unsafeInTopContext $ go c (evalTCM m)
      where
        go :: [(Text , Arg R.Type)] -> UnquoteM Term -> UnquoteM Term
        go []             m = m
        go ((s , a) : as) m = go as (extendCxt s a m)

    constInfo :: QName -> TCM Definition
    constInfo x = either err return =<< getConstInfo' x
      where err _ = genericError $ "Unbound name: " ++ prettyShow x

    tcGetType :: QName -> TCM Term
    tcGetType x = do
      r  <- isReconstructed
      ci <- constInfo x
      let t = defType ci
      if r then do
        t <- locallyReduceAllDefs $ reconstructParametersInType t
        quoteType t
      else
        quoteType t


    tcIsMacro :: QName -> TCM Term
    tcIsMacro x = do
      true  <- primTrue
      false <- primFalse
      let qBool True  = true
          qBool False = false
      qBool . isMacro . theDef <$> constInfo x

    tcGetDefinition :: QName -> TCM Term
    tcGetDefinition x = do
      r <- isReconstructed
      if r then
        tcGetDefinitionRecons x
      else
        quoteDefn =<< constInfo x

    tcGetDefinitionRecons :: QName -> TCM Term
    tcGetDefinitionRecons x = do
      ci@(Defn {theDef=d}) <- constInfo x
      case d of
        f@(Function {funClauses=cs}) -> do
          cs' <- mapM reconsClause cs
          locallyReconstructed $ quoteDefn ci{theDef=f{funClauses=cs'}}

        _ -> quoteDefn ci

      where
        reconsClause :: Clause -> TCM Clause
        reconsClause c = do
          tel' <- reconsTel $ clauseTel c
          b' <- case (clauseType c, clauseBody c) of
                (Just t, Just b) ->
                  addContext (clauseTel c) $ do
                     bb <- locallyReduceAllDefs
                           $ reconstructParameters' defaultAction (unArg t) b
                     return $ Just bb
                _ -> return $ clauseBody c
          let c' = c{clauseBody=b', clauseTel=tel'}
          reportSDoc "tc.reconstruct" 50
                   $ "getDefinition reconstructed clause:" <+> pretty c'
          return c'

        reconsTel :: Telescope -> TCM Telescope
        reconsTel EmptyTel = return EmptyTel
        reconsTel (ExtendTel _ NoAbs{}) = __IMPOSSIBLE__
        reconsTel (ExtendTel (d@Dom{unDom=t}) ds@Abs{unAbs=ts}) = do
           t <- locallyReduceAllDefs $ reconstructParametersInType t
           let d' = d{unDom=t}
           ts' <- addContext d' $ reconsTel ts
           return $ ExtendTel d' ds{unAbs=ts'}


    setDirty :: UnquoteM ()
    setDirty = modify (first $ const Dirty)

    tcDeclareDef :: Arg QName -> R.Type -> UnquoteM Term
    tcDeclareDef (Arg i x) a = inOriginalContext $ do
      setDirty
      when (hidden i) $ liftTCM $ typeError . GenericDocError =<<
        "Cannot declare hidden function" <+> prettyTCM x
      tell [x]
      liftTCM $ do
        reportSDoc "tc.unquote.decl" 10 $ sep
          [ "declare" <+> prettyTCM x <+> ":"
          , nest 2 $ prettyR a
          ]
        a <- locallyReduceAllDefs $ isType_ =<< toAbstract_ a
        alreadyDefined <- isRight <$> getConstInfo' x
        when alreadyDefined $ genericError $ "Multiple declarations of " ++ prettyShow x
        addConstant' x i x a emptyFunction
        when (isInstance i) $ addTypedInstance x a
        primUnitUnit

    tcDeclarePostulate :: Arg QName -> R.Type -> UnquoteM Term
    tcDeclarePostulate (Arg i x) a = inOriginalContext $ do
      clo <- commandLineOptions
      when (Lens.getSafeMode clo) $ liftTCM $ typeError . GenericDocError =<<
        "Cannot postulate '" <+> prettyTCM x <+> ":" <+> prettyR a <+> "' with safe flag"
      setDirty
      when (hidden i) $ liftTCM $ typeError . GenericDocError =<<
        "Cannot declare hidden function" <+> prettyTCM x
      tell [x]
      liftTCM $ do
        reportSDoc "tc.unquote.decl" 10 $ sep
          [ "declare Postulate" <+> prettyTCM x <+> ":"
          , nest 2 $ prettyR a
          ]
        a <- locallyReduceAllDefs $ isType_ =<< toAbstract_ a
        alreadyDefined <- isRight <$> getConstInfo' x
        when alreadyDefined $ genericError $ "Multiple declarations of " ++ prettyShow x
        addConstant' x i x a defaultAxiom
        when (isInstance i) $ addTypedInstance x a
        primUnitUnit

    -- A datatype is expected to be declared with a function type.
    -- The second argument indicates how many preceding types are parameters.
    tcDeclareData :: QName -> Integer -> R.Type -> UnquoteM Term
    tcDeclareData x npars t = inOriginalContext $ do
      setDirty
      tell [x]
      liftTCM $ do
        reportSDoc "tc.unquote.decl" 10 $ sep
          [ "declare Data" <+> prettyTCM x <+> ":"
          , nest 2 $ prettyR t
          ]
        alreadyDefined <- isRight <$> getConstInfo' x
        when alreadyDefined $ genericError $ "Multiple declarations of " ++ prettyShow x
        e <- toAbstract_ t
        -- The type to be checked with @checkSig@ is without parameters.
        let (tel, e') = splitPars (fromInteger npars) e
        ac <- asksTC (^. lensIsAbstract)
        let defIn = mkDefInfo (nameConcrete $ qnameName x) noFixity' PublicAccess ac noRange
        checkSig DataName defIn x (A.GeneralizeTel Map.empty tel) e'
        primUnitUnit

    tcDefineData :: QName -> [(QName, R.Type)] -> UnquoteM Term
    tcDefineData x cs = inOriginalContext $ (setDirty >>) $ liftTCM $ do
      caseEitherM (getConstInfo' x)
        (const $ genericError $ "Missing declaration for " ++ prettyShow x) $ \def -> do
        npars <- case theDef def of
                   DataOrRecSig n -> return n
                   _              -> genericError $ prettyShow x ++
                     " is not declared as a datatype or record, or it already has a definition."

        -- For some reasons, reifying parameters and adding them to the context via
        -- `addContext` before `toAbstract_` is different from substituting the type after
        -- `toAbstract_, so some dummy parameters are added and removed later.
        es <- mapM (toAbstract_ . addDummy npars . snd) cs
        reportSDoc "tc.unquote.def" 10 $ vcat $
          [ "declaring constructors of" <+> prettyTCM x <+> ":" ] ++ map prettyA es

        -- Translate parameters from internal definitions back to abstract syntax.
        t   <- instantiateFull . defType =<< instantiateDef def
        tel <- reify =<< theTel <$> telViewUpTo npars t

        es' <- case mapM (uncurry (substNames' tel) . splitPars npars) es of
                 Nothing -> genericError $ "Number of parameters doesn't match!"
                 Just es -> return es

        ac <- asksTC (^. lensIsAbstract)
        let i = mkDefInfo (nameConcrete $ qnameName x) noFixity' PublicAccess ac noRange
            conNames = map fst cs
            toAxiom c e = A.Axiom ConName i defaultArgInfo Nothing c e
            as = zipWith toAxiom conNames es'
            lams = map (\case {A.TBind _ tac (b :| []) _ -> A.DomainFree tac b
                              ;_ -> __IMPOSSIBLE__ }) tel
        reportSDoc "tc.unquote.def" 10 $ vcat $
          [ "checking datatype: " <+> prettyTCM x <+> " with constructors:"
          , nest 2 (vcat (map prettyTCM conNames))
          ]
        checkDataDef i x YesUniverseCheck (A.DataDefParams Set.empty lams) as
        primUnitUnit
      where
        addDummy :: Int -> R.Type -> R.Type
        addDummy 0 t = t
        addDummy n t = R.Pi (defaultDom (R.Sort $ R.LitS 0)) (R.Abs "dummy" $ addDummy (n - 1) t)

        substNames' :: [A.TypedBinding] -> [A.TypedBinding] -> A.Expr -> Maybe A.Expr
        substNames' (a : as) (b : bs) e = do
          let (A.TBind _ _ (na :| _) expra) = a
              (A.TBind _ _ (nb :| _) exprb) = b
              getName n = A.unBind . A.binderName $ namedArg n
          e' <- substNames' as bs e
          return $ mapExpr (substName (getName na) (getName nb)) e'
          where
            -- Substitute @Var x@ for @Var y@ in an @Expr@.
            substName :: Name -> Name -> (A.Expr -> A.Expr)
            substName x y e@(A.Var n)
                    | y == n    = A.Var x
                    | otherwise = e
            substName _ _ e = e
        substNames' [] [] e = return e
        substNames' _ _ _ = Nothing

    tcDefineFun :: QName -> [R.Clause] -> UnquoteM Term
    tcDefineFun x cs = inOriginalContext $ (setDirty >>) $ liftTCM $ do
      whenM (isLeft <$> getConstInfo' x) $
        genericError $ "Missing declaration for " ++ prettyShow x
      cs <- mapM (toAbstract_ . QNamed x) cs
      reportSDoc "tc.unquote.def" 10 $ vcat $ map prettyA cs
      let accessDontCare = __IMPOSSIBLE__  -- or ConcreteDef, value not looked at
      ac <- asksTC (^. lensIsAbstract)     -- Issue #4012, respect AbstractMode
      let i = mkDefInfo (nameConcrete $ qnameName x) noFixity' accessDontCare ac noRange
      locallyReduceAllDefs $ checkFunDef NotDelayed i x cs
      primUnitUnit

    tcRunSpeculative :: Term -> UnquoteM Term
    tcRunSpeculative mu = do
      oldState <- getTC
      u <- reduce =<< evalTCM mu
      case u of
        Con _ _ [Apply (Arg { unArg = x }), Apply (Arg { unArg = b })] -> do
          unlessM (unquote b) $ putTC oldState
          return x
        _ -> liftTCM $ typeError . GenericDocError =<<
          "Should be a pair: " <+> prettyTCM u

    tcGetInstances :: MetaId -> UnquoteM Term
    tcGetInstances m = liftTCM (getInstanceCandidates m) >>= \case
      Left unblock -> do
        s <- gets snd
        throwError (BlockedOnMeta s unblock)
      Right cands -> liftTCM $
        buildList <*> mapM (quoteTerm . candidateTerm) cands

    splitPars :: Int -> A.Expr -> ([A.TypedBinding], A.Expr)
    splitPars 0 e = ([] , e)
    splitPars npars (A.Pi _ (n :| _) e) = first (n :) (splitPars (npars - 1) e)
    splitPars npars e = __IMPOSSIBLE__
------------------------------------------------------------------------
-- * Trusted executables
------------------------------------------------------------------------

type ExeArg  = Text
type StdIn   = Text
type StdOut  = Text
type StdErr  = Text

-- | Raise an error if the @--allow-exec@ option was not specified.
--
requireAllowExec :: TCM ()
requireAllowExec = do
  allowExec <- optAllowExec <$> pragmaOptions
  unless allowExec $
    typeError $ GenericError "Missing option --allow-exec"

-- | Convert an @ExitCode@ to an Agda natural number.
--
exitCodeToNat :: ExitCode -> Nat
exitCodeToNat  ExitSuccess    = Nat 0
exitCodeToNat (ExitFailure n) = Nat (toInteger n)

-- | Call a trusted executable with the given arguments and input.
--
--   Returns the exit code, stdout, and stderr.
--
tcExec :: ExeName -> [ExeArg] -> StdIn -> TCM Term
tcExec exe args stdIn = do
  requireAllowExec
  exes <- optTrustedExecutables <$> commandLineOptions
  case Map.lookup exe exes of
    Nothing -> raiseExeNotTrusted exe exes
    Just fp -> do
      -- Check that the executable exists.
      unlessM (liftIO $ doesFileExist fp) $ raiseExeNotFound exe fp
      -- Check that the executable is executable.
      unlessM (liftIO $ executable <$> getPermissions fp) $ raiseExeNotExecutable exe fp

      let strArgs    = T.unpack <$> args
      let strStdIn   = T.unpack stdIn
      (datExitCode, strStdOut, strStdErr) <- lift $ readProcessWithExitCode fp strArgs strStdIn
      let natExitCode = exitCodeToNat datExitCode
      let txtStdOut   = T.pack strStdOut
      let txtStdErr   = T.pack strStdErr
      toR <- toTerm
      return $ toR (natExitCode, (txtStdOut, txtStdErr))

-- | Raise an error if the trusted executable cannot be found.
--
raiseExeNotTrusted :: ExeName -> Map ExeName FilePath -> TCM a
raiseExeNotTrusted exe exes = genericDocError =<< do
  vcat . map pretty $
    ("Could not find '" ++ T.unpack exe ++ "' in list of trusted executables:") :
    [ "  - " ++ T.unpack exe | exe <- Map.keys exes ]

raiseExeNotFound :: ExeName -> FilePath -> TCM a
raiseExeNotFound exe fp = genericDocError =<< do
  text $ "Could not find file '" ++ fp ++ "' for trusted executable " ++ T.unpack exe

raiseExeNotExecutable :: ExeName -> FilePath -> TCM a
raiseExeNotExecutable exe fp = genericDocError =<< do
  text $ "File '" ++ fp ++ "' for trusted executable" ++ T.unpack exe ++ " does not have permission to execute"
