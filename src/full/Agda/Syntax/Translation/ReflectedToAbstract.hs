{-# OPTIONS_GHC -fwarn-missing-signatures #-}

module Agda.Syntax.Translation.ReflectedToAbstract where

import Control.Arrow        ( (***) )
import Control.Monad        ( foldM )
import Control.Monad.Except ( MonadError )
import Control.Monad.Reader ( MonadReader(..), asks, reader, runReaderT )

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text

import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Common
import Agda.Syntax.Abstract
  ( Name, QName, QNamed(QNamed)
  , isNoName, nameConcrete, nextName, qualify, unambiguous
  )
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern
import Agda.Syntax.Reflected as R
import Agda.Syntax.Internal (Dom,Dom'(..))

import Agda.Interaction.Options (optUseUnicode, UnicodeOrAscii(..))
import Agda.TypeChecking.Monad as M hiding (MetaInfo)
import Agda.Syntax.Scope.Monad (getCurrentModule)

import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Functor
import Agda.Utils.Singleton
import Agda.Utils.Size

type Vars = [(Name,R.Type)]

type MonadReflectedToAbstract m =
  ( MonadReader Vars m
  , MonadFresh NameId m
  , MonadError TCErr m
  , MonadTCEnv m
  , ReadTCState m
  , HasOptions m
  , HasBuiltins m
  , HasConstInfo m
  )

-- | Adds a new unique name to the current context.
--   NOTE: See @chooseName@ in @Agda.Syntax.Translation.AbstractToConcrete@ for similar logic.
--   NOTE: See @freshConcreteName@ in @Agda.Syntax.Scope.Monad@ also for similar logic.
withName :: MonadReflectedToAbstract m => String -> (Name -> m a) -> m a
withName s = withVar s R.Unknown

withVar :: MonadReflectedToAbstract m => String -> R.Type -> (Name -> m a) -> m a
withVar s t f = do
  name <- freshName_ s
  ctx  <- asks $ map $ nameConcrete . fst
  glyphMode <- optUseUnicode <$> M.pragmaOptions
  let freshNameMode = case glyphMode of
        UnicodeOk -> A.UnicodeSubscript
        AsciiOnly -> A.AsciiCounter
  let name' = head $ filter (notTaken ctx) $ iterate (nextName freshNameMode) name
  local ((name,t):) $ f name'
  where
    notTaken xs x = isNoName x || nameConcrete x `notElem` xs

withNames :: MonadReflectedToAbstract m => [String] -> ([Name] -> m a) -> m a
withNames ss = withVars $ zip ss $ repeat R.Unknown

withVars :: MonadReflectedToAbstract m => [(String, R.Type)] -> ([Name] -> m a) -> m a
withVars ss f = case ss of
  []     -> f []
  ((s,t):ss) -> withVar s t $ \n -> withVars ss $ \ns -> f (n:ns)

-- | Returns the name and type of the variable with the given de Bruijn index.
askVar :: MonadReflectedToAbstract m => Int -> m (Maybe (Name,R.Type))
askVar i = reader (!!! i)

askName :: MonadReflectedToAbstract m => Int -> m (Maybe Name)
askName i = fmap fst <$> askVar i

class ToAbstract r where
  type AbsOfRef r
  toAbstract :: MonadReflectedToAbstract m => r -> m (AbsOfRef r)

  default toAbstract
    :: (Traversable t, ToAbstract s, t s ~ r, t (AbsOfRef s) ~ (AbsOfRef r))
    => MonadReflectedToAbstract m => r -> m (AbsOfRef r)
  toAbstract = traverse toAbstract

-- | Translate reflected syntax to abstract, using the names from the current typechecking context.
toAbstract_ ::
  (ToAbstract r
  , MonadFresh NameId m
  , MonadError TCErr m
  , MonadTCEnv m
  , ReadTCState m
  , HasOptions m
  , HasBuiltins m
  , HasConstInfo m
  ) => r -> m (AbsOfRef r)
toAbstract_ = withShowAllArguments . toAbstractWithoutImplicit

-- | Drop implicit arguments unless --show-implicit is on.
toAbstractWithoutImplicit ::
  (ToAbstract r
  , MonadFresh NameId m
  , MonadError TCErr m
  , MonadTCEnv m
  , ReadTCState m
  , HasOptions m
  , HasBuiltins m
  , HasConstInfo m
  ) => r -> m (AbsOfRef r)
toAbstractWithoutImplicit x = do
  xs <- killRange <$> getContextNames
  let ctx = zip xs $ repeat R.Unknown
  runReaderT (toAbstract x) ctx

instance ToAbstract r => ToAbstract (Named name r) where
  type AbsOfRef (Named name r) = Named name (AbsOfRef r)

instance ToAbstract r => ToAbstract (Arg r) where
  type AbsOfRef (Arg r) = NamedArg (AbsOfRef r)
  toAbstract (Arg i x) = Arg i <$> toAbstract (unnamed x)

instance ToAbstract r => ToAbstract [Arg r] where
  type AbsOfRef [Arg r] = [NamedArg (AbsOfRef r)]

-- instance ToAbstract r A.Expr => ToAbstract (Dom r, Name) (A.TypedBinding) where
instance (ToAbstract r, AbsOfRef r ~ A.Expr) => ToAbstract (Dom r, Name) where
  type AbsOfRef (Dom r, Name) = A.TypedBinding
  toAbstract (Dom{domInfo = i, domIsFinite = isfin, unDom = x, domTactic = tac}, name) = do
    dom <- toAbstract x
    -- TODO(Amy): Anyone know why this discards the tactic? It was like
    -- that when I got here!
    return $ A.TBind noRange
      (A.TypedBindingInfo Nothing isfin)
      (singleton $ unnamedArg i $ A.mkBinder_ name)
      dom

instance ToAbstract (A.Expr, Elim) where
  type AbsOfRef (A.Expr, Elim) = A.Expr
  toAbstract (f, Apply arg) = do
    arg     <- toAbstract arg
    showImp <- showImplicitArguments
    return $ if showImp || visible arg
             then A.App (setOrigin Reflected defaultAppInfo_) f arg
             else f

instance ToAbstract (A.Expr, Elims) where
  type AbsOfRef (A.Expr, Elims) = A.Expr
  toAbstract (f, elims) = foldM (curry toAbstract) f elims

instance ToAbstract r => ToAbstract (R.Abs r) where
  type AbsOfRef (R.Abs r) = (AbsOfRef r, Name)
  toAbstract (Abs s x) = withName s' $ \name -> (,name) <$> toAbstract x
    where s' = if (isNoName s) then "z" else s -- TODO: only do this when var is free

instance ToAbstract Literal where
  type AbsOfRef Literal = A.Expr
  toAbstract l = return $ A.Lit empty l

instance ToAbstract Term where
  type AbsOfRef Term = A.Expr
  toAbstract = \case
    R.Var i es -> do
      name <- mkVarName i
      toAbstract (A.Var name, es)
    R.Con c es -> toAbstract (A.Con (unambiguous $ killRange c), es)
    R.Def f es -> do
      af <- mkDef (killRange f)
      toAbstract (af, es)
    R.Lam h t  -> do
      (e, name) <- toAbstract t
      let info  = setHiding h $ setOrigin Reflected defaultArgInfo
      return $ A.Lam exprNoRange (A.mkDomainFree $ unnamedArg info $ A.mkBinder_ name) e
    R.ExtLam cs es -> do
      name <- freshName_ extendedLambdaName
      m    <- getCurrentModule
      let qname   = qualify m name
          cname   = nameConcrete name
          defInfo = mkDefInfo cname noFixity' PublicAccess ConcreteDef noRange
      cs <- toAbstract $ fmap (QNamed qname) cs
      toAbstract
        (A.ExtendedLam exprNoRange defInfo defaultErased qname cs, es)
    R.Pi a b   -> do
      (b, name) <- toAbstract b
      a         <- toAbstract (a, name)
      return $ A.Pi exprNoRange (singleton a) b
    R.Sort s   -> toAbstract s
    R.Lit l    -> toAbstract l
    R.Meta x es    -> do
      info <- mkMetaInfo
      let info' = info{ metaNumber = Just x }
      toAbstract (A.Underscore info', es)
    R.Unknown      -> A.Underscore <$> mkMetaInfo

mkMetaInfo :: ReadTCState m => m MetaInfo
mkMetaInfo = do
  scope <- getScope
  return $ emptyMetaInfo { metaScope = scope }

mkDef :: HasConstInfo m => QName -> m A.Expr
mkDef f = getConstInfo f <&> theDef <&> \case

  Constructor{}
    -> A.Con $ unambiguous f

  Function{ funProjection = Right Projection{ projProper = Just{} } }
    -> A.Proj ProjSystem $ unambiguous f

  d@Function{} | isMacro d
    -> A.Macro f

  _ -> A.Def f

mkApp :: A.Expr -> A.Expr -> A.Expr
mkApp e1 e2 = A.App (setOrigin Reflected defaultAppInfo_) e1 $ defaultNamedArg e2


mkVar :: MonadReflectedToAbstract m => Int -> m (Name, R.Type)
mkVar i = ifJustM (askVar i) return $ do
  cxt   <- getContextTelescope
  names <- asks $ drop (size cxt) . reverse . map fst
  withShowAllArguments' False $ typeError $ DeBruijnIndexOutOfScope i cxt names

mkVarName :: MonadReflectedToAbstract m => Int -> m Name
mkVarName i = fst <$> mkVar i

annotatePattern :: MonadReflectedToAbstract m => Int -> R.Type -> A.Pattern -> m A.Pattern
annotatePattern _ R.Unknown p = return p
annotatePattern i t p = local (drop $ i + 1) $ do
  t <- toAbstract t  -- go into the right context for translating the type
  return $ A.AnnP patNoRange t p

instance ToAbstract Sort where
  type AbsOfRef Sort = A.Expr
  toAbstract s = do
    setName <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSet
    propName <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinProp
    infName <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSetOmega
    case s of
      SetS x -> mkApp (A.Def setName) <$> toAbstract x
      LitS x -> return $ A.Def' setName $ A.Suffix x
      PropS x -> mkApp (A.Def propName) <$> toAbstract x
      PropLitS x -> return $ A.Def' propName $ A.Suffix x
      InfS x -> return $ A.Def' infName $ A.Suffix x
      UnknownS -> mkApp (A.Def setName) . A.Underscore <$> mkMetaInfo

instance ToAbstract R.Pattern where
  type AbsOfRef R.Pattern = A.Pattern
  toAbstract pat = case pat of
    R.ConP c args -> do
      args <- toAbstract args
      return $ A.ConP (ConPatInfo ConOCon patNoRange ConPatEager) (unambiguous $ killRange c) args
    R.DotP t -> A.DotP patNoRange <$> toAbstract t
    R.VarP i -> do
      (x, t) <- mkVar i
      annotatePattern i t $ A.VarP $ A.mkBindName x
    R.LitP l  -> return $ A.LitP patNoRange l
    R.AbsurdP i -> do
      (_, t) <- mkVar i
      annotatePattern i t $ A.AbsurdP patNoRange
    R.ProjP d -> return $ A.ProjP patNoRange ProjSystem $ unambiguous $ killRange d

instance ToAbstract (QNamed R.Clause) where
  type AbsOfRef (QNamed R.Clause) = A.Clause

  toAbstract (QNamed name (R.Clause tel pats rhs)) = withVars (map (Text.unpack *** unArg) tel) $ \_ -> do
    checkClauseTelescopeBindings tel pats
    pats <- toAbstract pats
    rhs  <- toAbstract rhs
    let lhs = spineToLhs $ A.SpineLHS empty name pats
    return $ A.Clause lhs [] (A.RHS rhs Nothing) A.noWhereDecls False
  toAbstract (QNamed name (R.AbsurdClause tel pats)) = withVars (map (Text.unpack *** unArg) tel) $ \_ -> do
    checkClauseTelescopeBindings tel pats
    pats <- toAbstract pats
    let lhs = spineToLhs $ A.SpineLHS empty name pats
    return $ A.Clause lhs [] A.AbsurdRHS A.noWhereDecls False

instance ToAbstract [QNamed R.Clause] where
  type AbsOfRef [QNamed R.Clause] = [A.Clause]
  toAbstract = traverse toAbstract

instance ToAbstract (List1 (QNamed R.Clause)) where
  type AbsOfRef (List1 (QNamed R.Clause)) = List1 A.Clause
  toAbstract = traverse toAbstract

-- | Check that all variables in the telescope are bound in the left-hand side. Since we check the
--   telescope by attaching type annotations to the pattern variables there needs to be somewhere to
--   put the annotation. Also, since the lhs is where the variables are actually bound, missing a
--   binding for a variable that's used later in the telescope causes unbound variable panic
--   (see #5044).
checkClauseTelescopeBindings :: MonadReflectedToAbstract m => [(Text, Arg R.Type)] -> [Arg R.Pattern] -> m ()
checkClauseTelescopeBindings tel pats =
  case reverse [ x | ((x, _), i) <- zip (reverse tel) [0..], not $ Set.member i bs ] of
    [] -> return ()
    xs -> genericDocError $ ("Missing bindings for telescope variable" <> s) <?>
                              (fsep (punctuate ", " $ map (text . Text.unpack) xs) <> ".") $$
                             "All variables in the clause telescope must be bound in the left-hand side."
      where s | length xs == 1 = empty
              | otherwise      = "s"
  where
    bs = boundVars pats

    boundVars = Set.unions . map (bound . unArg)
    bound (R.VarP i)    = Set.singleton i
    bound (R.ConP _ ps) = boundVars ps
    bound R.DotP{}      = Set.empty
    bound R.LitP{}      = Set.empty
    bound (R.AbsurdP i) = Set.singleton i
    bound R.ProjP{}     = Set.empty
