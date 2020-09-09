{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fwarn-missing-signatures #-}

module Agda.Syntax.Translation.ReflectedToAbstract where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text

import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Common
import Agda.Syntax.Abstract as A hiding (Apply)
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
import Agda.Utils.Functor
import Agda.Utils.Singleton
import Agda.Utils.Size

type Names = [Name]

type MonadReflectedToAbstract m =
  ( MonadReader Names m
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
withName s f = do
  name <- freshName_ s
  ctx  <- asks $ map nameConcrete
  glyphMode <- optUseUnicode <$> M.pragmaOptions
  let freshNameMode = case glyphMode of
        UnicodeOk -> A.UnicodeSubscript
        AsciiOnly -> A.AsciiCounter
  let name' = head $ filter (notTaken ctx) $ iterate (nextName freshNameMode) name
  local (name:) $ f name'
  where
    notTaken xs x = isNoName x || nameConcrete x `notElem` xs

withNames :: MonadReflectedToAbstract m => [String] -> ([Name] -> m a) -> m a
withNames ss f = case ss of
  []     -> f []
  (s:ss) -> withNames ss $ \ns -> withName s $ \n -> f (n:ns)

-- | Returns the name of the variable with the given de Bruijn index.
askName :: MonadReflectedToAbstract m => Int -> m (Maybe Name)
askName i = reader (!!! i)

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
toAbstractWithoutImplicit x = runReaderT (toAbstract x) =<< getContextNames

instance ToAbstract r => ToAbstract (Named name r) where
  type AbsOfRef (Named name r) = Named name (AbsOfRef r)

instance ToAbstract r => ToAbstract (Arg r) where
  type AbsOfRef (Arg r) = NamedArg (AbsOfRef r)
  toAbstract (Arg i x) = Arg i <$> toAbstract (unnamed x)

instance ToAbstract r => ToAbstract [Arg r] where
  type AbsOfRef [Arg r] = [NamedArg (AbsOfRef r)]

-- instance ToAbstract r Expr => ToAbstract (Dom r, Name) (A.TypedBinding) where
instance (ToAbstract r, AbsOfRef r ~ Expr) => ToAbstract (Dom r, Name) where
  type AbsOfRef (Dom r, Name) = A.TypedBinding
  toAbstract (Dom{domInfo = i,unDom = x, domTactic = tac}, name) = do
    dom <- toAbstract x
    return $ mkTBind noRange (singleton $ unnamedArg i $ mkBinder_ name) dom

instance ToAbstract (Expr, Elim) where
  type AbsOfRef (Expr, Elim) = Expr
  toAbstract (f, Apply arg) = do
    arg     <- toAbstract arg
    showImp <- showImplicitArguments
    return $ if showImp || visible arg
             then App (setOrigin Reflected defaultAppInfo_) f arg
             else f

instance ToAbstract (Expr, Elims) where
  type AbsOfRef (Expr, Elims) = Expr
  toAbstract (f, elims) = foldM (curry toAbstract) f elims

instance ToAbstract r => ToAbstract (R.Abs r) where
  type AbsOfRef (R.Abs r) = (AbsOfRef r, Name)
  toAbstract (Abs s x) = withName s' $ \name -> (,) <$> toAbstract x <*> return name
    where s' = if (isNoName s) then "z" else s -- TODO: only do this when var is free

instance ToAbstract Literal where
  type AbsOfRef Literal = Expr
  toAbstract l = return $ A.Lit empty l

instance ToAbstract Term where
  type AbsOfRef Term = Expr
  toAbstract t = case t of
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
      return $ A.Lam exprNoRange (mkDomainFree $ unnamedArg info $ mkBinder_ name) e
    R.ExtLam cs es -> do
      name <- freshName_ extendedLambdaName
      m    <- getCurrentModule
      let qname   = qualify m name
          cname   = nameConcrete name
          defInfo = mkDefInfo cname noFixity' PublicAccess ConcreteDef noRange
      cs <- toAbstract $ fmap (QNamed qname) cs
      toAbstract (A.ExtendedLam exprNoRange defInfo qname cs, es)
    R.Pi a b   -> do
      (b, name) <- toAbstract b
      a         <- toAbstract (a, name)
      return $ A.Pi exprNoRange (singleton a) b
    R.Sort s   -> toAbstract s
    R.Lit l    -> toAbstract l
    R.Meta x es    -> toAbstract (A.Underscore info, es)
      where info = emptyMetaInfo{ metaNumber = Just x }
    R.Unknown      -> return $ Underscore emptyMetaInfo

mkDef :: HasConstInfo m => QName -> m A.Expr
mkDef f =
  ifM (isMacro . theDef <$> getConstInfo f)
      (return $ A.Macro f)
      (return $ A.Def f)

mkApp :: Expr -> Expr -> Expr
mkApp e1 e2 = App (setOrigin Reflected defaultAppInfo_) e1 $ defaultNamedArg e2

mkVarName :: MonadReflectedToAbstract m => Int -> m Name
mkVarName i = ifJustM (askName i) return $ do
  cxt   <- getContextTelescope
  names <- asks $ drop (size cxt) . reverse
  withShowAllArguments' False $ typeError $ DeBruijnIndexOutOfScope i cxt names

instance ToAbstract Sort where
  type AbsOfRef Sort = Expr
  toAbstract s = do
    setName <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSet
    case s of
      SetS x -> mkApp (A.Def setName) <$> toAbstract x
      LitS x -> return $ A.Def' setName $ A.Suffix x
      UnknownS -> return $ mkApp (A.Def setName) $ Underscore emptyMetaInfo

instance ToAbstract R.Pattern where
  type AbsOfRef R.Pattern = A.Pattern
  toAbstract pat = case pat of
    R.ConP c args -> do
      args <- toAbstract args
      return $ A.ConP (ConPatInfo ConOCon patNoRange ConPatEager) (unambiguous $ killRange c) args
    R.DotP t -> A.DotP patNoRange <$> toAbstract t
    R.VarP i -> A.VarP . mkBindName <$> mkVarName i
    R.LitP l  -> return $ A.LitP patNoRange l
    R.AbsurdP -> return $ A.AbsurdP patNoRange
    R.ProjP d -> return $ A.ProjP patNoRange ProjSystem $ unambiguous $ killRange d

instance ToAbstract (QNamed R.Clause) where
  type AbsOfRef (QNamed R.Clause) = A.Clause

  -- TODO: remember the types in the telescope
  toAbstract (QNamed name (R.Clause tel pats rhs)) = withNames (map (Text.unpack . fst) tel) $ \_ -> do
    pats <- toAbstract pats
    rhs  <- toAbstract rhs
    let lhs = spineToLhs $ SpineLHS empty name pats
    return $ A.Clause lhs [] (RHS rhs Nothing) noWhereDecls False
  toAbstract (QNamed name (R.AbsurdClause tel pats)) = withNames (map (Text.unpack . fst) tel) $ \_ -> do
    pats <- toAbstract pats
    let lhs = spineToLhs $ SpineLHS empty name pats
    return $ A.Clause lhs [] AbsurdRHS noWhereDecls False

instance ToAbstract [QNamed R.Clause] where
  type AbsOfRef [QNamed R.Clause] = [A.Clause]
  toAbstract = traverse toAbstract

instance ToAbstract (List1 (QNamed R.Clause)) where
  type AbsOfRef (List1 (QNamed R.Clause)) = List1 A.Clause
  toAbstract = traverse toAbstract
