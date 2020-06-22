{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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
withName :: MonadReflectedToAbstract m => String -> (Name -> m a) -> m a
withName s f = do
  name <- freshName_ s
  ctx  <- asks $ map nameConcrete
  let name' = head $ filter (notTaken ctx) $ iterate nextName name
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

class ToAbstract r a | r -> a where
  toAbstract :: MonadReflectedToAbstract m => r -> m a

  default toAbstract
    :: (Traversable t, ToAbstract s b, t s ~ r, t b ~ a)
    => MonadReflectedToAbstract m => r -> m a
  toAbstract = traverse toAbstract

-- | Translate reflected syntax to abstract, using the names from the current typechecking context.
toAbstract_ ::
  (ToAbstract r a
  , MonadFresh NameId m
  , MonadError TCErr m
  , MonadTCEnv m
  , ReadTCState m
  , HasOptions m
  , HasBuiltins m
  , HasConstInfo m
  ) => r -> m a
toAbstract_ = withShowAllArguments . toAbstractWithoutImplicit

-- | Drop implicit arguments unless --show-implicit is on.
toAbstractWithoutImplicit ::
  (ToAbstract r a
  , MonadFresh NameId m
  , MonadError TCErr m
  , MonadTCEnv m
  , ReadTCState m
  , HasOptions m
  , HasBuiltins m
  , HasConstInfo m
  ) => r -> m a
toAbstractWithoutImplicit x = runReaderT (toAbstract x) =<< getContextNames

instance ToAbstract r a => ToAbstract (Named name r) (Named name a) where

instance ToAbstract r a => ToAbstract (Arg r) (NamedArg a) where
  toAbstract (Arg i x) = Arg i <$> toAbstract (unnamed x)

instance ToAbstract r a => ToAbstract [Arg r] [NamedArg a] where

instance ToAbstract r Expr => ToAbstract (Dom r, Name) (A.TypedBinding) where
  toAbstract (Dom{domInfo = i,unDom = x, domTactic = tac}, name) = do
    dom <- toAbstract x
    return $ mkTBind noRange (singleton $ unnamedArg i $ mkBinder_ name) dom

instance ToAbstract (Expr, Elim) Expr where
  toAbstract (f, Apply arg) = do
    arg     <- toAbstract arg
    showImp <- showImplicitArguments
    return $ if showImp || visible arg
             then App (setOrigin Reflected defaultAppInfo_) f arg
             else f

instance ToAbstract (Expr, Elims) Expr where
  toAbstract (f, elims) = foldM (curry toAbstract) f elims

instance ToAbstract r a => ToAbstract (R.Abs r) (a, Name) where
  toAbstract (Abs s x) = withName s' $ \name -> (,) <$> toAbstract x <*> return name
    where s' = if (isNoName s) then "z" else s -- TODO: only do this when var is free

instance ToAbstract Literal Expr where
  toAbstract l = return $ A.Lit empty l

instance ToAbstract Term Expr where
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

instance ToAbstract Sort Expr where
  toAbstract s = do
    setName <- fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSet
    case s of
      SetS x -> mkApp (A.Def setName) <$> toAbstract x
      LitS x -> return $ A.Def' setName $ A.Suffix x
      UnknownS -> return $ mkApp (A.Def setName) $ Underscore emptyMetaInfo

instance ToAbstract R.Pattern A.Pattern where
  toAbstract pat = case pat of
    R.ConP c args -> do
      args <- toAbstract args
      return $ A.ConP (ConPatInfo ConOCon patNoRange ConPatEager) (unambiguous $ killRange c) args
    R.DotP t -> A.DotP patNoRange <$> toAbstract t
    R.VarP i -> A.VarP . mkBindName <$> mkVarName i
    R.LitP l  -> return $ A.LitP patNoRange l
    R.AbsurdP -> return $ A.AbsurdP patNoRange
    R.ProjP d -> return $ A.ProjP patNoRange ProjSystem $ unambiguous $ killRange d

instance ToAbstract (QNamed R.Clause) A.Clause where
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

instance ToAbstract [QNamed R.Clause] [A.Clause] where
  toAbstract = traverse toAbstract

instance ToAbstract (List1 (QNamed R.Clause)) (List1 A.Clause) where
  toAbstract = traverse toAbstract
