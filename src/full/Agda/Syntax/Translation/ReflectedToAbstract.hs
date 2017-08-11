{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fwarn-missing-signatures #-}

module Agda.Syntax.Translation.ReflectedToAbstract where

import Control.Applicative
import Control.Monad.Reader

import Data.Traversable as Trav hiding (mapM)

import Agda.Syntax.Fixity
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Info
import Agda.Syntax.Common
import Agda.Syntax.Abstract as A hiding (Apply)
import Agda.Syntax.Reflected as R

import Agda.TypeChecking.Monad as M hiding (MetaInfo)
import Agda.Syntax.Scope.Monad (getCurrentModule)

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.List
import Agda.Utils.Functor
import Agda.Utils.Size

type Names = [Name]

type WithNames a = ReaderT Names TCM a
-- Note: we only need the TCM for fresh names

-- | Adds a new unique name to the current context.
withName :: String -> (Name -> WithNames a) -> WithNames a
withName s f = do
  name <- freshName_ s
  ctx  <- asks $ map nameConcrete
  let name' = head $ filter (notTaken ctx) $ iterate nextName name
  local (name:) $ f name'
  where
    notTaken xs x = isNoName x || nameConcrete x `notElem` xs

-- | Returns the name of the variable with the given de Bruijn index.
askName :: Int -> WithNames (Maybe Name)
askName i = reader (!!! i)

class ToAbstract r a | r -> a where
  toAbstract :: r -> WithNames a

-- | Translate reflected syntax to abstract, using the names from the current typechecking context.
toAbstract_ :: ToAbstract r a => r -> TCM a
toAbstract_ = withShowAllArguments . toAbstractWithoutImplicit

-- | Drop implicit arguments unless --show-implicit is on.
toAbstractWithoutImplicit :: ToAbstract r a => r -> TCM a
toAbstractWithoutImplicit x = runReaderT (toAbstract x) =<< getContextNames

instance ToAbstract r a => ToAbstract (Named name r) (Named name a) where
  toAbstract = traverse toAbstract

instance ToAbstract r a => ToAbstract (Arg r) (NamedArg a) where
  toAbstract (Arg i x) = Arg i <$> toAbstract (unnamed x)

instance ToAbstract [Arg Term] [NamedArg Expr] where
  toAbstract = traverse toAbstract

instance ToAbstract r Expr => ToAbstract (Dom r, Name) (A.TypedBindings) where
  toAbstract (Dom i x, name) = do
    dom <- toAbstract x
    return $ TypedBindings noRange $ Arg i $ TBind noRange [pure name] dom

instance ToAbstract (Expr, Elim) Expr where
  toAbstract (f, Apply arg) = do
    arg     <- toAbstract arg
    showImp <- lift showImplicitArguments
    return $ if showImp || visible arg
             then App (ExprRange noRange) f arg
             else f

instance ToAbstract (Expr, Elims) Expr where
  toAbstract (f, elims) = foldM (curry toAbstract) f elims

instance ToAbstract r a => ToAbstract (R.Abs r) (a, Name) where
  toAbstract (Abs s x) = withName s' $ \name -> (,) <$> toAbstract x <*> return name
    where s' = if (isNoName s) then "z" else s -- TODO: only do this when var is free

instance ToAbstract Literal Expr where
  toAbstract l = return (A.Lit l)

instance ToAbstract Term Expr where
  toAbstract t = case t of
    R.Var i es -> do
      mname <- askName i
      case mname of
        Nothing -> do
          cxt   <- lift $ getContextTelescope
          names <- asks $ drop (size cxt) . reverse
          lift $ withShowAllArguments' False $ typeError $ DeBruijnIndexOutOfScope i cxt names
        Just name -> toAbstract (A.Var name, es)
    R.Con c es -> toAbstract (A.Con (AmbQ [killRange c]), es)
    R.Def f es -> do
      af <- lift $ mkDef (killRange f)
      toAbstract (af, es)
    R.Lam h t  -> do
      (e, name) <- toAbstract t
      let info  = setHiding h $ setOrigin Reflected defaultArgInfo
      return $ A.Lam exprNoRange (DomainFree info name) e
    R.ExtLam cs es -> do
      name <- freshName_ extendedLambdaName
      m    <- lift $ getCurrentModule
      let qname   = qualify m name
          cname   = nameConcrete name
          defInfo = mkDefInfo cname noFixity' PublicAccess ConcreteDef noRange
      cs <- toAbstract $ map (QNamed qname) cs
      toAbstract (A.ExtendedLam exprNoRange defInfo qname cs, es)
    R.Pi a b   -> do
      (b, name) <- toAbstract b
      a         <- toAbstract (a, name)
      return $ A.Pi exprNoRange [a] b
    R.Sort s   -> toAbstract s
    R.Lit l    -> toAbstract l
    R.Meta x es    -> toAbstract (A.Underscore info, es)
      where info = emptyMetaInfo{ metaNumber = Just x }
    R.Unknown      -> return $ Underscore emptyMetaInfo

mkDef :: QName -> TCM A.Expr
mkDef f =
  ifM (isMacro . theDef <$> getConstInfo f)
      (return $ A.Macro f)
      (return $ A.Def f)

mkSet :: Expr -> Expr
mkSet e = App exprNoRange (A.Set exprNoRange 0) $ defaultNamedArg e

instance ToAbstract Sort Expr where
  toAbstract (SetS x) = mkSet <$> toAbstract x
  toAbstract (LitS x) = return $ A.Set exprNoRange x
  toAbstract UnknownS = return $ mkSet $ Underscore emptyMetaInfo

instance ToAbstract R.Pattern (Names, A.Pattern) where
  toAbstract pat = case pat of
    R.ConP c args -> do
      (names, args) <- toAbstractPats args
      return (names, A.ConP (ConPatInfo ConOCon patNoRange) (AmbQ [killRange c]) args)
    R.DotP    -> return ([], A.WildP patNoRange)
    R.VarP s | isNoName s -> withName "z" $ \ name -> return ([name], A.VarP name)
        -- Ulf, 2016-08-09: Also bind noNames (#2129). This to make the
        -- behaviour consistent with lambda and pi.
        -- return ([], A.WildP patNoRange)
    R.VarP s  -> withName s $ \ name -> return ([name], A.VarP name)
    R.LitP l  -> return ([], A.LitP l)
    R.AbsurdP -> return ([], A.AbsurdP patNoRange)
    R.ProjP d -> return ([], A.ProjP patNoRange ProjSystem $ AmbQ [killRange d])

toAbstractPats :: [Arg R.Pattern] -> WithNames (Names, [NamedArg A.Pattern])
toAbstractPats pats = case pats of
    []   -> return ([], [])
    p:ps -> do
      (names,  p)  <- (distributeF . fmap distributeF) <$> toAbstract p
      (namess, ps) <- local (names++) $ toAbstractPats ps
      return (namess++names, p:ps)

instance ToAbstract (QNamed R.Clause) A.Clause where
  toAbstract (QNamed name (R.Clause pats rhs)) = do
    (names, pats) <- toAbstractPats pats
    rhs           <- local (names++) $ toAbstract rhs
    let lhs = spineToLhs $ SpineLHS (LHSRange noRange) name pats []
    return $ A.Clause lhs [] (RHS rhs Nothing) [] False
  toAbstract (QNamed name (R.AbsurdClause pats)) = do
    (_, pats) <- toAbstractPats pats
    let lhs = spineToLhs $ SpineLHS (LHSRange noRange) name pats []
    return $ A.Clause lhs [] AbsurdRHS [] False

instance ToAbstract [QNamed R.Clause] [A.Clause] where
  toAbstract = traverse toAbstract
