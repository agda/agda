{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

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
import Agda.Utils.List
import Agda.Utils.Functor

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
toAbstract_ :: (ToAbstract r a) => r -> TCM a
toAbstract_ x = runReaderT (toAbstract x) =<< getContextNames

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
    arg <- toAbstract arg
    return $ App (ExprRange noRange) f arg

instance ToAbstract (Expr, Elims) Expr where
  toAbstract (f, elims) = foldM (curry toAbstract) f elims

instance ToAbstract r a => ToAbstract (R.Abs r) (a, Name) where
  toAbstract (Abs s x) = withName s' $ \name -> (,) <$> toAbstract x <*> return name
    where s' = if (isNoName s) then "z" else s -- TODO: only do this when var is free

instance ToAbstract Literal Expr where
  toAbstract l@(LitNat    {}) = return (A.Lit l)
  toAbstract l@(LitFloat  {}) = return (A.Lit l)
  toAbstract l@(LitString {}) = return (A.Lit l)
  toAbstract l@(LitChar   {}) = return (A.Lit l)
  toAbstract l@(LitQName  {}) = return (A.Lit l)

instance ToAbstract Term Expr where
  toAbstract t = case t of
    R.Var i es -> do
      let fallback = withName ("@" ++ show i) return
      name <- fromMaybeM fallback $ askName i
      toAbstract (A.Var name, es)
    R.Con c es -> toAbstract (A.Con (AmbQ [killRange c]), es)
    R.Def f es -> toAbstract (A.Def (killRange f), es)
    R.Lam h t  -> do
      (e, name) <- toAbstract t
      let info  = setHiding h defaultArgInfo
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
    R.QuoteGoal t -> do
      (e, name) <- toAbstract t
      return $ A.QuoteGoal exprNoRange name e
    R.QuoteTerm t  -> toAbstract (A.QuoteTerm exprNoRange, Apply $ defaultArg t)
    R.QuoteContext -> return $ A.QuoteContext exprNoRange
    R.Unquote t es -> toAbstract (A.Unquote exprNoRange, Apply (defaultArg t) : es)
    R.Unknown      -> return $ Underscore emptyMetaInfo

instance ToAbstract Type Expr where
  toAbstract (El _ x) = toAbstract x

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
      return (names, A.ConP (ConPatInfo ConPCon patNoRange) (AmbQ [killRange c]) args)
    R.DotP    -> return ([], A.DotP patNoRange (Underscore emptyMetaInfo))
    R.VarP s  -> withName s' $ \name -> return ([name], A.VarP name)
      where s' = if (isNoName s) then "z" else s --TODO: only do this when var is free
    R.LitP l  -> return ([], A.LitP l)
    R.AbsurdP -> return ([], A.AbsurdP patNoRange)
    R.ProjP p -> return ([], A.DefP patNoRange p [])

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
    return $ A.Clause lhs (RHS rhs) [] False
  toAbstract (QNamed name (R.AbsurdClause pats)) = do
    (_, pats) <- toAbstractPats pats
    let lhs = spineToLhs $ SpineLHS (LHSRange noRange) name pats []
    return $ A.Clause lhs AbsurdRHS [] False

instance ToAbstract [QNamed R.Clause] [A.Clause] where
  toAbstract = traverse toAbstract
