module Agda.Syntax.IdiomBrackets (parseIdiomBrackets) where

import Control.Applicative
import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Operators

import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad

import Agda.Utils.Pretty ( prettyShow )

parseIdiomBrackets :: Range -> Expr -> ScopeM Expr
parseIdiomBrackets r e = do
  let qPure = QName $ Name noRange [Id "pure"]
      qAp   = QName $ Name noRange [Hole, Id "<*>", Hole]
      ePure = App r (Ident qPure) . defaultNamedArg
      eAp a b = App r (App r (Ident qAp) (defaultNamedArg a)) (defaultNamedArg b)
  mapM_ ensureInScope [qPure, qAp]
  case e of
    RawApp _ es -> do
      e : es <- appViewM =<< parseApplication es
      return $ foldl eAp (ePure e) es
    _ -> return $ ePure e

appViewM :: Expr -> ScopeM [Expr]
appViewM e =
  case e of
    App{}           -> let AppView e' es = appView e in (e' :) <$> mapM onlyVisible es
    OpApp _ op _ es -> (Ident op :) <$> mapM (ordinary <=< noPlaceholder <=< onlyVisible) es
    _               -> return [e]
  where
    onlyVisible a
      | defaultNamedArg () == (fmap (() <$) a) = return $ namedArg a
      | otherwise = genericError $ "Only regular arguments are allowed in idiom brackets (no implicit or instance arguments)"
    noPlaceholder Placeholder{}       = genericError "Naked sections are not allowed in idiom brackets"
    noPlaceholder (NoPlaceholder _ x) = return x

    ordinary (Ordinary a) = return a
    ordinary _ = genericError "Binding syntax is not allowed in idiom brackets"

ensureInScope :: QName -> ScopeM ()
ensureInScope q = do
  r <- resolveName q
  case r of
    UnknownName -> genericError $
      prettyShow q ++ " needs to be in scope to use idiom brackets (| ... |)"
    _ -> return ()
