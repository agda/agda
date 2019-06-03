module Agda.Syntax.IdiomBrackets (parseIdiomBracketsSeq) where

import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Operators
import Agda.Syntax.Concrete.Pretty ( leftIdiomBrkt, rightIdiomBrkt )

import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad

import Agda.Utils.Pretty ( prettyShow )

parseIdiomBracketsSeq :: Range -> [Expr] -> ScopeM Expr
parseIdiomBracketsSeq r es = do
  let qEmpty = QName $ Name noRange InScope [Id "empty"]
      qPlus  = QName $ Name noRange InScope [Hole, Id "<|>", Hole]
      ePlus a b = App r (App r (Ident qPlus) (defaultNamedArg a)) (defaultNamedArg b)
  case es of
    []       -> ensureInScope qEmpty >> return (Ident qEmpty)
    [e]      -> parseIdiomBrackets r e
    es@(_:_) -> do
      ensureInScope qPlus
      es' <- mapM (parseIdiomBrackets r) es
      return $ foldr1 ePlus es'

parseIdiomBrackets :: Range -> Expr -> ScopeM Expr
parseIdiomBrackets r e = do
  let qPure = QName $ Name noRange InScope [Id "pure"]
      qAp   = QName $ Name noRange InScope [Hole, Id "<*>", Hole]
      ePure   = App r (Ident qPure) . defaultNamedArg
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
      | defaultNamedArg () == fmap (() <$) a = return $ namedArg a
      | otherwise = genericError "Only regular arguments are allowed in idiom brackets (no implicit or instance arguments)"
    noPlaceholder Placeholder{}       = genericError "Naked sections are not allowed in idiom brackets"
    noPlaceholder (NoPlaceholder _ x) = return x

    ordinary (Ordinary a) = return a
    ordinary _ = genericError "Binding syntax is not allowed in idiom brackets"

ensureInScope :: QName -> ScopeM ()
ensureInScope q = do
  r <- resolveName q
  case r of
    UnknownName -> genericError $
      prettyShow q ++ " needs to be in scope to use idiom brackets " ++ prettyShow leftIdiomBrkt ++ " ... " ++ prettyShow rightIdiomBrkt
    _ -> return ()
