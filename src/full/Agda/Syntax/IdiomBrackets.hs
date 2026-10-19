{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}

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

import Agda.Utils.List1  ( List1, pattern (:|), (<|) )
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Utils.Singleton

parseIdiomBracketsSeq :: Range -> Maybe QName -> [Expr] -> ScopeM Expr
parseIdiomBracketsSeq r mod es = do
  let qEmpty = maybe QName qualify mod $ simpleName "empty"
      qPlus  = maybe QName qualify mod $ simpleBinaryOperator "<|>"
      ePlus a b = App r (App r (Ident qPlus) (defaultNamedArg a)) (defaultNamedArg b)
  case es of
    []       -> ensureInScope qEmpty >> return (Ident qEmpty)
    [e]      -> parseIdiomBrackets r mod e
    es@(_:_) -> do
      ensureInScope qPlus
      es' <- mapM (parseIdiomBrackets r mod) es
      return $ foldr1 ePlus es'

parseIdiomBrackets :: Range -> Maybe QName -> Expr -> ScopeM Expr
parseIdiomBrackets r mod e = do
  let qPure = maybe QName qualify mod $ simpleName "pure"
      qAp   = maybe QName qualify mod $ simpleBinaryOperator "<*>"
      ePure   = App r (Ident qPure) . defaultNamedArg
      eAp a b = App r (App r (Ident qAp) (defaultNamedArg a)) (defaultNamedArg b)
  mapM_ ensureInScope [qPure, qAp]
  case e of
    RawApp _ es -> do
      e :| es <- appViewM =<< parseApplication es
      return $ foldl eAp (ePure e) es
    _ -> return $ ePure e

appViewM :: Expr -> ScopeM (List1 Expr)
appViewM = \case
    e@App{}         -> let AppView e' es = appView e in (e' :|) <$> mapM onlyVisible es
    OpApp _ op _ es -> (Ident op <|) <$> mapM (ordinary <=< noPlaceholder <=< onlyVisible) es
    e               -> return $ singleton e
  where
    onlyVisible a
      | defaultNamedArg () == fmap (() <$) a = return $ namedArg a
      | otherwise = idiomBracketError "Only regular arguments are allowed in idiom brackets (no implicit or instance arguments)"
    noPlaceholder Placeholder{}       = idiomBracketError "Naked sections are not allowed in idiom brackets"
    noPlaceholder (NoPlaceholder _ x) = return x

    ordinary (Ordinary a) = return a
    ordinary _ = idiomBracketError "Binding syntax is not allowed in idiom brackets"

ensureInScope :: QName -> ScopeM ()
ensureInScope q = do
  r <- resolveName q
  case r of
    UnknownName -> idiomBracketError $
      prettyShow q ++ " needs to be in scope to use idiom brackets " ++ prettyShow leftIdiomBrkt ++ " ... " ++ prettyShow rightIdiomBrkt
    _ -> return ()

idiomBracketError :: String -> ScopeM a
idiomBracketError = typeError . IdiomBracketError
