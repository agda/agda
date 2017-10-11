module Agda.Syntax.DoNotation (desugarDoNotation) where

import Control.Applicative
import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Operators

import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad

import Agda.Utils.Pretty ( prettyShow )

desugarDoNotation :: Range -> [DoStmt] -> ScopeM Expr
desugarDoNotation r ss = do
  let qBind = QName $ Name noRange [Hole, Id ">>=", Hole]
      qThen = QName $ Name noRange [Hole, Id ">>", Hole]
  mapM_ ensureInScope [qBind, qThen]
  desugarDo qBind qThen ss

desugarDo :: QName -> QName -> [DoStmt] -> ScopeM Expr
desugarDo qBind qThen [] = genericError "Empty 'do' block"  -- IMPOSSIBLE?
desugarDo qBind qThen [s]
  | DoThen e <- s = return e
  | otherwise     = genericError "The last statement in a 'do' block must be an expression"
desugarDo qBind qThen (DoThen e : ss) = do
  e' <- desugarDo qBind qThen ss
  return (appOp qThen e e')
desugarDo qBind qThen (DoBind r p e [] : ss)
  | Just x <- singleName p = do  -- maybe non-matching
  res <- resolveName (QName x)
  let isMatch = case res of
        ConstructorName{}   -> True
        PatternSynResName{} -> True
        _                   -> False
  body <- desugarDo qBind qThen ss
  if isMatch then return $ matchingBind qBind r p e body []
             else return $ nonMatchingBind qBind r x e body
desugarDo qBind qThen (DoBind r p e cs : ss) = do
  body <- desugarDo qBind qThen ss
  return $ matchingBind qBind r p e body cs
desugarDo qBind qThen (DoLet r ds : ss) =
  Let r ds . Just <$> desugarDo qBind qThen ss

singleName :: Pattern -> Maybe Name
singleName (IdentP (QName x)) = Just x
singleName (RawAppP _ [p])    = singleName p
singleName _                  = Nothing

matchingBind :: QName -> Range -> Pattern -> Expr -> Expr -> [LamClause] -> Expr
matchingBind qBind r p e body cs = appOp (setRange r qBind) e $ ExtendedLam (getRange (body, cs)) (mainClause : cs)
  where
    mainClause = LamClause { lamLHS      = LHS p [] [] []
                           , lamRHS      = RHS body
                           , lamWhere    = NoWhere
                           , lamCatchAll = False }


nonMatchingBind :: QName -> Range -> Name -> Expr -> Expr -> Expr
nonMatchingBind qBind r x e body =
    appOp (setRange r qBind) e $ Lam (getRange (x, body)) [bx] body
  where bx = DomainFree defaultArgInfo $ mkBoundName_ x

app :: Expr -> [Expr] -> Expr
app e es = foldl (\ e1 e2 -> App (getRange (e1, e2)) e1 (defaultNamedArg e2)) e es

appOp :: QName -> Expr -> Expr -> Expr
appOp q e1 e2 = app (Ident q) [e1, e2]

ensureInScope :: QName -> ScopeM ()
ensureInScope q = do
  r <- resolveName q
  case r of
    UnknownName -> genericError $
      prettyShow q ++ " needs to be in scope to use do-notation"
    _ -> return ()
