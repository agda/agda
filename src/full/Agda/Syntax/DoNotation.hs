{-# OPTIONS_GHC -Wunused-imports #-}

{-|
    Desugaring for do-notation. Uses whatever `_>>=_` and `_>>_` happen to be
    in scope.

    Example:

    ```
      foo = do
        x ← m₁
        m₂
        just y ← m₃
          where nothing → m₄
        let z = t
        m₅
    ```
    desugars to
    ```
      foo =
        m₁ >>= λ x →
        m₂ >>
        m₃ >>= λ where
          just y → let z = t in m₅
          nothing → m₄
    ```
 -}
module Agda.Syntax.DoNotation (desugarDoNotation) where

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete

import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad

import Agda.Utils.List1  ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Singleton

import Agda.Utils.Impossible

desugarDoNotation :: Range -> List1 DoStmt -> ScopeM Expr
desugarDoNotation r ss = do
  let qBind = QName $ simpleBinaryOperator ">>="
      qThen = QName $ simpleBinaryOperator ">>"
      isBind DoBind{} = True
      isBind _        = False
      isThen DoThen{} = True
      isThen _        = False
  -- Only check the operation we actually need. One could imagine to fall back
  -- on _>>=_ if _>>_ is not in scope, but if we are desugaring to _>>_ at all
  -- I think we should throw an error rather than silently switching to _>>=_.
  -- / Ulf
  mapM_ ensureInScope $ [qBind | any isBind ss] ++
                        [qThen | any isThen $ List1.init ss] -- ignore the last 'DoThen'
  desugarDo qBind qThen ss

desugarDo :: QName -> QName -> List1 DoStmt -> ScopeM Expr
desugarDo qBind qThen = \case

  -- The last statement must be a DoThen.
  DoThen e        :| [] -> return e

  -- Or an absurd bind.
  DoBind r p e [] :| [] | Just (r', NotHidden) <- isAbsurdP p ->
    return $ appOp (setRange r qBind) e $ AbsurdLam r' NotHidden

  -- Otherwise, sorry.
  _ :| [] -> failure

  -- `DoThen` and `DoLet` are easy.
  DoThen e   :| ss -> appOp qThen e   <$> desugarDo0 ss
  DoLet r ds :| ss -> Let r ds . Just <$> desugarDo0 ss

  -- `DoBind` requires more work since we want to generate plain lambdas when possible.
  DoBind r p e [] :| ss | Just x <- singleName p -> do
    -- In this case we have a single name in the bind pattern and no where clauses.
    -- It could still be a pattern bind though (for instance, `refl ← pure eq`), so
    -- to figure out which one to use we look up the name in the scope; if it's a
    -- constructor or pattern synonym we desugar to a pattern lambda.
    res <- resolveName (QName x)
    let isMatch = case res of
          ConstructorName{}   -> True
          PatternSynResName{} -> True
          _                   -> False
    rest <- desugarDo0 ss
    if isMatch then return $ matchingBind qBind r p e rest []
               else return $ nonMatchingBind qBind r x e rest

  -- If there are @where@ clauses we have to desugar to a pattern lambda.
  DoBind r p e cs :| ss -> do
    rest <- desugarDo0 ss
    return $ matchingBind qBind r p e rest cs

  where
  desugarDo0 :: [DoStmt] -> ScopeM Expr
  desugarDo0 ss = List1.ifNull ss failure $ desugarDo qBind qThen

  failure = genericError
    "The last statement in a 'do' block must be an expression or an absurd match."

singleName :: Pattern -> Maybe Name
singleName = \case
  IdentP _ (QName x) -> Just x
  _ -> Nothing

matchingBind :: QName -> Range -> Pattern -> Expr -> Expr -> [LamClause] -> Expr
matchingBind qBind r p e body cs =
  appOp (setRange r qBind) e             -- Set the range of the lambda to that of the
    $ ExtendedLam (getRange cs)          -- where-clauses to make highlighting of overlapping
        defaultErased                    -- patterns not highlight the rest of the do-block.
    $ fmap addParens (mainClause :| cs)
  where
    mainClause = LamClause { lamLHS      = [p]
                           , lamRHS      = RHS body
                           , lamCatchAll = False }

    -- Add parens to left-hand sides.
    addParens c = c { lamLHS = addP (lamLHS c) }
      where
      addP []           = __IMPOSSIBLE__
      addP pps@(p : ps) = [ParenP (getRange pps) $ rawAppP $ p :| ps ]

nonMatchingBind :: QName -> Range -> Name -> Expr -> Expr -> Expr
nonMatchingBind qBind r x e body =
    appOp (setRange r qBind) e $ Lam (getRange (x, body)) (singleton bx) body
  where bx = DomainFree $ defaultNamedArg $ mkBinder_ x

appOp :: QName -> Expr -> Expr -> Expr
appOp q e1 e2 = app (Ident q) [par e1, par e2]
  where
    par e = Paren (getRange e) e  -- Add parens to get the right precedence context (#3152)
    app e es = foldl (\ e1 e2 -> App (getRange (e1, e2)) e1 (defaultNamedArg e2)) e es

ensureInScope :: QName -> ScopeM ()
ensureInScope q = do
  r <- resolveName q
  case r of
    UnknownName -> genericError $
      prettyShow q ++ " needs to be in scope to desugar 'do' block"
    _ -> return ()
