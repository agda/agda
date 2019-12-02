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

import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete

import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad

import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.List   ( initMaybe )

desugarDoNotation :: Range -> [DoStmt] -> ScopeM Expr
desugarDoNotation r ss = do
  let qBind = QName $ Name noRange InScope [Hole, Id ">>=", Hole]
      qThen = QName $ Name noRange InScope [Hole, Id ">>", Hole]
      isBind DoBind{} = True
      isBind _        = False
      isThen DoThen{} = True
      isThen _        = False
  -- Only check the operation we actually need. One could imagine to fall back
  -- on _>>=_ if _>>_ is not in scope, but if we are desugaring to _>>_ at all
  -- I think we should throw an error rather than silently switching to _>>=_.
  -- / Ulf
  mapM_ ensureInScope $ [qBind | any isBind ss] ++
                        [qThen | any isThen $ fromMaybe ss $ initMaybe ss] -- ignore the last 'DoThen'
  desugarDo qBind qThen ss

desugarDo :: QName -> QName -> [DoStmt] -> ScopeM Expr

-- The parser doesn't generate empty 'do' blocks at the moment, but if that
-- changes throwing the error is the right thing to do.
desugarDo qBind qThen [] = genericError "Empty 'do' block"

-- The last statement must be a DoThen
desugarDo qBind qThen [s]
  | DoThen e              <- s           = return e
  | DoBind r p e []       <- s
  , Just (r' , NotHidden) <- isAbsurdP p =
      return $ appOp (setRange r qBind) e $ AbsurdLam r' NotHidden
  | otherwise                            =
      genericError "The last statement in a 'do' block must be an expression or an absurd match."

-- `DoThen` and `DoLet` are easy
desugarDo qBind qThen (DoThen e   : ss) = appOp qThen e   <$> desugarDo qBind qThen ss
desugarDo qBind qThen (DoLet r ds : ss) = Let r ds . Just <$> desugarDo qBind qThen ss

-- `DoBind` requires more work since we want to generate plain lambdas when
-- possible.
desugarDo qBind qThen (DoBind r p e [] : ss)
  | Just x <- singleName p = do
  -- In this case we have a single name in the bind pattern and no where clauses.
  -- It could still be a pattern bind though (for instance, `refl ← pure eq`), so
  -- to figure out which one to use we look up the name in the scope; if it's a
  -- constructor or pattern synonym we desugar to a pattern lambda.
  res <- resolveName (QName x)
  let isMatch = case res of
        ConstructorName{}   -> True
        PatternSynResName{} -> True
        _                   -> False
  rest <- desugarDo qBind qThen ss
  if isMatch then return $ matchingBind qBind r p e rest []
             else return $ nonMatchingBind qBind r x e rest
desugarDo qBind qThen (DoBind r p e cs : ss) = do
  -- If there are where clauses we have to desugar to a pattern lambda.
  rest <- desugarDo qBind qThen ss
  return $ matchingBind qBind r p e rest cs

singleName :: Pattern -> Maybe Name
singleName (IdentP (QName x)) = Just x
singleName (RawAppP _ [p])    = singleName p
singleName _                  = Nothing

matchingBind :: QName -> Range -> Pattern -> Expr -> Expr -> [LamClause] -> Expr
matchingBind qBind r p e body cs =
  appOp (setRange r qBind) e          -- Set the range of the lambda to that of the
    $ ExtendedLam (getRange cs)       -- where-clauses to make highlighting of overlapping
    $ map addParens (mainClause : cs) -- patterns not highlight the rest of the do-block.
  where
    mainClause = LamClause { lamLHS      = LHS p [] [] NoEllipsis
                           , lamRHS      = RHS body
                           , lamWhere    = NoWhere
                           , lamCatchAll = False }

    -- Add parens to left-hand sides: there can only be one pattern in these clauses.
    addParens c = c { lamLHS = addP (lamLHS c) }
      where addP (LHS p rw we ell) = LHS (RawAppP noRange [ParenP noRange p]) rw we ell

nonMatchingBind :: QName -> Range -> Name -> Expr -> Expr -> Expr
nonMatchingBind qBind r x e body =
    appOp (setRange r qBind) e $ Lam (getRange (x, body)) [bx] body
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
