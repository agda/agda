module Term.Eval (whnf) where

import           Bound.Name                       (instantiateName)
import           Control.Monad                    (mzero, guard)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Maybe        (MaybeT, runMaybeT)
import           Data.Void                        (vacuous)

import           Monad
import           Term

whnf :: Term v -> TC v (Term v)
whnf t@(App (Meta mv) es) = do
    mvInst <- getMetaInst mv
    case mvInst of
      Open{}    -> return t
      Inst _ t' -> whnf $ eliminate (vacuous t') es
whnf t@(App (Def defName) es) = do
    def <- definitionOf defName
    case def of
      Function _ _ cs -> whnfFun t es cs
      _               -> return $ t
whnf (App J (_ : x : _ : _ : Apply p : Apply (App Refl []) : es)) =
    whnf $ eliminate p (x : es)
whnf t = return t

whnfFun :: Term v -> [Elim Term v] -> [Clause] -> TC v (Term v)
whnfFun t _es [] = do
    return t
whnfFun t es (Clause patterns body : clauses) = do
    mbMatched <- runMaybeT $ matchClause es patterns
    case mbMatched of
        Nothing ->
            whnfFun t es clauses
        Just (args, leftoverEs) -> do
            let body' = instantiateName (args !!) (vacuous body)
            whnf $ eliminate body' leftoverEs

matchClause :: [Elim Term v] -> [Pattern]
            -> MaybeT (TC v) ([Term v], [Elim Term v])
matchClause es [] =
    return ([], es)
matchClause (Apply arg : es) (VarP : patterns) = do
    (args, leftoverEs) <- matchClause es patterns
    return (arg : args, leftoverEs)
matchClause (Apply arg : es) (ConP con conPatterns : patterns) = do
    App (Con con') conEs <- lift $ whnf arg
    guard (con == con')
    matchClause (conEs ++ es) (conPatterns ++ patterns)
matchClause _ _ =
    mzero
