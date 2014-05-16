module Impl.LazyScope (LazyScope) where

import Prelude hiding (pi, abs)

import           Bound
import           Bound.Name                       (instantiateName)
import           Prelude.Extras                   (Eq1)
import           Data.Foldable                    (Foldable)
import           Data.Traversable                 (Traversable)
import           Data.Void                        (vacuous)
import           Control.Monad                    (guard, mzero)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT, runMaybeT)

import           Types.Term
import           Types.Monad
import           Types.Definition

-- Base terms
------------------------------------------------------------------------

newtype LazyScope v =
    LS {unLS :: TermView (Scope (Named ()) LazyScope) LazyScope v}
    deriving (Eq, Functor, Foldable, Traversable, Eq1)

instance Monad LazyScope where
    return v = LS (App (Var v) [])

    LS term0 >>= f = LS $ case term0 of
        Lam body           -> Lam (body >>>= f)
        Pi domain codomain -> Pi (domain >>= f) (codomain >>>= f)
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unLS $ eliminate (f v) elims'
                   Def n   -> App (Def n)   elims'
                   Con n   -> App (Con n)   elims'
                   J       -> App J         elims'
                   Refl    -> App Refl      elims'
                   Meta mv -> App (Meta mv) elims'

instance Term LazyScope where
    type TermAbs LazyScope = Scope (Named ()) LazyScope

    toAbs   = toScope
    fromAbs = fromScope

    unview = LS
    view   = unLS

    eliminate (LS term0) elims = case (term0, elims) of
        (App (Con _c) args, Proj field : es) ->
            if unField field >= length args
            then error "Impl.LazyScope.eliminate: Bad elimination"
            else case (args !! unField field) of
                   Apply t -> eliminate t es
                   _       -> error "Impl.LazyScope.eliminate: Bad constructor argument"
        (Lam body, Apply argument : es) ->
            eliminate (instantiate1 argument body) es
        (App h es1, es2) ->
            LS $ App h (es1 ++ es2)
        (_, _) ->
            error "Impl.LazyScope.eliminate: Bad elimination"

    whnf ls@(LS t) = case t of
        App (Meta mv) es -> do
            mvInst <- getBodyOfMetaVar mv
            case mvInst of
              Nothing -> return ls
              Just t' -> whnf $ eliminate (vacuous t') es
        App (Def defName) es -> do
            def' <- getDefinition defName
            case def' of
              Function _ _ cs -> whnfFun ls es cs
              _               -> return ls
        App J (_ : x : _ : _ : Apply p : Apply (LS (App Refl [])) : es) ->
            whnf $ eliminate p (x : es)
        _ ->
            return ls

whnfFun :: LazyScope v -> [Elim LazyScope v] -> [Clause LazyScope]
        -> TC LazyScope v (LazyScope v)
whnfFun ls es clauses0 = case clauses0 of
    [] ->
        return ls
    (Clause patterns body : clauses) -> do
        mbMatched <- runMaybeT $ matchClause es patterns
        case mbMatched of
            Nothing ->
                whnfFun ls es clauses
            Just (args, leftoverEs) -> do
                let body' = instantiateName (args !!) (vacuous body)
                whnf $ eliminate body' leftoverEs

matchClause :: [Elim LazyScope v] -> [Pattern]
            -> MaybeT (TC LazyScope v) ([LazyScope v], [Elim LazyScope v])
matchClause es [] =
    return ([], es)
matchClause (Apply arg : es) (VarP : patterns) = do
    (args, leftoverEs) <- matchClause es patterns
    return (arg : args, leftoverEs)
matchClause (Apply arg : es) (ConP con conPatterns : patterns) = do
    LS (App (Con con') conEs) <- lift $ whnf arg
    guard (con == con')
    matchClause (conEs ++ es) (conPatterns ++ patterns)
matchClause _ _ =
    mzero
