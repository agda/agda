module Impl.LazyScope (LazyScope) where

import Prelude                                    hiding (pi, abs, foldr)

import           Bound                            hiding (instantiate)
import           Bound.Name                       (instantiateName)
import           Prelude.Extras                   (Eq1, (==#))
import           Data.Foldable                    (Foldable, foldr)
import           Data.Traversable                 (Traversable, sequenceA)
import           Data.Functor                     ((<$>))
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT, runMaybeT)
import           Control.Monad                    (guard, mzero)
import           Data.Void                        (vacuous)
import           Data.Monoid                      ((<>), mconcat, mempty)

import           Types.Monad
import           Types.Definition
import           Types.Term
import           Types.Var

-- Base terms
------------------------------------------------------------------------

newtype LazyScope v = LS {unLS :: TermView LazyScope v}
    deriving (Eq, Eq1, Functor, Foldable, Traversable)

instance Monad LazyScope where
    return v = LS (App (Var v) [])

    LS term0 >>= f = LS $ case term0 of
        Lam body           -> Lam (LSAbs (unLSAbs body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (LSAbs (unLSAbs codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        Con n elims        -> Con n (map (>>= f) elims)
        Refl               -> Refl
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unLS $ eliminate (f v) elims'
                   Def n   -> App (Def n)   elims'
                   J       -> App J         elims'
                   Meta mv -> App (Meta mv) elims'

instance IsTerm LazyScope where
    newtype Abs LazyScope v = LSAbs {unLSAbs :: Scope (Named ()) LazyScope v}

    toAbs   = LSAbs . toScope
    fromAbs = fromScope . unLSAbs

    weaken = LSAbs . Scope .  return . F

    instantiate abs t = instantiate1 t (unLSAbs abs)

    abstract v = LSAbs . Bound.abstract f
      where
        f v' = if v == v' then Just (named (varName v) ()) else Nothing

    unview = LS
    view   = unLS

    whnf :: LazyScope v -> TC LazyScope v (LazyScope v)
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
        App J (_ : x : _ : _ : Apply p : Apply (LS Refl) : es) ->
            whnf $ eliminate p (x : es)
        _ ->
            return ls
      where
        whnfFun
            :: LazyScope v -> [Elim LazyScope v] -> [Clause LazyScope]
            -> TC LazyScope v (LazyScope v)
        whnfFun ls' _ [] =
            return ls'
        whnfFun ls' es (Clause patterns body : clauses) = do
            mbMatched <- runMaybeT $ matchClause es patterns
            case mbMatched of
                Nothing ->
                    whnfFun ls' es clauses
                Just (args, leftoverEs) -> do
                    let ixArg n =
                            if n >= length args
                            then error "Impl.LazyScope.whnf: too few arguments"
                            else args !! n
                    let body' = instantiateName ixArg (vacuous body)
                    whnf $ eliminate body' leftoverEs

        matchClause
            :: [Elim LazyScope v] -> [Pattern]
            -> MaybeT (TC LazyScope v) ([LazyScope v], [Elim LazyScope v])
        matchClause es [] =
            return ([], es)
        matchClause (Apply arg : es) (VarP : patterns) = do
            (args, leftoverEs) <- matchClause es patterns
            return (arg : args, leftoverEs)
        matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
            LS (Con dataCon' dataConArgs) <- lift $ whnf arg
            guard (dataCon == dataCon')
            matchClause (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
        matchClause _ _ =
            mzero

    metaVars t = case view t of
        Lam body           -> metaVars $ unscope $ unLSAbs $ body
        Pi domain codomain -> metaVars domain <> metaVars (unscope (unLSAbs (codomain)))
        Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
        App h elims        -> metaVarsHead h <> mconcat (map metaVarsElim elims)
        Set                -> mempty
        Refl               -> mempty
        Con _ args         -> mconcat (map metaVars args)

-- TODO There seems to be a bug preventing us from deriving this.  Check
-- with 7.8.

instance Eq1 (Abs LazyScope) where
    LSAbs s1 ==# LSAbs s2 = s1 ==# s2

instance Functor (Abs LazyScope) where
    fmap f (LSAbs s) = LSAbs $ fmap f s

-- TODO instantiate all the methods
instance Foldable (Abs LazyScope) where
    foldr f x (LSAbs s) = foldr f x s

-- TODO instantiate all the methods
instance Traversable (Abs LazyScope) where
    sequenceA (LSAbs s) = LSAbs <$> sequenceA s
