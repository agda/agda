module Eval
    ( -- * Elimination
      eliminate
      -- * 'Blocked'
    , Blocked(..)
    , ignoreBlocking
      -- * Reducing
    , whnf
    , nf
    , nfElim
    ) where

import           Prelude                          hiding (pi)

import           Bound.Name                       (instantiateName)
import           Data.Void                        (vacuousM)
import           Control.Monad                    (guard, mzero, void)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT(MaybeT), runMaybeT)
import           Prelude.Extras                   (Eq1((==#)))
import qualified Data.Set                         as Set

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import           Types.Var
import           Types.Definition
import qualified Types.Signature                  as Sig
import           Types.Term

-- | Tries to apply the eliminators to the term.  Trows an error
-- when the term and the eliminators don't match.
eliminate :: (IsTerm t) => t v -> [Elim t v] -> t v
eliminate t elims = case (view t, elims) of
    (_, []) ->
        t
    (Con _c args, Proj _ field : es) ->
        if unField field >= length args
        then error "Eval.eliminate: Bad elimination"
        else eliminate (args !! unField field) es
    (Lam body, Apply argument : es) ->
        eliminate (instantiate body argument) es
    (App h es1, es2) ->
        unview $ App h (es1 ++ es2)
    (_, _) ->
        error "Eval.eliminate: Bad elimination"

data Blocked t v
    = NotBlocked (t v)
    | MetaVarHead MetaVar [Elim t v]
    -- ^ The term is 'MetaVar'-headed.
    | BlockedOn (Set.Set MetaVar) Name [Elim t v]
    -- ^ Returned when a 'MetaVar' is preventing us from reducing a
    -- definition.  The 'Name' is the name of the definition, the
    -- 'Elim's the eliminators stuck on it.
    --
    -- Note that it might not be the only 'MetaVar' preventing us to do
    -- so.
    deriving (Eq)

instance Eq1 t => Eq1 (Blocked t) where
    NotBlocked t1 ==# NotBlocked t2 =
      t1 ==# t2
    MetaVarHead mv1 es1 ==# MetaVarHead mv2 es2 =
      mv1 == mv2 && and (zipWith (==#) es1 es2)
    BlockedOn mv1 n1 es1 ==# BlockedOn mv2 n2 es2 =
      mv1 == mv2 && n1 == n2 && and (zipWith (==#) es1 es2)
    _ ==# _ =
      False

ignoreBlocking :: (IsTerm t) => Blocked t v -> t v
ignoreBlocking (NotBlocked t)           = t
ignoreBlocking (MetaVarHead mv es)      = metaVar mv es
ignoreBlocking (BlockedOn _ funName es) = def funName es

whnf :: (IsTerm t) => Sig.Signature t -> t v -> Blocked t v
whnf sig t = case view t of
  App (Meta mv) es | Just t' <- Sig.getMetaVarBody sig mv ->
    whnf sig $ eliminate (vacuousM t') es
  App (Def defName) es | Function _ cs <- Sig.getDefinition sig defName ->
    whnfFun sig defName es cs
  App J (_ : x : _ : _ : Apply p : Apply refl' : es) | Refl <- view refl' ->
    whnf sig $ eliminate p (x : es)
  App (Meta mv) elims ->
    MetaVarHead mv elims
  _ ->
    NotBlocked t

whnfFun
  :: (IsTerm t)
  => Sig.Signature t -> Name -> [Elim t v] -> [Clause t] -> Blocked t v
whnfFun _ funName es [] =
  NotBlocked $ def funName es
whnfFun sig funName es (Clause patterns body : clauses) =
  case runMaybeT (matchClause sig es patterns) of
    Left mv ->
      BlockedOn mv funName es
    Right Nothing ->
      whnfFun sig funName es clauses
    Right (Just (args, leftoverEs)) -> do
      let ixArg n = if n >= length args
                    then error "Eval.whnf: too few arguments"
                    else args !! n
      let body' = instantiateName ixArg (vacuousM body)
      whnf sig $ eliminate body' leftoverEs

matchClause
  :: (IsTerm t)
  => Sig.Signature t -> [Elim t v] -> [Pattern]
  -> MaybeT (Either (Set.Set MetaVar)) ([t v], [Elim t v])
matchClause _ es [] =
  return ([], es)
matchClause sig (Apply arg : es) (VarP : patterns) = do
  (args, leftoverEs) <- matchClause sig es patterns
  return (arg : args, leftoverEs)
matchClause sig (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
  case whnf sig arg of
    MetaVarHead mv _ -> do
      -- Here we just want to see if we would make it without this
      -- blockage.  This also means that the last metavariable will
      -- block first.
      case matchClause sig es patterns of
        MaybeT (Left mvs)      -> MaybeT $ Left $ Set.insert mv mvs
        MaybeT (Right Nothing) -> MaybeT $ Right Nothing
        MaybeT (Right _)       -> MaybeT $ Left $ Set.singleton mv
    NotBlocked t | Con dataCon' dataConArgs <- view t -> do
      guard (dataCon == dataCon')
      matchClause sig (map Apply dataConArgs ++ es) (dataConPatterns ++ patterns)
    _ ->
      mzero
matchClause _ _ _ =
  mzero

nf :: (IsTerm t) => Sig.Signature t -> t v -> t v
nf sig t = case view (ignoreBlocking (whnf sig t)) of
  Lam body ->
    lam $ nfAbs body
  Pi domain codomain ->
    pi (nf sig domain) (nfAbs codomain)
  Equal type_ x y ->
    equal (nf sig type_) (nf sig x) (nf sig y)
  Refl ->
    refl
  Con dataCon args ->
    con dataCon $ map (nf sig) args
  Set ->
    set
  App h elims ->
    app h $ map nfElim elims
  where
    nfAbs = toAbs . nf sig . fromAbs

    nfElim (Apply t') = Apply $ nf sig t'
    nfElim (Proj n f) = Proj n f

nfElim :: (IsTerm t) => Sig.Signature t -> Elim t v -> Elim t v
nfElim sig (Proj ix field) = Proj ix field
nfElim sig (Apply t)       = Apply $ nf sig t
