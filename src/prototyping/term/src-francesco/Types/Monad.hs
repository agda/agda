module Types.Monad
    ( -- * Monad definition
      TC
    , ClosedTC
    , runTC
      -- * Operations
      -- ** Errors
    , typeError
      -- ** Source location
    , atSrcLoc
      -- ** Definition handling
    , addDefinition
    , getDefinition
      -- ** MetaVar handling
    , addFreshMetaVar
    , instantiateMetaVar
    , getTypeOfMetaVar
    , getBodyOfMetaVar
      -- ** Context handling
    , extendContext
    , getTypeOfName
    , getTypeOfVar
    , closeClauseBody


      -- * Utils
      -- ** Useful synonyms
    , Term
    , Type
      -- ** Context operations
    , ctxPi
    , ctxApp
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Monad.State              (gets, modify)
import           Control.Monad.Reader             (asks)
import qualified Data.Map as Map
import           Bound                            hiding (instantiate, abstract)

import           Syntax.Abstract                  (Name)
import           Syntax.Abstract.Pretty           ()
import           Types.Definition
import           Types.Var
import           Types.Term
import qualified Types.Context                    as Ctx
import           Types.Monad.Types

-- Definitions operations
------------------------------------------------------------------------

addDefinition :: IsTerm t => Name -> Definition t -> TC t v ()
addDefinition x def' =
    modify $ \s -> s { _tsSignature = Map.insert x def' $ _tsSignature s }

getDefinition :: IsTerm t => Name -> TC t v (Definition t)
getDefinition name = atSrcLoc name $ do
  sig <- gets _tsSignature
  case Map.lookup name sig of
    Just def' -> return def'
    Nothing   -> typeError $ "definitionOf: Not in scope " ++ error "TODO definitionOf show name"

-- MetaVar operations
------------------------------------------------------------------------

addFreshMetaVar :: IsTerm t => Type t v -> TC t v (Term t v)
addFreshMetaVar type_ = do
    ctx <- asks _teContext
    let mvType = ctxPi ctx type_
    mv <- nextMetaVar
    modify $ \s -> s { _tsMetaStore = Map.insert mv (Open mvType) $ _tsMetaStore s }
    return $ ctxApp (metaVar mv) ctx
  where
    nextMetaVar = do
        m <- gets $ Map.maxViewWithKey . _tsMetaStore
        return $ case m of
          Nothing                  -> MetaVar 0
          Just ((MetaVar i, _), _) -> MetaVar (i + 1)

instantiateMetaVar :: IsTerm t => MetaVar -> Closed (Term t) -> TC t v ()
instantiateMetaVar mv t = do
  mvInst <- getMetaInst mv
  mvType <- case mvInst of
      Inst _ _    -> typeError $ "instantiateMetaVar: already instantiated."
      Open mvType -> return mvType
  modify $ \s -> s { _tsMetaStore = Map.insert mv (Inst mvType t) (_tsMetaStore s) }

getTypeOfMetaVar :: IsTerm t => MetaVar -> TC t v (Closed (Type t))
getTypeOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst mvType _ -> mvType
      Open mvType   -> mvType

getBodyOfMetaVar :: IsTerm t => MetaVar -> TC t v (Maybe (Closed (Term t)))
getBodyOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst _ mvBody -> Just mvBody
      Open _        -> Nothing

getMetaInst :: IsTerm t => MetaVar -> TC t v (MetaInst t)
getMetaInst mv = do
  mbMvInst <- gets $ Map.lookup mv . _tsMetaStore
  case mbMvInst of
      Nothing     -> typeError $ "getMetaInst: non-existent meta " ++ show mv
      Just mvInst -> return mvInst

-- Operations on the context
------------------------------------------------------------------------

extendContext
    :: (IsTerm t)
    => Name -> Type t v
    -> (TermVar v -> Ctx.Ctx v (Type t) (TermVar v) -> TC t (TermVar v) a)
    -> TC t v a
extendContext n type_ m =
    tcLocal extend (m (B (named n ())) (Ctx.singleton n type_))
  where
    extend env = env { _teContext = Ctx.Snoc (_teContext env) (n, type_) }

getTypeOfName :: (IsTerm t) => Name -> TC t v (v, Type t v)
getTypeOfName n = do
    ctx <- asks _teContext
    case Ctx.lookupName n ctx of
      Nothing -> typeError $ "Name not in scope " ++ show n
      Just t  -> return t

getTypeOfVar :: (IsTerm t) => v -> TC t v (Type t v)
getTypeOfVar v = do
    ctx <- asks _teContext
    return $ Ctx.getVar v ctx

-- TODO this looks very wrong here.  See if you can change the interface
-- to get rid of it.
closeClauseBody :: (IsTerm t) => Term t v -> TC t v (ClauseBody t)
closeClauseBody t = do
    ctx <- asks _teContext
    return $ Scope $ fmap (toIntVar ctx) t
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

-- -- LazyScope term
-- -----------------

-- -- These term uses lazy evaluation and the classic bound 'Scope'.

-- newtype Term v =
--     Term {unTerm :: TermView TermAbs Term v}
--     deriving (Show, Eq, Functor, Foldable, Traversable, Eq1)

-- instance Show1 Term

-- instance Monad Term where
--     return v = Term (App (Var v) [])

--     Term term0 >>= f = Term $ case term0 of
--         Lam body           -> Lam (TermAbs (unTermAbs body >>>= f))
--         Pi domain codomain -> Pi (domain >>= f) (TermAbs (unTermAbs codomain >>>= f))
--         Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
--         Set                -> Set
--         App h elims        ->
--             let elims' = map (>>>= f) elims
--             in case h of
--                    Var v   -> unTerm $ eliminate (f v) elims'
--                    Def n   -> App (Def n)   elims'
--                    Con n   -> App (Con n)   elims'
--                    J       -> App J         elims'
--                    Refl    -> App Refl      elims'
--                    Meta mv -> App (Meta mv) elims'

-- instance (DeBruijn v) => PP.Pretty (Term v) where
--     prettyPrec p (Term t) = PP.prettyPrec p t

-- newtype TermAbs v = TermAbs {unTermAbs :: Scope (Named ()) Term v}
--     deriving (Functor, Traversable, Foldable, Eq1, Eq, Show, Show1)

-- toAbs :: Term (TermVar v) -> TermAbs v
-- toAbs = TermAbs . toScope

-- fromAbs :: TermAbs v -> Term (TermVar v)
-- fromAbs = fromScope . unTermAbs

-- unview :: TermView TermAbs Term v -> Term v
-- unview = Term

-- view :: Term v -> TermView TermAbs Term v
-- view = unTerm

-- instantiate :: TermAbs v -> Term v -> Term v
-- instantiate abs t = instantiate1 t (unTermAbs abs)

-- abstract :: forall v. (DeBruijn v, Eq v) => v -> Term v -> TermAbs v
-- abstract v = TermAbs . Bound.abstract abs
--   where
--     name = Bound.Name.name $ varIndex v

--     abs :: v -> Maybe (Named ())
--     abs v' = if v == v' then Just (named name ()) else Nothing

-- weaken :: Term v -> TermAbs v
-- weaken = TermAbs . Scope . return . F

-- metaVars :: Term v -> HS.HashSet MetaVar
-- metaVars (Term t) = case t of
--     Lam body           -> metaVarsAbs body
--     Pi domain codomain -> metaVars domain <> metaVarsAbs codomain
--     Equal type_ x y    -> metaVars type_ <> metaVars x <> metaVars y
--     App h elims        -> metaVarsHead h <> mconcat (map metaVarsElims elims)
--     Set                -> mempty
--   where
--     metaVarsHead (Meta mv) = HS.singleton mv
--     metaVarsHead _         = mempty

--     metaVarsElims (Apply t') = metaVars t'
--     metaVarsElims _          = mempty

--     metaVarsAbs (TermAbs (Scope t')) = metaVars t'

-- -- | Tries to apply the eliminators to the term.  Trows an error when
-- -- the term and the eliminators don't match.
-- eliminate :: Term v -> [Elim Term v] -> Term v
-- eliminate (Term term0) elims = case (term0, elims) of
--     (t, []) ->
--         Term t
--     (App (Con _c) args, Proj _ field : es) ->
--         if unField field >= length args
--         then error "Impl.Term.eliminate: Bad elimination"
--         else case (args !! unField field) of
--                Apply t -> eliminate t es
--                _       -> error "Impl.Term.eliminate: Bad constructor argument"
--     (Lam body, Apply argument : es) ->
--         eliminate (instantiate body argument) es
--     (App h es1, es2) ->
--         Term $ App h (es1 ++ es2)
--     (_, _) ->
--         error "Impl.Term.eliminate: Bad elimination"

-- whnf :: Term v -> TC v (Term v)
-- whnf ls@(Term t) = case t of
--     App (Meta mv) es -> do
--         mvInst <- getBodyOfMetaVar mv
--         case mvInst of
--           Nothing -> return ls
--           Just t' -> whnf $ eliminate (vacuous t') es
--     App (Def defName) es -> do
--         def' <- getDefinition defName
--         case def' of
--           Function _ _ cs -> whnfFun ls es cs
--           _               -> return ls
--     App J (_ : x : _ : _ : Apply p : Apply (Term (App Refl [])) : es) ->
--         whnf $ eliminate p (x : es)
--     _ ->
--         return ls

-- whnfFun :: Term v -> [Elim Term v] -> [Clause Term] -> TC v (Term v)
-- whnfFun ls es clauses0 = case clauses0 of
--     [] ->
--         return ls
--     (Clause patterns body : clauses) -> do
--         mbMatched <- runMaybeT $ matchClause es patterns
--         case mbMatched of
--             Nothing ->
--                 whnfFun ls es clauses
--             Just (args, leftoverEs) -> do
--                 let body' = instantiateName (args !!) (vacuous body)
--                 whnf $ eliminate body' leftoverEs

-- matchClause :: [Elim Term v] -> [Pattern]
--             -> MaybeT (TC v) ([Term v], [Elim Term v])
-- matchClause es [] =
--     return ([], es)
-- matchClause (Apply arg : es) (VarP : patterns) = do
--     (args, leftoverEs) <- matchClause es patterns
--     return (arg : args, leftoverEs)
-- matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
--     Term (App (Con dataCon') dataConEs) <- lift $ whnf arg
--     guard (dataCon == dataCon')
--     matchClause (dataConEs ++ es) (dataConPatterns ++ patterns)
-- matchClause _ _ =
--     mzero

-- Context
----------

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: IsTerm t => Type t v -> Ctx.Ctx v0 (Type t) v -> Type t v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ reverse $ go ctx0
  where
    go :: IsTerm t => Ctx.Ctx v0 (Type t) v -> [v]
    go Ctx.Empty                    = []
    go (Ctx.Snoc ctx (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: IsTerm t => Ctx.Ctx v0 (Type t) v -> Type t v -> Type t v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- Pretty printing
------------------

-- instance PP.Pretty (Definition Term) where
--   prettyPrec _ _ = PP.text "TODO pretty Definition"
