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

      -- * 'Term' type
    , Term
    , TermAbs
    , toAbs
    , fromAbs
    , unview
    , view
    , instantiate
    , eliminate
    , whnf
    , weaken

      -- ** Utils
    , Type
      -- *** 'Term' smart constructors
    , lam
    , pi
    , equal
    , app
    , set
    , var
    , metaVar
    , def
    , con
    , refl
    , whnfView
      -- ** 'Ctx' to 'Term'
    , ctxApp
    , ctxPi
    ) where

import Prelude                                    hiding (abs, pi)

import           Control.Applicative              (Applicative, (<$>))
import           Control.Monad.State              (MonadState, gets, modify, State, evalState)
import           Control.Monad.Reader             (MonadReader, asks, local, ReaderT(ReaderT), runReaderT)
import           Control.Monad.Error              (MonadError, throwError, Error, strMsg, ErrorT, runErrorT)
import           Data.Void                        (Void, vacuous)
import qualified Data.Map as Map
import           Bound                            hiding (instantiate)
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)
import           Control.Monad                    (guard, mzero, liftM)
import           Control.Monad.Trans              (lift)
import           Control.Monad.Trans.Maybe        (MaybeT, runMaybeT)
import           Prelude.Extras                   (Eq1, Show1)
import           Bound.Name                       (instantiateName)
import           Data.Monoid                      ((<>))

import qualified Text.PrettyPrint.Extended        as PP
import           Syntax.Abstract                  (Name, SrcLoc, noSrcLoc, HasSrcLoc, srcLoc)
import           Syntax.Abstract.Pretty           ()
import           Types.Term
import           Types.Definition
import qualified Types.Context                    as Ctx

-- Monad definition
------------------------------------------------------------------------

newtype TC v a =
    TC {unTC :: ReaderT (TCEnv v) (ErrorT TCErr (State TCState)) a}
    deriving (Functor, Applicative, Monad, MonadReader (TCEnv v), MonadState TCState, MonadError TCErr)

type ClosedTC = TC Void

runTC :: ClosedTC a -> IO (Either TCErr a)
runTC m = return $ flip evalState initState
                 $ runErrorT
                 $ flip runReaderT initEnv
                 $ unTC m

tcLocal :: (TCEnv v -> TCEnv v') -> TC v' a -> TC v a
tcLocal f (TC (ReaderT m)) = TC (ReaderT (m . f))

data TCEnv v = TCEnv
    { _teContext       :: !(Ctx.ClosedCtx Type v)
    , _teCurrentSrcLoc :: !SrcLoc
    }

initEnv :: Closed TCEnv
initEnv = TCEnv
  { _teContext       = Ctx.Empty
  , _teCurrentSrcLoc = noSrcLoc
  }

data TCState = TCState
  { _tsSignature :: Map.Map Name (Definition Term)
  , _tsMetaStore :: Map.Map MetaVar MetaInst
  }

initState :: TCState
initState = TCState
  { _tsSignature = Map.empty
  , _tsMetaStore = Map.empty
  }

data MetaInst
    = Open (Closed Type)
    | Inst (Closed Type) (Closed Term)
--  deriving Show

data TCErr = TCErr SrcLoc String

instance Error TCErr where
  strMsg = TCErr noSrcLoc

instance Show TCErr where
  show (TCErr p s) = show p ++ ": " ++ s

typeError :: String -> TC v b
typeError err = do
  loc <- asks _teCurrentSrcLoc
  throwError $ TCErr loc err

atSrcLoc :: HasSrcLoc a => a -> TC v b -> TC v b
atSrcLoc x = local $ \env -> env { _teCurrentSrcLoc = srcLoc x }

-- Definitions operations
------------------------------------------------------------------------

addDefinition :: Name -> Definition Term -> TC v ()
addDefinition x def' =
    modify $ \s -> s { _tsSignature = Map.insert x def' $ _tsSignature s }

getDefinition :: Name -> TC v (Definition Term)
getDefinition name = atSrcLoc name $ do
  sig <- gets _tsSignature
  case Map.lookup name sig of
    Just def' -> return def'
    Nothing   -> typeError $ "definitionOf: Not in scope " ++ error "TODO definitionOf show name"

-- MetaVar operations
------------------------------------------------------------------------

addFreshMetaVar :: Type v -> TC v (Term v)
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

instantiateMetaVar :: MetaVar -> Closed Term -> TC v ()
instantiateMetaVar mv t = do
  mvInst <- getMetaInst mv
  mvType <- case mvInst of
      Inst _ _    -> typeError $ "instantiateMetaVar: already instantiated."
      Open mvType -> return mvType
  modify $ \s -> s { _tsMetaStore = Map.insert mv (Inst mvType t) (_tsMetaStore s) }

getTypeOfMetaVar :: MetaVar -> TC v (Closed Type)
getTypeOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst mvType _ -> mvType
      Open mvType   -> mvType

getBodyOfMetaVar :: MetaVar -> TC v (Maybe (Closed Term))
getBodyOfMetaVar mv = do
    mvInst <- getMetaInst mv
    return $ case mvInst of
      Inst _ mvBody -> Just mvBody
      Open _        -> Nothing

getMetaInst :: MetaVar -> TC v MetaInst
getMetaInst mv = do
  mbMvInst <- gets $ Map.lookup mv . _tsMetaStore
  case mbMvInst of
      Nothing     -> typeError $ "getMetaInst: non-existent meta " ++ show mv
      Just mvInst -> return mvInst

-- Operations on the context
------------------------------------------------------------------------

extendContext :: Name -> Type v
              -> (TermVar v -> Ctx.Ctx v Type (TermVar v) -> TC (TermVar v) a)
              -> TC v a
extendContext n type_ m =
    tcLocal extend (m (B (named n ())) (Ctx.singleton n type_))
  where
    extend env = env { _teContext = Ctx.Snoc (_teContext env) (n, type_) }

getTypeOfName :: Name -> TC v (v, Type v)
getTypeOfName n = do
    ctx <- asks _teContext
    case Ctx.lookupName n ctx of
      Nothing -> typeError $ "Name not in scope " ++ show n
      Just t  -> return t

getTypeOfVar :: v -> TC v (Type v)
getTypeOfVar v = do
    ctx <- asks _teContext
    return $ Ctx.getVar v ctx

-- TODO this looks very wrong here.  See if you can change the interface
-- to get rid of it.
closeClauseBody :: Term v -> TC v (ClauseBody Term)
closeClauseBody t = do
    ctx <- asks _teContext
    return $ Scope $ liftM (toIntVar ctx) t
  where
    toIntVar ctx v = B $ Ctx.elemIndex v ctx

------------------------------------------------------------------------
-- Term definition
------------------------------------------------------------------------

-- Term definition, if it was a typeclass:
--
-- class (Functor t, Monad t, Foldable t, Traversable t, ...) => Term t where
--     type TermAbs t :: * -> *
--
--     toAbs   :: t (TermVar v) -> TermAbs t v
--     fromAbs :: TermAbs t v -> t (TermVar v)
--
--     unview :: TermView (TermAbs t) t v -> t v
--     view   :: t v -> TermView (TermAbs t) t v
--
--     eliminate :: t v -> [Elim t v] -> t v
--
--     whnf :: t v -> TC v (t v)
--
--     instantiate :: TermAbs v -> t v -> t v
--
--     -- Method present if the abstraction supports a faster version.
--     weaken :: t v -> TermAbs v
--     weaken = toAbs . fmap F
--
-- So why are we not using this type class?  Because inference with type
-- families gets tricky.  I might get back to it at some point.

-- LazyScope term
-----------------

-- These term uses lazy evaluation and the classic bound 'Scope'.

newtype Term v =
    Term {unTerm :: TermView TermAbs Term v}
    deriving (Show, Eq, Functor, Foldable, Traversable, Eq1)

instance Show1 Term

instance Monad Term where
    return v = Term (App (Var v) [])

    Term term0 >>= f = Term $ case term0 of
        Lam body           -> Lam (TermAbs (unTermAbs body >>>= f))
        Pi domain codomain -> Pi (domain >>= f) (TermAbs (unTermAbs codomain >>>= f))
        Equal type_ x y    -> Equal (type_ >>= f) (x >>= f) (y >>= f)
        Set                -> Set
        App h elims        ->
            let elims' = map (>>>= f) elims
            in case h of
                   Var v   -> unTerm $ eliminate (f v) elims'
                   Def n   -> App (Def n)   elims'
                   Con n   -> App (Con n)   elims'
                   J       -> App J         elims'
                   Refl    -> App Refl      elims'
                   Meta mv -> App (Meta mv) elims'

instance (DeBruijn v) => PP.Pretty (Term v) where
    prettyPrec p (Term t) = PP.prettyPrec p t

newtype TermAbs v = TermAbs {unTermAbs :: Scope (Named ()) Term v}
    deriving (Functor, Traversable, Foldable, Eq1, Eq, Show, Show1)

toAbs :: Term (TermVar v) -> TermAbs v
toAbs = TermAbs . toScope

fromAbs :: TermAbs v -> Term (TermVar v)
fromAbs = fromScope . unTermAbs

unview :: TermView TermAbs Term v -> Term v
unview = Term

view :: Term v -> TermView TermAbs Term v
view = unTerm

instantiate :: TermAbs v -> Term v -> Term v
instantiate abs t = instantiate1 t (unTermAbs abs)

weaken :: Term v -> TermAbs v
weaken = TermAbs . Scope . return . F

-- | Tries to apply the eliminators to the term.  Trows an error when
-- the term and the eliminators don't match.
eliminate :: Term v -> [Elim Term v] -> Term v
eliminate (Term term0) elims = case (term0, elims) of
    (t, []) ->
        Term t
    (App (Con _c) args, Proj _ field : es) ->
        if unField field >= length args
        then error "Impl.Term.eliminate: Bad elimination"
        else case (args !! unField field) of
               Apply t -> eliminate t es
               _       -> error "Impl.Term.eliminate: Bad constructor argument"
    (Lam body, Apply argument : es) ->
        eliminate (instantiate body argument) es
    (App h es1, es2) ->
        Term $ App h (es1 ++ es2)
    (_, _) ->
        error "Impl.Term.eliminate: Bad elimination"

whnf :: Term v -> TC v (Term v)
whnf ls@(Term t) = case t of
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
    App J (_ : x : _ : _ : Apply p : Apply (Term (App Refl [])) : es) ->
        whnf $ eliminate p (x : es)
    _ ->
        return ls

whnfFun :: Term v -> [Elim Term v] -> [Clause Term] -> TC v (Term v)
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

matchClause :: [Elim Term v] -> [Pattern]
            -> MaybeT (TC v) ([Term v], [Elim Term v])
matchClause es [] =
    return ([], es)
matchClause (Apply arg : es) (VarP : patterns) = do
    (args, leftoverEs) <- matchClause es patterns
    return (arg : args, leftoverEs)
matchClause (Apply arg : es) (ConP dataCon dataConPatterns : patterns) = do
    Term (App (Con dataCon') dataConEs) <- lift $ whnf arg
    guard (dataCon == dataCon')
    matchClause (dataConEs ++ es) (dataConPatterns ++ patterns)
matchClause _ _ =
    mzero

-- Utils
------------------------------------------------------------------------

type Type = Term

-- Term
-------

lam :: TermAbs v -> Term v
lam body = unview $ Lam body

pi :: Term v -> TermAbs v -> Term v
pi domain codomain = unview $ Pi domain codomain

equal :: Term v -> Term v -> Term v -> Term v
equal type_ x y = unview $ Equal type_ x y

app :: Head v -> [Elim Term v] -> Term v
app h elims = unview $ App h elims

set :: Term v
set = unview Set

var :: v -> Term v
var v = unview (App (Var v) [])

metaVar :: MetaVar -> Term v
metaVar mv = unview (App (Meta mv) [])

def :: Name -> Term v
def f = unview (App (Def f) [])

con :: Name -> Term v
con c = unview (App (Con c) [])

refl :: Term v
refl = unview (App Refl [])

whnfView :: Term v -> TC v (TermView TermAbs Term v)
whnfView t = view <$> whnf t

-- Context
----------

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
ctxApp :: Type v -> Ctx.Ctx v0 Type v -> Type v
ctxApp t ctx0 = eliminate t $ map (Apply . var) $ reverse $ go ctx0
  where
    go :: Ctx.Ctx v0 Type v -> [v]
    go Ctx.Empty                    = []
    go (Ctx.Snoc ctx (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 't'.
ctxPi :: Ctx.Ctx v0 Type v -> Type v -> Type v0
ctxPi Ctx.Empty                  t = t
ctxPi (Ctx.Snoc ctx (_n, type_)) t = ctxPi ctx $ pi type_ (toAbs t)

-- Pretty printing
------------------

instance (DeBruijn v) => PP.Pretty (TermView TermAbs Term v) where
  prettyPrec p t = case t of
    Set ->
      PP.text "Set"
    Equal a x y ->
      PP.prettyApp p (PP.text "_==_") [a, x, y]
    Pi a b0 ->
      let b = fromAbs b0
          n = absName b
      in PP.condParens (p > 0) $
          PP.sep [ PP.parens (PP.pretty n <> PP.text " : " <> PP.pretty a) PP.<+>
                   PP.text "->"
                 , PP.nest 2 $ PP.pretty b
                 ]
    Lam b0 ->
      let b = fromAbs b0
          n = absName b
      in PP.condParens (p > 0) $
         PP.sep [ PP.text "\\" <> PP.pretty n <> PP.text " ->"
                , PP.nest 2 $ PP.pretty b
                ]
    App h es ->
      PP.prettyApp p (PP.pretty h) es

instance PP.Pretty (Definition Term) where
  prettyPrec _ _ = PP.text "TODO pretty Definition"
