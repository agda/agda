
{-| EDSL to construct terms without touching De Bruijn indices.

e.g. given t, u :: Term, Γ ⊢ t, u : A, we can build "λ f. f t u" like this:

runNames [] $ do
  -- @open@ binds @t@ and @u@ to computations that know how to weaken themselves in
  -- an extended context

  [t,u] <- mapM open [t,u]

  -- @lam@ gives the illusion of HOAS by providing f as a computation.
  -- It also extends the internal context with the name "f", so that
  -- @t@ and @u@ will get weakened in the body.
  -- We apply f with the (<@>) combinator from Agda.TypeChecking.Primitive.

  lam "f" $ \ f -> f <@> t <@> u

-}
module Agda.TypeChecking.Names where

-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)

import Control.Monad          ( liftM2, unless )
import Control.Monad.Except   ( MonadError )
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.Reader   ( MonadReader(..), ReaderT, runReaderT )
import Control.Monad.State    ( MonadState )
import Control.Monad.Trans    ( MonadTrans, lift )

import Data.List              ( isSuffixOf )

import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Level
import Agda.TypeChecking.Pretty ()  -- instances only
import Agda.TypeChecking.Free

import Agda.Utils.Fail (Fail, runFail_)
import Agda.Utils.Impossible

instance HasBuiltins m => HasBuiltins (NamesT m) where
  getBuiltinThing b = lift $ getBuiltinThing b

newtype NamesT m a = NamesT { unName :: ReaderT Names m a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadFail
           , MonadTrans
           , MonadState s
           , MonadIO
           , HasOptions
           , MonadDebug
           , MonadTCEnv
           , MonadTCState
           , MonadTCM
           , ReadTCState
           , MonadReduce
           , MonadError e
           , MonadAddContext
           , HasConstInfo
           , PureTCM
           )


-- | A list of variable names from a context.
type Names = [String]

runNamesT :: Names -> NamesT m a -> m a
runNamesT n m = runReaderT (unName m) n

runNames :: Names -> NamesT Fail a -> a
runNames n m = runFail_ (runNamesT n m)

currentCxt :: Monad m => NamesT m Names
currentCxt = NamesT ask

-- | @cxtSubst Γ@ returns the substitution needed to go
--   from Γ to the current context.
--
--   Fails if @Γ@ is not a subcontext of the current one.
cxtSubst :: MonadFail m => Names -> NamesT m (Substitution' a)
cxtSubst ctx = do
  ctx' <- currentCxt
  if (ctx `isSuffixOf` ctx')
     then return $ raiseS (length ctx' - length ctx)
     else fail $ "out of context (" ++ show ctx ++ " is not a sub context of " ++ show ctx' ++ ")"

-- | @inCxt Γ t@ takes a @t@ in context @Γ@ and produce an action that
--   will return @t@ weakened to the current context.
--
--   Fails whenever @cxtSubst Γ@ would.
inCxt :: (MonadFail m, Subst a) => Names -> a -> NamesT m a
inCxt ctx a = do
  sigma <- cxtSubst ctx
  return $ applySubst sigma a

-- | Closed terms
cl' :: Applicative m => a -> NamesT m a
cl' = pure

cl :: Monad m => m a -> NamesT m a
cl = lift

-- | Open terms in the current context.
open :: (MonadFail m, Subst a) => a -> NamesT m (NamesT m a)
open a = do
  ctx <- NamesT ask
  pure $ inCxt ctx a

-- | Monadic actions standing for variables.
--
--   @b@ is quantified over so the same variable can be used e.g. both
--   as a pattern and as an expression.
type Var m = forall b. (Subst b, DeBruijn b) => NamesT m b


-- | @bind n f@ provides @f@ with a fresh variable, which can be used in any extended context.
--
--   Returns an @Abs@ which binds the extra variable.
bind :: MonadFail m => ArgName -> ((forall b. (Subst b, DeBruijn b) => NamesT m b) -> NamesT m a) -> NamesT m (Abs a)
bind n f = Abs n <$> bind' n f

-- | Like @bind@ but returns a bare term.
bind' :: MonadFail m => ArgName -> ((forall b. (Subst b, DeBruijn b) => NamesT m b) -> NamesT m a) -> NamesT m a
bind' n f = do
  cxt <- NamesT ask
  (NamesT . local (n:) . unName $ f (inCxt (n:cxt) (deBruijnVar 0)))


-- * Helpers to build lambda abstractions.

glam :: MonadFail m
     => ArgInfo -> ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
glam info n f = Lam info <$> bind n (\ x -> f x)

lam :: MonadFail m
    => ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
lam n f = glam defaultArgInfo n f

ilam :: MonadFail m
    => ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
ilam n f = glam (setRelevance Irrelevant defaultArgInfo) n f


-- * Combinators for n-ary binders.

data AbsN a = AbsN { absNName :: [ArgName], unAbsN :: a } deriving (Functor,Foldable,Traversable)

instance Subst a => Subst (AbsN a) where
  type SubstArg (AbsN a) = SubstArg a
  applySubst rho (AbsN xs a) = AbsN xs (applySubst (liftS (length xs) rho) a)

-- | Will crash on @NoAbs@
toAbsN :: Abs (AbsN a) -> AbsN a
toAbsN (Abs n x') = AbsN (n : absNName x') (unAbsN x')
toAbsN NoAbs{}    = __IMPOSSIBLE__

absAppN :: Subst a => AbsN a -> [SubstArg a] -> a
absAppN f xs = (parallelS $ reverse xs) `applySubst` unAbsN f

type ArgVars m = (forall b. (Subst b, DeBruijn b) => [NamesT m (Arg b)])

type Vars m = (forall b. (Subst b, DeBruijn b) => [NamesT m b])

bindN :: ( MonadFail m
        ) =>
        [ArgName] -> (Vars m -> NamesT m a) -> NamesT m (AbsN a)
bindN [] f = AbsN [] <$> f []
bindN (x:xs) f = toAbsN <$> bind x (\ x -> bindN xs (\ xs -> f (x:xs)))

bindNArg :: ( MonadFail m
        ) =>
        [Arg ArgName] -> (ArgVars m -> NamesT m a) -> NamesT m (AbsN a)
bindNArg [] f = AbsN [] <$> f []
bindNArg (Arg i x:xs) f = toAbsN <$> bind x (\ x -> bindNArg xs (\ xs -> f ((Arg i <$> x):xs)))


glamN :: (Functor m, MonadFail m) =>
         [Arg ArgName] -> (NamesT m Args -> NamesT m Term) -> NamesT m Term
glamN [] f = f $ pure []
glamN (Arg i n:ns) f = glam i n $ \ x -> glamN ns (\ xs -> f ((:) <$> (Arg i <$> x) <*> xs))


applyN :: ( Monad m
        , Subst a
        ) =>
        NamesT m (AbsN a) -> [NamesT m (SubstArg a)] -> NamesT m a
applyN f xs = do
  f <- f
  xs <- sequence xs
  unless (length xs == length (absNName f)) $ __IMPOSSIBLE__
  return $ absAppN f xs

applyN' :: ( Monad m
        , Subst a
        ) =>
        NamesT m (AbsN a) -> NamesT m [SubstArg a] -> NamesT m a
applyN' f xs = do
  f <- f
  xs <- xs
  unless (length xs == length (absNName f)) $ __IMPOSSIBLE__
  return $ absAppN f xs

abstractN :: ( MonadFail m
             , Abstract a
             ) =>
             NamesT m Telescope -> (Vars m -> NamesT m a) -> NamesT m a
abstractN tel f = do
  tel <- tel
  u <- bindN (teleNames tel) f
  return $ abstract tel $ unAbsN u

abstractT :: ( MonadFail m
             , Abstract a
             ) =>
             String -> NamesT m Type -> (Var m -> NamesT m a) -> NamesT m a
abstractT n ty f = do
  u <- bind n f
  ty <- ty
  let tel = ExtendTel (defaultDom ty) $ Abs n EmptyTel
  return $ abstract tel $ unAbs u


lamTel :: Monad m => NamesT m (Abs [Term]) -> NamesT m ([Term])
lamTel t = map (Lam defaultArgInfo) . sequenceA <$> t

appTel :: Monad m => NamesT m [Term] -> NamesT m Term -> NamesT m [Term]
appTel = liftM2 (\ fs x -> map (`apply` [Arg defaultArgInfo x]) fs)
