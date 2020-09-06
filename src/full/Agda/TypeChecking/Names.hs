{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| EDSL to construct terms without touching De Bruijn indices.

e.g. if given t, u :: Term, Γ ⊢ t, u : A, we can build "λ f. f t u" like this:

runNames [] $ do
  -- @open@ binds @t@ and @u@ to computations that know how to weaken themselves in
  -- an extended context

  [t,u] <- mapM open [t,u]

  -- @lam@ gives the illusion of HOAS by providing f as a computation
  -- It also extends the internal context with the name "f", so that
  -- @t@ and @u@ will get weakened in the body.
  -- Then we finish the job using the (<@>) combinator from Agda.TypeChecking.Primitive

  lam "f" $ \ f -> f <@> t <@> u

-}
module Agda.TypeChecking.Names where

-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.List

import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free

import Agda.Utils.Fail (Fail, runFail_)

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
           )

-- deriving instance MonadState s m => MonadState s (NamesT m)

type Names = [String]

runNamesT :: Names -> NamesT m a -> m a
runNamesT n m = runReaderT (unName m) n

-- We use @Fail@ instead of @Identity@ because the computation can fail.
runNames :: Names -> NamesT Fail a -> a
runNames n m = runFail_ (runNamesT n m)

currentCxt :: Monad m => NamesT m Names
currentCxt = NamesT ask

cxtSubst :: MonadFail m => Names -> NamesT m (Substitution' a)
cxtSubst ctx = do
  ctx' <- currentCxt
  if (ctx `isSuffixOf` ctx')
     then return $ raiseS (genericLength ctx' - genericLength ctx)
     else fail $ "thing out of context (" ++ show ctx ++ " is not a sub context of " ++ show ctx' ++ ")"

inCxt :: (MonadFail m, Subst a) => Names -> a -> NamesT m a
inCxt ctx a = do
  sigma <- cxtSubst ctx
  return $ applySubst sigma a

-- closed terms
cl' :: Applicative m => a -> NamesT m a
cl' = pure

cl :: Monad m => m a -> NamesT m a
cl = lift

open :: (MonadFail m, Subst a) => a -> NamesT m (NamesT m a)
open a = do
  ctx <- NamesT ask
  pure $ inCxt ctx a

bind' :: (MonadFail m, Subst b, DeBruijn b, Subst a, Free a) => ArgName -> (NamesT m b -> NamesT m a) -> NamesT m a
bind' n f = do
  cxt <- NamesT ask
  (NamesT . local (n:) . unName $ f (inCxt (n:cxt) (deBruijnVar 0)))

bind :: ( MonadFail m
        , Subst b
        , DeBruijn b
        , Subst a
        , Free a
        ) =>
        ArgName -> (NamesT m b -> NamesT m a) -> NamesT m (Abs a)
bind n f = Abs n <$> bind' n f

glam :: MonadFail m
     => ArgInfo -> ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
glam info n f = Lam info <$> bind n f

glamN :: (Functor m, MonadFail m) =>
         [Arg ArgName] -> (NamesT m Args -> NamesT m Term) -> NamesT m Term
glamN [] f = f $ pure []
glamN (Arg i n:ns) f = glam i n $ \ x -> glamN ns (\ xs -> f ((:) <$> (Arg i <$> x) <*> xs))

lam :: MonadFail m
    => ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
lam n f = glam defaultArgInfo n f

ilam :: MonadFail m
    => ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
ilam n f = glam (setRelevance Irrelevant defaultArgInfo) n f
