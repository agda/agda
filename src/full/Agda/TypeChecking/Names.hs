{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE UndecidableInstances       #-}

{-| Primitive functions, such as addition on builtin integers.
-}
module Agda.TypeChecking.Names where

import Control.Monad
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans

import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Data.Traversable (traverse)
import Data.Monoid (mempty)

import Agda.Interaction.Options

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Nat)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty ()

import Agda.TypeChecking.Monad hiding (getConstInfo, typeOfConst)
import qualified Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Reduce.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Level
import Agda.TypeChecking.Quote (QuotingKit, quoteTermWithKit, quoteTypeWithKit, quoteClauseWithKit, quotingKit)
import Agda.TypeChecking.Pretty ()  -- instances only
import Agda.TypeChecking.Free

import Agda.Utils.Monad
import Agda.Utils.Pretty (pretty)
import Agda.Utils.String ( Str(Str), unStr )
import Agda.Utils.Maybe

#include "undefined.h"
import Agda.Utils.Impossible
import Debug.Trace

instance HasBuiltins m => HasBuiltins (NamesT m) where
  getBuiltinThing b = lift $ getBuiltinThing b

newtype NamesT m a = NamesT { unName :: ReaderT Names m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, HasOptions)

deriving instance MonadState s m => MonadState s (NamesT m)

type Names = [String]

runNamesT :: Names -> NamesT m a -> m a
runNamesT n m = runReaderT (unName m) n

runNames :: Names -> NamesT Identity a -> a
runNames n m = runIdentity (runNamesT n m)

inCxt :: (Monad m, Subst t a) => Names -> a -> NamesT m a
inCxt ctx a = do
  ctx' <- NamesT ask
  if (ctx `isSuffixOf` ctx')
     then return $ raise (genericLength ctx' - genericLength ctx) a
     else fail $ "thing out of context (" ++ show ctx ++ " is not a sub context of " ++ show ctx' ++ ")"


-- closed terms
cl' :: Applicative m => a -> NamesT m a
cl' = pure

cl :: Monad m => m a -> NamesT m a
cl = lift

open :: ( Monad m
#if __GLASGOW_HASKELL__ <= 708
        , Applicative m
#endif
        , Subst t a
        ) => a -> NamesT m (NamesT m a)
open a = do
  ctx <- NamesT ask
  pure $ inCxt ctx a

bind' :: (Monad m, Subst t' b, DeBruijn b, Subst t a, Free a) => ArgName -> (NamesT m b -> NamesT m a) -> NamesT m a
bind' n f = do
  cxt <- NamesT ask
  (NamesT . local (n:) . unName $ f (inCxt (n:cxt) (deBruijnVar 0)))

bind :: ( Monad m
#if __GLASGOW_HASKELL__ <= 708
        , Functor m
#endif
        , Subst t' b
        , DeBruijn b
        , Subst t a
        , Free a
        ) =>
        ArgName -> (NamesT m b -> NamesT m a) -> NamesT m (Abs a)
bind n f = mkAbs n <$> bind' n f

#if __GLASGOW_HASKELL__ <= 708
glam :: (Functor m, Monad m)
#else
glam :: Monad m
#endif
     => ArgInfo -> ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
glam info n f = Lam info <$> bind n f

#if __GLASGOW_HASKELL__ <= 708
lam :: (Functor m, Monad m)
#else
lam :: Monad m
#endif
    => ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
lam n f = glam defaultArgInfo n f

#if __GLASGOW_HASKELL__ <= 708
ilam :: (Functor m, Monad m)
#else
ilam :: Monad m
#endif
    => ArgName -> (NamesT m Term -> NamesT m Term) -> NamesT m Term
ilam n f = glam (setRelevance Irrelevant defaultArgInfo) n f


instance MonadTCM m => MonadTCM (NamesT m) where
   liftTCM = lift . liftTCM

instance MonadReader r m => MonadReader r (NamesT m) where
  ask = lift ask
  local f (NamesT m) = NamesT $ mapReaderT (local f) m
