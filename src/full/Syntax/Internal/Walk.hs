{-# OPTIONS -fglasgow-exts #-}

module Syntax.Internal.Walk where

import Control.Monad.Reader
import Control.Monad.Writer
import Data.Generics
import Data.Monoid

import Syntax.Internal

type WalkT m = ReaderT Int (WriterT WalkDone m)

-- | Check if given term is an abstraction.
--
isAbs :: Data a => a -> Bool
isAbs x = dataTypeName (dataTypeOf x) == dataTypeName (dataTypeOf (Abs undefined ()))

-- | Apply @f@ everywhere in a term, until told not to. 
--   Local reader state keeps track of how many binders have been passed.
--   Writer output lets @walk@ know whether to continue the traversal after
--     applying the function.
--   Might want to add some way to not traverse explanations (with something like 
--     @isabs@ above).
--
walk :: Monad m => GenericM (WalkT m) -> GenericM m
walk f x = do
    (v, _) <- runWriterT $ runReaderT (go f x) 0
    return v 
  where
    go :: Monad m => GenericM (WalkT m) -> GenericM (WalkT m)
    go f x = do
        (v, continue) <- listen $ f x
        case continue of
            Done     -> return v
            Continue -> 
                if isAbs x then local (+ 1) $ gmapM (go f) v 
		else gmapM (go f) v

data WalkDone = Done | Continue 
instance Monoid WalkDone where
    mempty	       = Continue
    mappend Continue x = x
    mappend Done     _ = Done

-- | @endWalk@ is used, instead of @return@, by a traversal function 
--     which wants to stop the term traversal.
--   If traversal function wants to continue traversal, then @return@
--     is used instead.
--
endWalk :: Monad m => a -> WalkT m a
endWalk x = do tell Done; return x


