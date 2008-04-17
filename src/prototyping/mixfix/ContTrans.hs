------------------------------------------------------------------------
-- A continuation transformer
------------------------------------------------------------------------

{-# LANGUAGE Rank2Types, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances #-}

module ContTrans where

import Control.Applicative
import Control.Monad
import qualified Parser

newtype ContTrans p r =
  P { unP :: forall r'. (r -> p r') -> p r' }

instance Functor (ContTrans p) where
  fmap f (P p) = P (\k -> p (k . f))

instance Monad (ContTrans p) where
  return x  = P (\k -> k x)
  P p >>= f = P (\k -> p (\x -> unP (f x) k))

instance Applicative (ContTrans p) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

instance Alternative p => Alternative (ContTrans p) where
  empty         = P (\_ -> empty)
  P p1 <|> P p2 = P (\k -> p1 k <|> p2 k)

parse :: Monad p =>
         (p r -> [tok] -> [r]) ->
         (ContTrans p r -> [tok] -> [r])
parse parse' (P p) = parse' (p return)

instance (Monad p, Alternative p, Parser.Parser p k r' tok) =>
         Parser.Parser (ContTrans p) k r' tok where
  sym c = P (\k -> Parser.sym c >>= k)
