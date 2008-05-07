------------------------------------------------------------------------
-- Transforms Parsers to NTParsers
------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses,
             UndecidableInstances #-}

module NTTrans where

import Parser
import Control.Applicative

newtype NTTrans p nt r =
  NTTrans { unNTTrans :: Grammar (NTTrans p nt) nt -> p r }

instance Functor p => Functor (NTTrans p nt) where
  fmap f (NTTrans m) = NTTrans $ fmap f . m

instance Monad p => Monad (NTTrans p nt) where
  return x        = NTTrans $ \_ -> return x
  NTTrans m >>= f = NTTrans $ \g -> m g >>= \x -> unNTTrans (f x) g

instance Applicative p => Applicative (NTTrans p nt) where
  pure x                    = NTTrans $ \_ -> pure x
  NTTrans m1 <*> NTTrans m2 = NTTrans $ \g -> m1 g <*> m2 g

instance Alternative p => Alternative (NTTrans p nt) where
  empty                     = NTTrans $ \_ -> empty
  NTTrans m1 <|> NTTrans m2 = NTTrans $ \g -> m1 g <|> m2 g

instance Parser p tok => Parser (NTTrans p nt) tok where
  symbol = NTTrans $ \_ -> symbol

instance Parser p tok => NTParser (NTTrans p nt) nt tok where
  nonTerm x = NTTrans $ \g -> unNTTrans (g x) g

parse :: Parser p tok =>
         (p r -> [tok] -> [r]) ->
         Grammar (NTTrans p nt) nt ->
         (nt r -> [tok] -> [r])
parse parse' g x = parse' (unNTTrans (nonTerm x) g)
