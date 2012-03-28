------------------------------------------------------------------------
-- A wrapper around ReadP
------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             FlexibleInstances #-}

module ReadPWrapper where

import qualified ReadP
import Control.Monad
import qualified Control.Applicative as A
import qualified Parser

newtype ReadP k r' tok r = R { unR :: ReadP.ReadP tok r }
  deriving (Functor, Monad, MonadPlus)

instance A.Applicative (ReadP k r' tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> p2 >>= \x -> return (f x)

instance A.Alternative (ReadP k r' tok) where
  empty = mzero
  (<|>) = mplus

parse :: ReadP k r' tok r -> [ tok ] -> [ r ]
parse = ReadP.parse . unR

instance Parser.Parser (ReadP k r' tok) k r' tok where
  sym                  = R . ReadP.char

  choice               = R . ReadP.choice . map unR
  many1                = R . ReadP.many1 . unR
  chainr1 (R p) (R op) = R $ ReadP.chainr1 p op
  chainl1 (R p) (R op) = R $ ReadP.chainl1 p op
