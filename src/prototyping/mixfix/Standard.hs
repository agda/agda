------------------------------------------------------------------------
-- The standard backtracking parser combinators
------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             FlexibleInstances #-}

module Standard where

import Control.Monad.Trans
import Control.Monad.State
import qualified Parser
import Control.Applicative

newtype Parser tok r = P { unP :: StateT [ tok ] [] r }
  deriving (Functor, Monad)

instance Alternative (Parser tok) where
  empty         = P mzero
  P p1 <|> P p2 = P (mplus p1 p2)

instance Applicative (Parser tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

parse :: Parser tok r -> [ tok ] -> [ r ]
parse p xs =
  map fst . filter (null . snd) . flip runStateT xs . unP $ p

instance Ord tok => Parser.Parser (Parser tok) tok where
  sym c = P $ do
    cs <- get
    case cs of
      c' : cs | c == c' -> do
        put cs
        return c' 
      _ -> mzero
  parse = parse
