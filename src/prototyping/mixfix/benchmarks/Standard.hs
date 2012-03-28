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

newtype Parser k r' tok r = P { unP :: StateT [ tok ] [] r }
  deriving (Functor, Monad)

instance Alternative (Parser k r' tok) where
  empty         = P mzero
  P p1 <|> P p2 = P (mplus p1 p2)

instance Applicative (Parser k r' tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

parse :: Parser k r' tok r -> [ tok ] -> [ r ]
parse p xs =
  map fst . filter (null . snd) . flip runStateT xs . unP $ p

instance Parser.Parser (Parser k r' tok) k r' tok where
  sym c = P $ do
    cs <- get
    case cs of
      c' : cs | c == c' -> do
        put cs
        return c'
      _ -> mzero
