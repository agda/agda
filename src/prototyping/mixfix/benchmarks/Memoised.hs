------------------------------------------------------------------------
-- A memoising variant of the standard backtracking parser combinators
------------------------------------------------------------------------

-- Following Frost/Szydlowski and Frost/Hafiz/Callaghan (but without
-- the left recursion fix).

-- Note that the user has to insert "memoise" annotations manually.

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Memoised where

import Control.Monad.Trans
import Control.Monad.State.Strict
import qualified Parser
import Control.Applicative
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Arrow

-- | Positions.

type Pos = Integer

-- | Lists annotated with positions.

type AnnList tok = [ (Pos, tok) ]

-- | The state used below.

type S k r' tok = Map (k, Maybe Pos) [(r', AnnList tok)]

newtype Parser k r' tok r =
  P { unP :: AnnList tok -> State (S k r' tok) [(r, AnnList tok)] }

lookupTable k = fmap (Map.lookup k) get
modifyTable f = modify f

instance Functor (Parser k r' tok) where
  fmap f (P p) = P $ fmap (map (f *** id)) . p

instance Monad (Parser k r' tok) where
  return x  = P $ \input -> return [(x, input)]
  P p >>= f = P $ \input -> do
    rs <- p input
    fmap concat $ mapM (uncurry $ unP . f) rs

instance Applicative (Parser k r' tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

instance Alternative (Parser k r' tok) where
  empty         = P $ \_     -> return empty
  P p1 <|> P p2 = P $ \input -> liftM2 (<|>) (p1 input) (p2 input)

parse :: Parser k r' tok r -> [ tok ] -> [ r ]
parse p xs =
  map fst .
  filter (null . snd) .
  flip evalState Map.empty $
  unP p (zip [1 ..] xs)

instance Parser.Parser (Parser k r' tok) k r' tok where
  sym c = P $ \input -> return $
    case input of
      (_, c') : cs | c == c' -> return (c', cs)
      _                      -> empty

  memoise k (P p) = P $ \input -> do
    let key = (k, case input of
                    (pos, _) : _ -> Just pos
                    []           -> Nothing)
    res' <- lookupTable key
    case res' of
      Just res -> return res
      Nothing  -> do
        rs <- p input
        modifyTable (Map.insert key rs)
        return rs
