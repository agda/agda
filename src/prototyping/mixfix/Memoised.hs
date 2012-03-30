------------------------------------------------------------------------
-- A memoising variant of the standard backtracking parser combinators
------------------------------------------------------------------------

-- Following Frost/Szydlowski and Frost/Hafiz/Callaghan (but without
-- the left recursion fix). An improvement has been made: The user
-- does not have to insert memoisation annotations manually. Instead
-- all grammar non-terminals are memoised. This is perhaps a bit less
-- flexible, but less error-prone, since there is no need to guarantee
-- that all "keys" (arguments to the memoise combinator) are unique.

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}

module Memoised where

import Control.Monad.State.Strict
import Control.Applicative
import qualified IndexedMap as IMap
import Control.Arrow
import IndexedOrd
import qualified Parser

-- | Positions.

type Pos = Integer

-- | Lists annotated with positions.

type AnnList tok = [ (Pos, tok) ]

-- | Keys used by the memoisation code. 'Nothing' is used to indicate
-- the end of the input.

data Key nt r = Key (nt r) (Maybe Pos)

instance IndexedEq nt => IndexedEq (Key nt) where
  iEq (Key x1 y1) (Key x2 y2) = case (y1 == y2, iEq x1 x2) of
    (True, Just eq) -> Just eq
    _               -> Nothing

instance IndexedOrd nt => IndexedOrd (Key nt) where
  iCompare (Key x1 y1) (Key x2 y2) = case compare y1 y2 of
    LT -> LT
    EQ -> iCompare x1 x2
    GT -> GT

-- | Memoised values.

newtype Value tok r = Value [(r, AnnList tok)]

-- | The parser type.

-- I did not replace the first function space with a reader monad
-- since the type checker had trouble handling the rank-2 argument
-- type (Parser.Grammar ...).

newtype Parser nt tok r =
  P { unP :: Parser.Grammar (Parser nt tok) nt ->
             AnnList tok ->
             State (IMap.Map (Key nt) (Value tok)) [(r, AnnList tok)] }

instance Functor (Parser nt tok) where
  fmap f (P p) = P $ \g input -> fmap (map (f *** id)) (p g input)

instance Monad (Parser nt tok) where
  return x  = P $ \_ input -> return [(x, input)]
  P p >>= f = P $ \g input -> do
    rs <- p g input
    fmap concat $ mapM (\(x, toks) -> unP (f x) g toks) rs

instance Applicative (Parser nt tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

instance Alternative (Parser nt tok) where
  empty         = P $ \_ _     -> return empty
  P p1 <|> P p2 = P $ \g input -> liftM2 (<|>) (p1 g input) (p2 g input)

parse :: Parser.Grammar (Parser nt tok) nt ->
         Parser nt tok r -> [tok] -> [r]
parse g p toks =
  map fst .
  filter (null . snd) .
  flip evalState IMap.empty $
  unP p g (zip [1 ..] toks)

instance Parser.Parser (Parser nt tok) tok where
  symbol = P $ \_ input -> return $
    case input of
      (_, c) : cs -> return (c, cs)
      _           -> empty

  parse = parse (const empty)

-- | Non-terminals are memoised.

instance Parser.NTParser (Parser nt tok) nt tok where
  nonTerm x = P $ \grammar input -> do
    let key = Key x (case input of
                       (pos, _) : _ -> Just pos
                       []           -> Nothing)
    res' <- lookupTable key
    case res' of
      Just (Value v) -> return v
      Nothing        -> do
        rs <- unP (grammar x) grammar input
        modifyTable (IMap.insert key (Value rs))
        return rs
    where
    lookupTable k = fmap (IMap.lookup k) get
    modifyTable f = modify f

  parseWithGrammar = parse
