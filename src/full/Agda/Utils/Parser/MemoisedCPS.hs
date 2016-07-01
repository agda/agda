------------------------------------------------------------------------
-- | Parser combinators with support for left recursion, following
-- Johnson\'s \"Memoization in Top-Down Parsing\".
--
-- This implementation is based on an implementation due to Atkey
-- (attached to an edlambda-members mailing list message from
-- 2011-02-15 titled \'Slides for \"Introduction to Parser
-- Combinators\"\').
--
-- Note that non-memoised left recursion is not guaranteed to work.
--
-- The code contains an important deviation from Johnson\'s paper: the
-- check for subsumed results is not included. This means that one can
-- get the same result multiple times when parsing using ambiguous
-- grammars. As an example, parsing the empty string using @S ∷= ε |
-- ε@ succeeds twice. This change also means that parsing fails to
-- terminate for some cyclic grammars that would otherwise be handled
-- successfully, such as @S ∷= S | ε@. However, the library is not
-- intended to handle infinitely ambiguous grammars. (It is unclear to
-- the author of this module whether the change leads to more
-- non-termination for grammars that are not cyclic.)

{-# LANGUAGE CPP                   #-}

module Agda.Utils.Parser.MemoisedCPS
  ( ParserClass(..)
  , Parser
  , ParserWithGrammar
  ) where

import Control.Applicative
import Control.Monad (ap, liftM2)
import Control.Monad.State.Strict (State, evalState, get, put)
import Data.Array
import Data.Hashable
import qualified Data.HashMap.Strict as Map
import Data.HashMap.Strict (HashMap)
import qualified Data.HashSet as Set
import Data.HashSet (HashSet)
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import Data.List
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP

import Agda.Utils.Monad (modify')

#include "undefined.h"
import Agda.Utils.Impossible

-- | Positions.

type Pos = Int

-- | State monad used by the parser.

type M k r tok b = State (IntMap (HashMap k (Value k r tok b)))

-- | Continuations.

type Cont k r tok b a = Pos -> a -> M k r tok b [b]

-- | Memoised values.

data Value k r tok b = Value
  { results       :: !(IntMap [r])
  , continuations :: [Cont k r tok b r]
  }

-- | The parser type.
--
-- The parameters of the type @Parser k r tok a@ have the following
-- meanings:
--
-- [@k@] Type used for memoisation keys.
--
-- [@r@] The type of memoised values. (Yes, all memoised values have
-- to have the same type.)
--
-- [@tok@] The token type.
--
-- [@a@] The result type.

newtype Parser k r tok a =
  P { unP :: forall b.
             Array Pos tok ->
             Pos ->
             Cont k r tok b a ->
             M k r tok b [b]
    }

instance Monad (Parser k r tok) where
  return    = pure
  P p >>= f = P $ \input i k ->
    p input i $ \j x -> unP (f x) input j k

instance Functor (Parser k r tok) where
  fmap f p = p >>= return . f

instance Applicative (Parser k r tok) where
  pure x = P $ \_ i k -> k i x
  (<*>)  = ap

instance Alternative (Parser k r tok) where
  empty         = P $ \_ _ _ -> return []
  P p1 <|> P p2 = P $ \input i k ->
    liftM2 (++) (p1 input i k) (p2 input i k)

class (Functor p, Applicative p, Alternative p, Monad p) =>
      ParserClass p k r tok | p -> k, p -> r, p -> tok where
  -- | Runs the parser.
  parse :: p a -> [tok] -> [a]

  -- | Tries to print the parser, or returns 'PP.empty', depending on
  -- the implementation. This function might not terminate.
  grammar :: p a -> Doc

  -- | Parses a single token.
  token :: p tok

  -- | Parses a token satisfying the given predicate.
  sat :: (tok -> Bool) -> p tok

  -- | Parses a given token.
  tok :: (Eq tok, Show tok) => tok -> p tok

  -- | Uses the given function to modify the printed representation
  -- (if any) of the given parser.
  annotate :: (Doc -> Doc) -> p a -> p a

  -- | Memoises the given parser.
  --
  -- Every memoised parser must be annotated with a /unique/ key.
  -- (Parametrised parsers must use distinct keys for distinct
  -- inputs.)
  memoise :: (Eq k, Hashable k, Show k) => k -> p r -> p r

  -- | Memoises the given parser, but only if printing, not if
  -- parsing.
  --
  -- Every memoised parser must be annotated with a /unique/ key.
  -- (Parametrised parsers must use distinct keys for distinct
  -- inputs.)
  memoiseIfPrinting :: (Eq k, Hashable k, Show k) => k -> p r -> p r

instance ParserClass (Parser k r tok) k r tok where
  parse p toks =
    flip evalState IntMap.empty $
    unP p (listArray (0, n - 1) toks) 0 $ \j x ->
      if j == n then return [x] else return []
    where n = genericLength toks

  grammar _ = PP.empty

  token = P $ \input i k ->
    if inRange (bounds input) i then
      (k $! (i + 1)) $! (input ! i)
    else
      return []

  sat p = do
    t <- token
    if p t then return t else empty

  tok t = sat (t ==)

  annotate _ p = p

  memoiseIfPrinting _ p = p

  memoise key p = P $ \input i k -> do

    let alter j zero f m =
          IntMap.alter (Just . f . maybe zero id) j m

        lookupTable   = fmap (\m -> Map.lookup key =<<
                                    IntMap.lookup i m) get
        insertTable v = modify' $ alter i Map.empty (Map.insert key v)

    v <- lookupTable
    case v of
      Nothing -> do
        insertTable (Value IntMap.empty [k])
        unP p input i $ \j r -> do
          Just (Value rs ks) <- lookupTable
          insertTable (Value (alter j [] (r :) rs) ks)
          concat <$> mapM (\k -> k j r) ks  -- See note [Reverse ks?].
      Just (Value rs ks) -> do
        insertTable (Value rs (k : ks))
        concat . concat <$>
          mapM (\(i, rs) -> mapM (k i) rs) (IntMap.toList rs)

-- [Reverse ks?]
--
-- If ks were reversed, then the code would be productive for some
-- infinitely ambiguous grammars, including S ∷= S | ε. However, in
-- some cases the results would not be fair (some valid results would
-- never be returned).

-- | An extended parser type, with some support for printing parsers.

data ParserWithGrammar k r tok a =
  PG (Bool -> Either (Parser k r tok a)
                     (State (HashSet k) Doc))
  -- ^ Invariant: If the boolean is 'True', then the result must be
  -- @'Left' something@, and if the boolean is 'False', then the
  -- result must be @'Right' something@.

-- | A smart constructor.

pg :: Parser k r tok a ->
      State (HashSet k) Doc ->
      ParserWithGrammar k r tok a
pg p d = PG $ \b -> if b then Left p else Right d

-- | Extracts the parser.

parser :: ParserWithGrammar k r tok a -> Parser k r tok a
parser (PG p) = either id __IMPOSSIBLE__ (p True)

-- | Extracts the document.

doc :: ParserWithGrammar k r tok a -> State (HashSet k) Doc
doc (PG p) = either __IMPOSSIBLE__ id (p False)

instance Monad (ParserWithGrammar k r tok) where
  return  = pure
  p >>= f = pg (parser p >>= parser . f)
               ((\d -> parens (d <+> text ">>= ?")) <$> doc p)

instance Functor (ParserWithGrammar k r tok) where
  fmap f p = pg (fmap f (parser p)) (doc p)

instance Applicative (ParserWithGrammar k r tok) where
  pure x    = pg (pure x) (return (text "ε"))
  p1 <*> p2 =
    pg (parser p1 <*> parser p2)
       (liftM2 (\d1 d2 -> parens (sep [d1, d2])) (doc p1) (doc p2))

instance Alternative (ParserWithGrammar k r tok) where
  empty     = pg empty (return (text "∅"))
  p1 <|> p2 =
    pg (parser p1 <|> parser p2)
       (liftM2 (\d1 d2 -> parens (sep [d1, text "|", d2])) (doc p1) (doc p2))

  many p = pg (many (parser p)) ((<+> text "⋆") . parens <$> doc p)
  some p = pg (some (parser p)) ((<+> text "+") . parens <$> doc p)

-- | A helper function.

memoiseDoc ::
  (Eq k, Hashable k, Show k) =>
  k -> ParserWithGrammar k r tok r -> State (HashSet k) Doc
memoiseDoc key p = do
  s <- get
  if Set.member key s then
    return (text ("<" ++ show key ++ ">"))
   else do
    put (Set.insert key s)
    (\d -> parens $
             text ("μ " ++ show key ++ ".") $+$ nest 2 d) <$>
      doc p

instance ParserClass (ParserWithGrammar k r tok) k r tok where
  parse p                 = parse (parser p)
  grammar p               = evalState (doc p) Set.empty
  token                   = pg token (return (text "·"))
  sat p                   = pg (sat p) (return (text "sat ?"))
  tok t                   = pg (tok t) (return (text (show t)))
  annotate f p            = pg (parser p) (f <$> doc p)
  memoise key p           = pg (memoise key (parser p))
                               (memoiseDoc key p)
  memoiseIfPrinting key p = pg (parser p) (memoiseDoc key p)
