{-# OPTIONS_GHC -Wunused-imports #-}

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


module Agda.Utils.Parser.MemoisedCPS
  ( ParserClass(..)
  , sat, token, tok, doc
  , DocP, bindP, choiceP, seqP, starP, atomP
  , Parser
  , ParserWithGrammar
  ) where

import Control.Applicative ( Alternative((<|>), empty, many, some) )
import Control.Monad (liftM2, (<=<))
import Control.Monad.State.Strict (State, evalState, runState, get, modify')

import Data.Array
import Data.Hashable
import qualified Data.HashMap.Strict as Map
import Data.HashMap.Strict (HashMap)


import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import qualified Data.List as List
import Data.Maybe

import qualified Agda.Utils.Null as Null
import Agda.Syntax.Common.Pretty hiding (annotate)

import Agda.Utils.Impossible

-- | Positions.

type Pos = Int

-- | State monad used by the parser.

type M k r tok b = State (IntMap (HashMap k (Value k r tok b)))

-- | Continuations.

type Cont k r tok b a = Pos -> a -> M k r tok b [b]

-- | Memoised values.

data Value k r tok b = Value
  { _results       :: !(IntMap [r])
  , _continuations :: [Cont k r tok b r]
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
  fmap f (P p) = P $ \input i k ->
    p input i $ \i -> k i . f

instance Applicative (Parser k r tok) where
  pure x        = P $ \_ i k -> k i x
  P p1 <*> P p2 = P $ \input i k ->
    p1 input i $ \i f ->
    p2 input i $ \i x ->
    k i (f x)

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
  grammar :: Show k => p a -> Doc

  -- | Parses a token satisfying the given predicate. The computed
  -- value is returned.
  sat' :: (tok -> Maybe a) -> p a

  -- | Uses the given function to modify the printed representation
  -- (if any) of the given parser.
  annotate :: (DocP -> DocP) -> p a -> p a

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

-- | Uses the given document as the printed representation of the
-- given parser. The document's precedence is taken to be 'atomP'.

doc :: ParserClass p k r tok => Doc -> p a -> p a
doc d = annotate (\_ -> (d, atomP))

-- | Parses a token satisfying the given predicate.

sat :: ParserClass p k r tok => (tok -> Bool) -> p tok
sat p = sat' (\t -> if p t then Just t else Nothing)

-- | Parses a single token.

token :: ParserClass p k r tok => p tok
token = doc "·" (sat' Just)

-- | Parses a given token.

tok :: (ParserClass p k r tok, Eq tok, Show tok) => tok -> p tok
tok t = doc (text (show t)) (sat (t ==))

instance ParserClass (Parser k r tok) k r tok where
  parse p toks =
    flip evalState IntMap.empty $
    unP p (listArray (0, n - 1) toks) 0 $ \j x ->
      if j == n then return [x] else return []
    where n = List.genericLength toks

  grammar _ = Null.empty

  sat' p = P $ \input i k ->
    if inRange (bounds input) i then
      case p (input ! i) of
        Nothing -> return []
        Just x  -> (k $! (i + 1)) $! x
    else
      return []

  annotate _ p = p

  memoiseIfPrinting _ p = p

  memoise key p = P $ \input i k -> do

    let alter j zero f m =
          IntMap.alter (Just . f . fromMaybe zero) j m

        lookupTable   = fmap (Map.lookup key <=< IntMap.lookup i) get
        insertTable v = modify' $ alter i Map.empty (Map.insert key v)

    v <- lookupTable
    case v of
      Nothing -> do
        insertTable (Value IntMap.empty [k])
        unP p input i $ \j r -> do
          ~(Just (Value rs ks)) <- lookupTable
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
  PG (Bool -> Either (Parser k r tok a) (Docs k))
  -- ^ Invariant: If the boolean is 'True', then the result must be
  -- @'Left' something@, and if the boolean is 'False', then the
  -- result must be @'Right' something@.

-- | Documents paired with precedence levels.

type DocP = (Doc, Int)

-- | Precedence of @>>=@.

bindP :: Int
bindP = 10

-- | Precedence of @<|>@.

choiceP :: Int
choiceP = 20

-- | Precedence of @<*>@.

seqP :: Int
seqP = 30

-- | Precedence of @⋆@ and @+@.

starP :: Int
starP = 40

-- | Precedence of atoms.

atomP :: Int
atomP = 50

-- | The extended parser type computes one top-level document, plus
-- one document per encountered memoisation key.
--
-- 'Nothing' is used to mark that a given memoisation key has been
-- seen, but that no corresponding document has yet been stored.

type Docs k = State (HashMap k (Maybe DocP)) DocP

-- | A smart constructor.

pg :: Parser k r tok a -> Docs k -> ParserWithGrammar k r tok a
pg p d = PG $ \b -> if b then Left p else Right d

-- | Extracts the parser.

parser :: ParserWithGrammar k r tok a -> Parser k r tok a
parser (PG p) = either id __IMPOSSIBLE__ (p True)

-- | Extracts the documents.

docs :: ParserWithGrammar k r tok a -> Docs k
docs (PG p) = either __IMPOSSIBLE__ id (p False)

instance Monad (ParserWithGrammar k r tok) where
  return  = pure
  p >>= f =
    pg (parser p >>= parser . f)
       ((\(d, p) -> (mparens (p < bindP) d <+> ">>= ?", bindP))
          <$> docs p)

instance Functor (ParserWithGrammar k r tok) where
  fmap f p = pg (fmap f (parser p)) (docs p)

instance Applicative (ParserWithGrammar k r tok) where
  pure x    = pg (pure x) (return ("ε", atomP))
  p1 <*> p2 =
    pg (parser p1 <*> parser p2)
       (liftM2 (\(d1, p1) (d2, p2) ->
                   (sep [ mparens (p1 < seqP) d1
                        , mparens (p2 < seqP) d2
                        ], seqP))
               (docs p1) (docs p2))

-- | A helper function.

starDocs :: String -> ParserWithGrammar k r tok a -> Docs k
starDocs s p =
  (\(d, p) -> (mparens (p < starP) d <+> text s, starP)) <$> docs p

instance Alternative (ParserWithGrammar k r tok) where
  empty     = pg empty (return ("∅", atomP))
  p1 <|> p2 =
    pg (parser p1 <|> parser p2)
       (liftM2 (\(d1, p1) (d2, p2) ->
                   (sep [ mparens (p1 < choiceP) d1
                        , "|"
                        , mparens (p2 < choiceP) d2
                        ], choiceP))
               (docs p1) (docs p2))

  many p = pg (many (parser p)) (starDocs "⋆" p)
  some p = pg (some (parser p)) (starDocs "+" p)

-- | Pretty-prints a memoisation key.

prettyKey :: Show k => k -> DocP
prettyKey key = (text ("<" ++ show key ++ ">"), atomP)

-- | A helper function.

memoiseDocs ::
  (Eq k, Hashable k, Show k) =>
  k -> ParserWithGrammar k r tok r -> Docs k
memoiseDocs key p = do
  r <- Map.lookup key <$> get
  case r of
    Just _  -> return ()
    Nothing -> do
      modify' (Map.insert key Nothing)
      d <- docs p
      modify' (Map.insert key (Just d))
  return (prettyKey key)

instance ParserClass (ParserWithGrammar k r tok) k r tok where
  parse p                 = parse (parser p)
  sat' p                  = pg (sat' p) (return ("<sat ?>", atomP))
  annotate f p            = pg (parser p) (f <$> docs p)
  memoise key p           = pg (memoise key (parser p))
                               (memoiseDocs key p)
  memoiseIfPrinting key p = pg (parser p) (memoiseDocs key p)

  grammar p =
    d
      $+$
    nest 2 (foldr1 ($+$) $
      "where" :
      map (\(k, d) -> fst (prettyKey k) <+> "∷=" <+>
                        maybe __IMPOSSIBLE__ fst d)
          (Map.toList ds))
    where
    ((d, _), ds) = runState (docs p) Map.empty
