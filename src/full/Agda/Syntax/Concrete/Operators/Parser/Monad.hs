{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds #-}

------------------------------------------------------------------------
-- | The parser monad used by the operator parser
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module Agda.Syntax.Concrete.Operators.Parser.Monad
  ( MemoKey(..), PrecedenceKey
  , Parser
  , parse
  , sat'
  , sat
  , doc
  , memoise
  , memoiseIfPrinting
  , grammar
  , pattern LeftPK
  , pattern RightPK
  ) where

import Data.Hashable
import GHC.Generics (Generic)
#if ! (__GLASGOW_HASKELL__ <= 908)
import GHC.Exts
#endif
import GHC.Word (Word64(..))

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty

import qualified Agda.Utils.Parser.MemoisedCPS as Parser
import Agda.Utils.Hash

-- | Memoisation keys.

data MemoKey = NodeK      {-# UNPACK #-} !PrecedenceKey
             | PostLeftsK {-# UNPACK #-} !PrecedenceKey
             | PreRightsK {-# UNPACK #-} !PrecedenceKey
             | TopK
             | AppK
             | NonfixK
  deriving (Eq, Show, Generic)

data PrecedenceKey = PrecKey !Bool !PrecedenceLevel
  deriving (Eq, Show)

pattern RightPK :: PrecedenceLevel -> PrecedenceKey
pattern RightPK l = PrecKey False l

pattern LeftPK :: PrecedenceLevel -> PrecedenceKey
pattern LeftPK l = PrecKey True l

#if __GLASGOW_HASKELL__ <= 908
doubleToWord64 :: Double -> Word64
doubleToWord64 x = fromIntegral $ hash x
#else
doubleToWord64 :: Double -> Word64
doubleToWord64 (D# x) = W64# (castDoubleToWord64# x)
#endif

instance Hashable PrecedenceKey where
  hashWithSalt h (PrecKey b l) = fromIntegral $
    fromIntegral (h + fromEnum b) `combineWord` fromIntegral (doubleToWord64 l)

instance Hashable MemoKey where
  hashWithSalt h = \case
    NodeK pk      -> hashWithSalt (h + 1) pk
    PostLeftsK pk -> hashWithSalt (h + 2) pk
    PreRightsK pk -> hashWithSalt (h + 3) pk
    TopK          -> combineInt h 4
    AppK          -> combineInt h 5
    NonfixK       -> combineInt h 6

-- | The parser monad.
type Parser tok a =
#ifdef DEBUG_PARSING
  Parser.ParserWithGrammar
#else
  Parser.Parser
#endif
    MemoKey tok (MaybePlaceholder tok) a

-- | Runs the parser.

parse :: forall tok a. Parser tok a -> [MaybePlaceholder tok] -> [a]
parse = Parser.parse

-- | Parses a token satisfying the given predicate. The computed value
-- is returned.

sat' :: (MaybePlaceholder tok -> Maybe a) -> Parser tok a
sat' = Parser.sat'

-- | Parses a token satisfying the given predicate.

sat :: (MaybePlaceholder tok -> Bool) ->
       Parser tok (MaybePlaceholder tok)
sat = Parser.sat

-- | Uses the given document as the printed representation of the
-- given parser. The document's precedence is taken to be 'atomP'.

doc :: Doc -> Parser tok a -> Parser tok a
doc = Parser.doc

-- | Memoises the given parser.
--
-- Every memoised parser must be annotated with a /unique/ key.
-- (Parametrised parsers must use distinct keys for distinct inputs.)

memoise :: MemoKey -> Parser tok tok -> Parser tok tok
memoise = Parser.memoise

-- | Memoises the given parser, but only if printing, not if parsing.
--
-- Every memoised parser must be annotated with a /unique/ key.
-- (Parametrised parsers must use distinct keys for distinct inputs.)

memoiseIfPrinting :: MemoKey -> Parser tok tok -> Parser tok tok
memoiseIfPrinting = Parser.memoiseIfPrinting

-- | Tries to print the parser, or returns 'empty', depending on the
-- implementation. This function might not terminate.

grammar :: Parser tok a -> Doc
grammar = Parser.grammar
