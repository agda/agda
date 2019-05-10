------------------------------------------------------------------------
-- | The parser monad used by the operator parser
------------------------------------------------------------------------

{-# LANGUAGE CPP           #-}
{-# LANGUAGE DeriveGeneric #-}

module Agda.Syntax.Concrete.Operators.Parser.Monad
  ( MemoKey(..)
  , Parser
  , parse
  , sat'
  , sat
  , doc
  , memoise
  , memoiseIfPrinting
  , grammar
  ) where

import Data.Hashable
import GHC.Generics (Generic)
import Text.PrettyPrint.HughesPJ

import Agda.Syntax.Common
import qualified Agda.Utils.Parser.MemoisedCPS as Parser

-- | Memoisation keys.

data MemoKey = NodeK      (Either Integer Integer)
             | PostLeftsK (Either Integer Integer)
             | PreRightsK (Either Integer Integer)
             | TopK
             | AppK
             | NonfixK
  deriving (Eq, Show, Generic)

instance Hashable MemoKey

-- | The parser monad.

type Parser tok a =
#ifdef DEBUG
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
