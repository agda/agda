------------------------------------------------------------------------
-- | The parser monad used by the operator parser
------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.Syntax.Concrete.Operators.Parser.Monad
  ( MemoKey(..)
  , Parser
  , parse
  , token
  , sat
  , tok
  , annotate
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

-- | Parses a single token.

token :: Parser tok (MaybePlaceholder tok)
token = Parser.token

-- | Parses a token satisfying the given predicate.

sat :: (MaybePlaceholder tok -> Bool) ->
       Parser tok (MaybePlaceholder tok)
sat = Parser.sat

-- | Parses a given token.

tok :: (Eq tok, Show tok) =>
       MaybePlaceholder tok -> Parser tok (MaybePlaceholder tok)
tok = Parser.tok

-- | Uses the given function to modify the printed representation (if
-- any) of the given parser.

annotate :: (Doc -> Doc) -> Parser tok a -> Parser tok a
annotate = Parser.annotate

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
