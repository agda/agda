-- | A abstract 'Range' type dedicated to keyword occurrences in the source.

module Agda.Syntax.Common.KeywordRange
  ( KwRange  -- Do not export the constructor.
  , kwRange
  ) where

import Control.DeepSeq ( NFData(rnf) )

import Agda.Syntax.Common.Pretty
import Agda.Syntax.Position

import Agda.Utils.Null

-- | Range dedicated to a keyword or fixed token sequence.
--
-- Motivation: by lacking a 'SetRange' instance we indicate that it cannot be updated.

newtype KwRange = KwRange { theKwRange :: Range }
  deriving (Eq, Ord, Show, Null)

-- | Create a keyword range.

kwRange :: HasRange a => a -> KwRange
kwRange = KwRange . getRange

-- Instances

instance HasRange KwRange where
  getRange = theKwRange

instance KillRange KwRange where
  killRange _ = empty

-- no SetRange instance!!

instance NFData KwRange where
  rnf _ = ()

instance Pretty KwRange where
  prettyPrec i = prettyPrec i . theKwRange
