-- | Types used for precise syntax highlighting.

module Interaction.Highlighting.Precise where

-- | Various syntactic aspects of the code.

data Aspect
  = Bound        -- ^ Bound variable.
  | Comment
  | Constructor
  | Dotted       -- ^ Dotted pattern.
  | Function
  | Keyword
  | Number
  | Operator
  | Postulate
  | String
  | Type
    deriving Show

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- A range is associated with zero or more aspects. Note that some
-- aspects may not combine well in the user interface, depending on
-- how the various aspects are represented. It is probably a good idea
-- to document here which the possible combinations are, so that the
-- UI designer can take them into account.

data Range = Range { from, to :: Integer
                   , aspects :: [Aspect]
                   }

-- | A 'File' is a collection of 'Range's.
--
-- Invariant: All ranges should be non-overlapping.

type File = [Range]
