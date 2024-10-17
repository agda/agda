module Agda.TypeChecking.Polarity.Base
  ( Polarity(..)
  ) where

import GHC.Generics (Generic)
import {-# SOURCE #-} Agda.Compiler.Treeless.Pretty () -- Instances only
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Position (KillRange (..))
import Control.DeepSeq ( NFData )


-- | Polarity for equality and subtype checking.
data Polarity
  = Covariant      -- ^ monotone
  | Contravariant  -- ^ antitone
  | Invariant      -- ^ no information (mixed variance)
  | Nonvariant     -- ^ constant
  deriving (Show, Eq, Generic)

instance Pretty Polarity where
  pretty = text . \case
    Covariant     -> "+"
    Contravariant -> "-"
    Invariant     -> "*"
    Nonvariant    -> "_"


instance KillRange Polarity where
  killRange = id


instance NFData Polarity
