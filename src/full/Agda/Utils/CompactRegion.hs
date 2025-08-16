{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Agda.Utils.CompactRegion where

import GHC.Exts
import GHC.Types
import GHC.Word
import Control.DeepSeq

data Compact = Compact Compact#

instance NFData Compact where
  rnf !x = ()

-- | Create a new compact region with given initial block size.
new :: Word -> IO Compact
new (W# size) = IO \s -> case compactNew# size s of
  (# s, com #) -> (# s, Compact com #)
{-# INLINE new #-}

-- | Add a value to a compact region.
add :: Compact -> a -> IO a
add (Compact com) a = IO (compactAdd# com a)
{-# INLINE add #-}

{-# INLINE compactWithSharing #-}
compactWithSharing :: a -> IO a
compactWithSharing a = do
  !(Compact c) <- new 31268
  IO (compactAddWithSharing# c a)
