-- | Some IORefs to access option values in pure code

module Agda.Interaction.Options.IORefs
    ( UnicodeOrAscii(..)
    , unsafeUnicodeOrAsciiIORef
    ) where

import Data.IORef
import qualified System.IO.Unsafe as UNSAFE

-- | In `Agda.Syntax.Concrete.Pretty` and `Agda.Utils.String` we want to know
-- whether we are allowed to insert unicode characters or not.

data UnicodeOrAscii = UnicodeOk | AsciiOnly

{-# NOINLINE unsafeUnicodeOrAsciiIORef #-}
unsafeUnicodeOrAsciiIORef :: IORef UnicodeOrAscii
unsafeUnicodeOrAsciiIORef = UNSAFE.unsafePerformIO $ newIORef UnicodeOk
