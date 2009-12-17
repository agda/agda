{-# LANGUAGE CPP #-}

-- | IO functions which are used when reading from standard input and
-- writing to standard output. Uses the UTF-8 character encoding under
-- versions of the base library up to 4.1, and whatever the locale
-- specifies under base 4.2 (and later?; only if the locale is
-- supported, see "System.IO").
--
-- Note that @'hSetEncoding' 'stdin'@ and @'hSetEncoding' 'stdout'@
-- can be used to change the behaviour of the functions below if base
-- 4.2 (or later?) is used.

module Agda.Utils.IO.Locale
  ( print
  , putStr
  , putStrLn
  , hGetContents
  ) where

import Prelude (Show, IO, String)
import System.IO (Handle)
#if MIN_VERSION_base(4,2,0)
import qualified Prelude
import qualified System.IO as IO
#else
import qualified System.IO.UTF8 as UTF8
#endif

-- | Prints the value.

print :: Show a => a -> IO ()
#if MIN_VERSION_base(4,2,0)
print = Prelude.print
#else
print = UTF8.print
#endif

-- | Prints the string.

putStr :: String -> IO ()
#if MIN_VERSION_base(4,2,0)
putStr = Prelude.putStr
#else
putStr = UTF8.putStr
#endif

-- | Prints the string with an appended newline.

putStrLn :: String -> IO ()
#if MIN_VERSION_base(4,2,0)
putStrLn = Prelude.putStrLn
#else
putStrLn = UTF8.putStrLn
#endif

-- | Returns the stream represented by the handle lazily.

hGetContents :: Handle -> IO String
#if MIN_VERSION_base(4,2,0)
hGetContents = IO.hGetContents
#else
hGetContents = UTF8.hGetContents
#endif
