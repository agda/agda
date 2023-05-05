{-| Choice of Unicode or ASCII glyphs.
-}
module Agda.Syntax.Concrete.Glyph
  ( UnicodeOrAscii(..)
  , unsafeSetUnicodeOrAscii
  , specialCharactersForGlyphs
  , braces', dbraces
  , forallQ
  , leftIdiomBrkt, rightIdiomBrkt, emptyIdiomBrkt
  , arrow, lambda
  , SpecialCharacters(..)
  ) where

import Control.DeepSeq

import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)

import GHC.Generics (Generic)

import Agda.Utils.Boolean
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Pretty

-- | We want to know whether we are allowed to insert unicode characters or not.
data UnicodeOrAscii
  = UnicodeOk  -- ^ 'true': Unicode characters are allowed.
  | AsciiOnly  -- ^ 'false: Stick to ASCII.
  deriving (Show, Eq, Enum, Bounded, Generic)

instance NFData UnicodeOrAscii

instance Boolean UnicodeOrAscii where
  fromBool = \case
    True -> UnicodeOk
    False -> AsciiOnly

instance IsBool UnicodeOrAscii where
  toBool = \case
    UnicodeOk -> True
    AsciiOnly -> False

{-# NOINLINE unsafeUnicodeOrAsciiIORef #-}
unsafeUnicodeOrAsciiIORef :: IORef UnicodeOrAscii
unsafeUnicodeOrAsciiIORef = UNSAFE.unsafePerformIO $ newIORef UnicodeOk

{-# NOINLINE unsafeSetUnicodeOrAscii #-}
unsafeSetUnicodeOrAscii :: UnicodeOrAscii -> IO ()
unsafeSetUnicodeOrAscii = writeIORef unsafeUnicodeOrAsciiIORef

-- | Are we allowed to use unicode supscript characters?
unsafeUnicodeOrAscii :: UnicodeOrAscii
unsafeUnicodeOrAscii = UNSAFE.unsafePerformIO (readIORef unsafeUnicodeOrAsciiIORef)

-- | Picking the appropriate set of special characters depending on
-- whether we are allowed to use unicode or have to limit ourselves
-- to ascii.

data SpecialCharacters = SpecialCharacters
  { _dbraces :: Doc -> Doc
  , _lambda  :: Doc
  , _arrow   :: Doc
  , _forallQ :: Doc
  , _leftIdiomBrkt  :: Doc
  , _rightIdiomBrkt :: Doc
  , _emptyIdiomBrkt :: Doc
  }

specialCharactersUnicode :: SpecialCharacters
specialCharactersUnicode = SpecialCharacters
  { _dbraces = (("\x2983 " <>) . (<> " \x2984"))
  , _lambda  = "\x03bb"
  , _arrow   = "\x2192"
  , _forallQ = "\x2200"
  , _leftIdiomBrkt  = "\x2987"
  , _rightIdiomBrkt = "\x2988"
  , _emptyIdiomBrkt = "\x2987\x2988"
  }

specialCharactersAscii :: SpecialCharacters
specialCharactersAscii = SpecialCharacters
  { _dbraces = braces . braces'
  , _lambda  = "\\"
  , _arrow   = "->"
  , _forallQ = "forall"
  , _leftIdiomBrkt  = "(|"
  , _rightIdiomBrkt = "|)"
  , _emptyIdiomBrkt = "(|)"
  }

-- | Return the glyph set based on a given (unicode or ascii) glyph mode
specialCharactersForGlyphs :: UnicodeOrAscii -> SpecialCharacters
specialCharactersForGlyphs UnicodeOk = specialCharactersUnicode
specialCharactersForGlyphs AsciiOnly = specialCharactersAscii

-- | Choose the glyph set based on the unsafe IORef.
{-# NOINLINE specialCharacters #-}
specialCharacters :: SpecialCharacters
specialCharacters = specialCharactersForGlyphs unsafeUnicodeOrAscii

braces' :: Doc -> Doc
braces' d = caseList (render d) (braces d) {-else-} $ \ c cs ->
  braces (spaceIfDash c <> d <> spaceIfDash (last1 c cs))
  -- Add space to avoid starting a comment (Ulf, 2010-09-13, #269)
  -- Andreas, 2018-07-21, #3161: Also avoid ending a comment
  where
  spaceIfDash '-' = " "
  spaceIfDash _   = empty

-- double braces...
dbraces :: Doc -> Doc
dbraces = _dbraces specialCharacters

-- forall quantifier
forallQ :: Doc
forallQ = _forallQ specialCharacters

-- left, right, and empty idiom bracket
leftIdiomBrkt, rightIdiomBrkt, emptyIdiomBrkt :: Doc
leftIdiomBrkt  = _leftIdiomBrkt  specialCharacters
rightIdiomBrkt = _rightIdiomBrkt specialCharacters
emptyIdiomBrkt = _emptyIdiomBrkt specialCharacters

arrow, lambda :: Doc
arrow  = _arrow specialCharacters
lambda = _lambda specialCharacters
