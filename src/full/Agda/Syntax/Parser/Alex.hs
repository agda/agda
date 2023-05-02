{-| This module defines the things required by Alex and some other
    Alex related things.
-}
module Agda.Syntax.Parser.Alex
    ( -- * Alex requirements
      AlexInput(..)
    , lensLexInput
    , alexInputPrevChar
    , alexGetChar, alexGetByte
      -- * Lex actions
    , LexAction(..), LexPredicate
    , (.&&.), (.||.), not'
    , PreviousInput, CurrentInput, TokenLength
      -- * Monad operations
    , getLexInput, setLexInput
    )
    where

import Control.Monad.State
import Data.Char
import Data.Word

import Agda.Syntax.Position
import Agda.Syntax.Parser.Monad

import Agda.Utils.Lens
import Agda.Utils.Tuple

-- | This is what the lexer manipulates.
data AlexInput = AlexInput
  { lexSrcFile  :: !SrcFile              -- ^ File.
  , lexPos      :: !PositionWithoutFile  -- ^ Current position.
  , lexInput    :: String                -- ^ Current input.
  , lexPrevChar :: !Char                 -- ^ Previously read character.
  }

-- | A lens for 'lexInput'.
lensLexInput :: Lens' AlexInput String
lensLexInput f r = f (lexInput r) <&> \ s -> r { lexInput = s }

-- | Get the previously lexed character. Same as 'lexPrevChar'. Alex needs this
--   to be defined to handle \"patterns with a left-context\".
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = lexPrevChar

-- | Returns the next character, and updates the 'AlexInput' value.
--
-- This function is not suitable for use by Alex 2, because it can
-- return non-ASCII characters.
alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar     (AlexInput { lexInput = []              }) = Nothing
alexGetChar inp@(AlexInput { lexInput = c:s, lexPos = p }) =
    Just (c, AlexInput
                 { lexSrcFile   = lexSrcFile inp
                 , lexInput     = s
                 , lexPos       = movePos p c
                 , lexPrevChar  = c
                 }
         )

-- | Returns the next byte, and updates the 'AlexInput' value.
--
-- A trick is used to handle the fact that there are more than 256
-- Unicode code points. The function translates characters to bytes in
-- the following way:
--
-- * Whitespace characters other than \'\\t\' and \'\\n\' are
--   translated to \' \'.
-- * Non-ASCII alphabetical characters are translated to \'z\'.
-- * Other non-ASCII printable characters are translated to \'+\'.
-- * Everything else is translated to \'\\1\'.
--
-- Note that it is important that there are no keywords containing
-- \'z\', \'+\', \' \' or \'\\1\'.
--
-- This function is used by Alex (version 3).

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte ai =
  mapFst (fromIntegral . fromEnum . toASCII) <$> alexGetChar ai
  where
  toASCII c
    | isSpace c && c /= '\t' && c /= '\n' = ' '
    | isAscii c                           = c
    | isPrint c                           = if isAlpha c then 'z'
                                                         else '+'
    | otherwise                           = '\1'

{--------------------------------------------------------------------------
    Monad operations
 --------------------------------------------------------------------------}

getLexInput :: Parser AlexInput
getLexInput = gets getInp
    where
        getInp s = AlexInput
                    { lexSrcFile    = parseSrcFile s
                    , lexPos        = parsePos s
                    , lexInput      = parseInp s
                    , lexPrevChar   = parsePrevChar s
                    }

setLexInput :: AlexInput -> Parser ()
setLexInput inp = modify upd
    where
        upd s = s { parseSrcFile    = lexSrcFile inp
                  , parsePos        = lexPos inp
                  , parseInp        = lexInput inp
                  , parsePrevChar   = lexPrevChar inp
                  }

{--------------------------------------------------------------------------
    Lex actions
 --------------------------------------------------------------------------}

type PreviousInput  = AlexInput
type CurrentInput   = AlexInput
type TokenLength    = Int

-- | In the lexer, regular expressions are associated with lex actions who's
--   task it is to construct the tokens.
newtype LexAction r
  = LexAction { runLexAction :: PreviousInput -> CurrentInput -> TokenLength -> Parser r }
  deriving (Functor)

instance Applicative LexAction where
  pure r    = LexAction $ \ _ _ _ -> pure r
  mf <*> mr = LexAction $ \ a b c -> runLexAction mf a b c <*> runLexAction mr a b c

instance Monad LexAction where
  return = pure
  m >>= k  = LexAction $ \ a b c -> do
    r <- runLexAction m a b c
    runLexAction (k r) a b c

instance MonadState ParseState LexAction where
  get   = LexAction $ \ _ _ _ -> get
  put s = LexAction $ \ _ _ _ -> put s

-- | Sometimes regular expressions aren't enough. Alex provides a way to do
--   arbitrary computations to see if the input matches. This is done with a
--   lex predicate.
type LexPredicate   = ([LexState], ParseFlags) -> PreviousInput -> TokenLength -> CurrentInput -> Bool

-- | Conjunction of 'LexPredicate's.
(.&&.) :: LexPredicate -> LexPredicate -> LexPredicate
p1 .&&. p2 = \x y z u -> p1 x y z u && p2 x y z u

-- | Disjunction of 'LexPredicate's.
(.||.) :: LexPredicate -> LexPredicate -> LexPredicate
p1 .||. p2 = \x y z u -> p1 x y z u || p2 x y z u

-- | Negation of 'LexPredicate's.
not' :: LexPredicate -> LexPredicate
not' p = \x y z u -> not (p x y z u)
