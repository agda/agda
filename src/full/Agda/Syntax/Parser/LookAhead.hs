
{-| When lexing by hand (for instance string literals) we need to do some
    looking ahead. The 'LookAhead' monad keeps track of the position we are
    currently looking at, and provides facilities to synchronise the look-ahead
    position with the actual position of the 'Parser' monad (see 'sync' and
    'rollback').
-}
module Agda.Syntax.Parser.LookAhead
    ( -- * The LookAhead monad
      LookAhead
    , runLookAhead
      -- * Operations
    , lookAheadError
    , getInput, setInput, liftP
    , nextChar, eatNextChar
    , sync, rollback
    , match, match'
    )
    where

import Control.Monad.Reader
import Control.Monad.State

import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Monad

import Agda.Utils.Null (ifNull)
import Agda.Utils.Maybe (fromMaybeM)

{--------------------------------------------------------------------------
    The look-ahead monad
 --------------------------------------------------------------------------}

{-| The LookAhead monad is basically a state monad keeping with an extra
    'AlexInput', wrapped around the 'Parser' monad.
-}
newtype LookAhead a =
    LookAhead { _unLookAhead :: ReaderT ErrorFunction
                                       (StateT AlexInput Parser) a
              }
    deriving (Functor, Applicative, Monad)

newtype ErrorFunction =
    ErrorFun { throwError :: forall a. String -> LookAhead a }

-- | Throw an error message according to the supplied method.
lookAheadError :: String -> LookAhead a
-- ASR (2021-02-07). The eta-expansion @\e -> throwError e@ is
-- required GHC >= 9.0.1 ((see Issue #4955).
lookAheadError s = ($ s) =<< do LookAhead $ asks (\e -> throwError e)

{--------------------------------------------------------------------------
    Operations
 --------------------------------------------------------------------------}

-- | Get the current look-ahead position.
getInput :: LookAhead AlexInput
getInput = LookAhead get


-- | Set the look-ahead position.
setInput :: AlexInput -> LookAhead ()
setInput = LookAhead . put


-- | Lift a computation in the 'Parser' monad to the 'LookAhead' monad.
liftP :: Parser a -> LookAhead a
liftP = LookAhead . lift . lift


-- | Look at the next character. Fails if there are no more characters.
nextChar :: LookAhead Char
nextChar = fromMaybeM (lookAheadError "unexpected end of file") nextCharMaybe

-- | Look at the next character. Return 'Nothing' if there are no more characters.
nextCharMaybe :: LookAhead (Maybe Char)
nextCharMaybe =
    do  inp <- getInput
        case alexGetChar inp of
            Nothing         -> return Nothing
            Just (c,inp')   ->
                do  setInput inp'
                    return $ Just c


-- | Consume all the characters up to the current look-ahead position.
sync :: LookAhead ()
sync =
    do  inp <- getInput
        liftP $ setLexInput inp


-- | Undo look-ahead. Restores the input from the 'ParseState'.
rollback :: LookAhead ()
rollback =
    do  inp <- liftP getLexInput
        setInput inp


-- | Consume the next character. Does 'nextChar' followed by 'sync'.
eatNextChar :: LookAhead Char
eatNextChar =
    do  c <- nextChar
        sync
        return c


{-| Do a case on the current input string. If any of the given strings match we
    move past it and execute the corresponding action. If no string matches, we
    execute a default action, advancing the input one character. This function
    only affects the look-ahead position.
-}
match :: [(String, LookAhead a)] -> LookAhead a -> LookAhead a
match xs def =
    do  c <- nextChar
        match' c xs def

{-| Same as 'match' but takes the initial character from the first argument
    instead of reading it from the input.  Consequently, in the default case
    the input is not advanced.
-}
match' :: Char -> [(String, LookAhead a)] -> LookAhead a -> LookAhead a
match' c xs def = do

  -- Set the error continuation to the default @def@, but make sure we reset
  -- the input to where we started speculative matching.
  inp <- getInput
  let fallback = setInput inp >> def

  -- Find the longest match from the table.
  match'' fallback xs c

  where
  match'' fallback bs c =

    -- Match the first character, dropping entries that do not match.
    ifNull [ (s, p) | (c':s, p) <- bs, c == c' ]

      -- If no alternatives are left, fall back to the failure continuation.
      {-then-} fallback

      -- Otherwise:
      {-else-} $ \ bs' -> do

        -- If we have a successful match, store it in the failure continuation.
        fallback' <- do
          case lookup "" bs' of

            -- No match yet.
            Nothing -> pure fallback

            -- Match found!  Remember it, and the state of the input where we found it.
            Just p  -> do
              inp <- getInput
              pure $ setInput inp >> p

        -- Keep trying to find a (longer) match.
        maybe fallback' (match'' fallback' bs') =<< nextCharMaybe

-- | Run a 'LookAhead' computation. The first argument is the error function.
runLookAhead :: (forall b. String -> LookAhead b) -> LookAhead a -> Parser a
runLookAhead err (LookAhead m) =
    do  inp <- getLexInput
        evalStateT (runReaderT m (ErrorFun err)) inp
