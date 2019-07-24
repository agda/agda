{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
lookAheadError s = ($ s) =<< do LookAhead $ asks throwError

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
nextChar =
    do  inp <- getInput
        case alexGetChar inp of
            Nothing         -> lookAheadError "unexpected end of file"
            Just (c,inp')   ->
                do  setInput inp'
                    return c


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
match' c xs def =
    do  inp <- getInput
        match'' inp xs c
    where
        match'' inp bs c =
            case bs' of
                []          -> setInput inp >> def
                [("",p)]    -> p
                _           -> match'' inp bs' =<< nextChar
            where
                bs' = [ (s, p) | (c':s, p) <- bs, c == c' ]

-- | Run a 'LookAhead' computation. The first argument is the error function.
runLookAhead :: (forall b. String -> LookAhead b) -> LookAhead a -> Parser a
runLookAhead err (LookAhead m) =
    do  inp <- getLexInput
        evalStateT (runReaderT m (ErrorFun err)) inp
