{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Parser.LexActions where

import Agda.Syntax.Literal
import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Position

lexToken :: Parser Token

token :: (String -> Parser tok) -> LexAction tok

withInterval  :: ((Interval, String) -> tok) -> LexAction tok
withInterval' :: (String -> a) -> ((Interval, a) -> tok) -> LexAction tok
withLayout :: Keyword -> LexAction r -> LexAction r

andThen   :: Parser () -> LexAction r -> LexAction r
skip      :: LexAction Token

begin     :: LexState -> LexAction Token
beginWith :: LexState -> LexAction a -> LexAction a
endWith   :: LexAction a -> LexAction a
begin_    :: LexState -> LexAction Token
end_      :: LexAction Token

keyword    :: Keyword -> LexAction Token
symbol     :: Symbol -> LexAction Token
identifier :: LexAction Token
literal    :: Read a => (a -> Literal) -> LexAction Token
literal'   :: (String -> a) -> (a -> Literal) -> LexAction Token
integer    :: String -> Integer

followedBy    :: Char -> LexPredicate
eof           :: LexPredicate
inState       :: LexState -> LexPredicate
