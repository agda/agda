module Agda.Syntax.Parser.LexActions where

import Agda.Syntax.Literal
import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Position

lexToken :: Parser Token

token :: (String -> Parser tok) -> LexAction tok

withRange  :: ((Range,String) -> tok) -> LexAction tok
withRange' :: (String -> a) -> ((Range,a) -> tok) -> LexAction tok
withLayout :: LexAction r -> LexAction r

begin   :: LexState -> LexAction Token
endWith :: LexAction a -> LexAction a
begin_  :: LexState -> LexAction Token
end_    :: LexAction Token

keyword    :: Keyword -> LexAction Token
symbol     :: Symbol -> LexAction Token
identifier :: LexAction Token
literal    :: Read a => (Range -> a -> Literal) -> LexAction Token

notFollowedBy :: Char -> LexPredicate
followedBy    :: Char -> LexPredicate
notEOF        :: LexPredicate
inState       :: LexState -> LexPredicate

