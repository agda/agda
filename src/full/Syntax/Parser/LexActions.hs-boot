module Syntax.Parser.LexActions where

import Syntax.Literal
import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Position

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
