{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Parser.Layout where

import Agda.Syntax.Parser.Alex   (LexAction)
import Agda.Syntax.Parser.Monad  (Parser)
import Agda.Syntax.Parser.Tokens (Token)

offsideRule      :: LexAction Token
newLayoutBlock   :: LexAction Token
emptyLayout      :: LexAction Token

confirmLayout    :: Parser ()
-- confirmLayoutAtNewLine :: Parser ()
-- confirmedLayoutComing  :: Parser ()
