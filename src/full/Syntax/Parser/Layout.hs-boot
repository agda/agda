module Syntax.Parser.Layout where

import Syntax.Parser.Alex
import Syntax.Parser.Tokens

offsideRule      :: LexAction Token
newLayoutContext :: LexAction Token
emptyLayout      :: LexAction Token
