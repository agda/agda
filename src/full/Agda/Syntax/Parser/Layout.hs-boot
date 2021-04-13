module Agda.Syntax.Parser.Layout where

import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Tokens

offsideRule      :: LexAction Token
newLayoutBlock   :: LexAction Token
emptyLayout      :: LexAction Token
