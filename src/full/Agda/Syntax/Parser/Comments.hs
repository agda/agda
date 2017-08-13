-- {-# LANGUAGE CPP #-}

{-| This module defines the lex action to lex nested comments. As is well-known
    this cannot be done by regular expressions (which, incidently, is probably
    the reason why C-comments don't nest).

    When scanning nested comments we simply keep track of the nesting level,
    counting up for /open comments/ and down for /close comments/.
-}
module Agda.Syntax.Parser.Comments
    where

import qualified Data.List as List

import {-# SOURCE #-} Agda.Syntax.Parser.LexActions
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.LookAhead
import Agda.Syntax.Position

import Agda.Utils.Monad

-- | Should comment tokens be output?

keepComments :: LexPredicate
keepComments (_, s) _ _ _ = parseKeepComments s

-- | Should comment tokens be output?

keepCommentsM :: Parser Bool
keepCommentsM = fmap parseKeepComments getParseFlags

-- | Manually lexing a block comment. Assumes an /open comment/ has been lexed.
--   In the end the comment is discarded and 'lexToken' is called to lex a real
--   token.
nestedComment :: LexAction Token
nestedComment inp inp' _ =
    do  setLexInput inp'
        runLookAhead err $ skipBlock "{-" "-}"
        keep <- keepCommentsM
        if keep then do
          inp'' <- getLexInput
          let p1 = lexPos inp; p2 = lexPos inp''
              i = posToInterval (lexSrcFile inp) p1 p2
              s = case (p1, p2) of
                    (Pn { posPos = p1 }, Pn { posPos = p2 }) ->
                      List.genericTake (p2 - p1) $ lexInput inp
          return $ TokComment (i, s)
         else
          lexToken
    where
        err _ = liftP $ parseErrorAt (lexPos inp) "Unterminated '{-'"

-- | Lex a hole (@{! ... !}@). Holes can be nested.
--   Returns @'TokSymbol' 'SymQuestionMark'@.
hole :: LexAction Token
hole inp inp' _ =
    do  setLexInput inp'
        runLookAhead err $ skipBlock "{!" "!}"
        p <- lexPos <$> getLexInput
        return $
          TokSymbol SymQuestionMark $
          posToInterval (lexSrcFile inp) (lexPos inp) p
    where
        err _ = liftP $ parseErrorAt (lexPos inp) "Unterminated '{!'"

-- | Skip a block of text enclosed by the given open and close strings. Assumes
--   the first open string has been consumed. Open-close pairs may be nested.
skipBlock :: String -> String -> LookAhead ()
skipBlock open close = scan 1
    where
        scan 0 = sync
        scan n = match [ open   ==>  scan (n + 1)
                       , close  ==>  scan (n - 1)
                       ] `other` scan n
            where
                (==>) = (,)
                other = ($)
