{-# OPTIONS -cpp #-}

module Syntax.Parser.Layout where

import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Parser.LexActions
import Syntax.Position

-- Layout

openBrace :: LexAction Token
openBrace = scanTok $ \_ ->
    do	pushContext NoLayout
	r <- getParseRange
	return (TkOpenBrace r)

closeBrace :: LexAction Token
closeBrace = scanTok $ \_ ->
    do	popContext
	r <- getParseRange
	return (TkCloseBrace r)

beginningOfLine :: LexAction Token
beginningOfLine (p,_,_) _ _ =
    do	offs <- getOffside p
	case offs of
	    LT	-> do	popContext
			return (TkVCloseBrace (Range p p))
	    EQ	-> do	popLexState
			return (TkVSemi (Range p p))
	    GT	-> do	popLexState
			scanToken

layoutLeft :: LexAction Token
layoutLeft (p,_,_) _ _ =
    do	popLexState
	pushLexState bol
	return (TkVCloseBrace (Range p p))

newLayoutContext :: LexAction Token
newLayoutContext (p,_,_) _ _ =
    do	popLexState
	let offset = posCol p
	ctx <- topContext
	case ctx of
	    Layout prev_off | prev_off >= offset ->
		do  -- token is indented to the left of the previous context.
		    -- we must generate a {} sequence now.
		    pushLexState layout_left
		    return (TkVOpenBrace (Range p p))
	    _ -> do pushContext (Layout offset)
		    return (TkVOpenBrace (Range p p))


