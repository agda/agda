
module Syntax.Parser.Tokens
    where

import Syntax.Position

data Token  = TkLambda Range	| TkArrow Range  | TkId (Range, String)
	    | TkLParen Range	| TkRParen Range | TkSemi Range | TkComma Range
	    | TkUniverse (Range,Int)
	    | TkSet Range	| TkType Range	 | TkProp Range | TkISet Range
	    | TkStar (Range,Int)
	    | TkInfix Range	| TkInfixL Range | TkInfixR Range
            | TkBackQuote Range	| TkWhere Range	 | TkData Range
	    | TkInt (Range, Int)| TkDblArrow Range
	    | TkOpenBrace Range	| TkCloseBrace Range
	    | TkOpenSquare Range| TkCloseSquare Range
	    | TkVOpenBrace Range| TkVCloseBrace Range	| TkVSemi Range
	    | TkEqual Range	| TkColon Range    | TkDot Range
	    | TkLet Range	| TkIn Range	    | TkPlugin (Range,String)
	    | TkSig Range	| TkStruct Range    | TkOf Range
            | TkUnderscore Range| TkOp (Range, String)
	    | TkTeX String
	    | TkLitString (Range,String)
	    | TkLitChar (Range, Char)
	    | TkEOF
    deriving Show

