{
{-|
-}
module Syntax.Parser.Parser (
      tokensParser
    ) where

import Syntax.Position
import Syntax.Parser.Monad
import Syntax.Parser.Lexer
import Syntax.Parser.Tokens
import Syntax.Concrete

import Utils.Monad

}

%name tokensParser Tokens
%tokentype { Token }
%monad { Parser }
%lexer { lexer } { TkEOF }
-- %expect 3

%token
    '('	    { TkLParen $$ }
    ')'	    { TkRParen $$ }
    '\\'    { TkLambda $$ }
    '->'    { TkArrow $$ }
    '_'     { TkUnderscore $$ }
    id	    { TkId $$ }
    int	    { TkInt $$ }
    string  { TkLitString $$ }
    char    { TkLitChar $$ }
    ':'	    { TkColon $$ }
    univ    { TkUniverse $$ }
    let	    { TkLet $$ }
    in	    { TkIn $$ }
    of	    { TkOf $$ }
    data    { TkData $$ }
    where   { TkWhere $$ }
    Star    { TkStar $$ }
    Set	    { TkSet $$ }
    ISet    { TkISet $$ }
    Prop    { TkProp $$ }
    Type    { TkType $$ }
    infix   { TkInfix $$ }
    infixl  { TkInfixL $$ }
    infixr  { TkInfixR $$ }
    plugin  { TkPlugin $$ }
    sig	    { TkSig $$ }
    struct  { TkStruct $$ }
    '{'	    { TkOpenBrace $$ }
    '}'	    { TkCloseBrace $$ }
    '['	    { TkOpenSquare $$ }
    ']'	    { TkCloseSquare $$ }
    vopen   { TkVOpenBrace $$ }
    vclose  { TkVCloseBrace $$ }
    '='	    { TkEqual $$ }
    ';'	    { TkSemi $$ }
    vsemi   { TkVSemi $$ }
    ','	    { TkComma $$ }
    '`'	    { TkBackQuote $$ }
    '.'	    { TkDot $$ }
    '?'	    { TkOp ($$,"?") }
    op	    { TkOp $$ }
    TeX	    { TkTeX $$ }

%%

-- Tokens

Token
    : '('	{ TkLParen $1 }
    | ')'	{ TkRParen $1 }
    | '\\'	{ TkLambda $1 }
    | '->'	{ TkArrow $1 }
    | '_'	{ TkUnderscore $1 }
    | id	{ TkId $1 }
    | string	{ TkLitString $1 }
    | char	{ TkLitChar $1 }
    | int	{ TkInt $1 }
    | ':'	{ TkColon $1 }
    | univ	{ TkUniverse $1 }
    | let	{ TkLet $1 }
    | in	{ TkIn $1 }
    | of	{ TkOf $1 }
    | data	{ TkData $1 }
    | where	{ TkWhere $1 }
    | Star	{ TkStar $1 }
    | Set	{ TkSet $1 }
    | ISet	{ TkISet $1 }
    | Prop	{ TkProp $1 }
    | Type	{ TkType $1 }
    | infix	{ TkInfix $1 }
    | infixl	{ TkInfixL $1 }
    | infixr	{ TkInfixR $1 }
    | plugin	{ TkPlugin $1 }
    | sig	{ TkSig $1 }
    | struct	{ TkStruct $1 }
    | '{'	{ TkOpenBrace $1 }
    | '}'	{ TkCloseBrace $1 }
    | '['	{ TkOpenSquare $1 }
    | ']'	{ TkCloseSquare $1 }
    | vopen	{ TkVOpenBrace $1 }
    | vclose	{ TkVCloseBrace $1 }
    | '='	{ TkEqual $1 }
    | ';'	{ TkSemi $1 }
    | vsemi	{ TkVSemi $1 }
    | ','	{ TkComma $1 }
    | '`'	{ TkBackQuote $1 }
    | '.'	{ TkDot $1 }
    | '?'	{ TkOp ($1,"?") }
    | op	{ TkOp $1 }
    | TeX	{ TkTeX $1 }

Tokens	: Token Tokens	{ $1 : $2 }
	|		{ [] }

topen :			{% pushCurrentContext }

{

-- Parsing

tokensParser	:: Parser [Token]

happyError = fail "Parse error"

}
