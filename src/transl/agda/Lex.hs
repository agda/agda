-- | Haskell lexical analysis.  Written for speed, not beauty!
module Lex(Token(..), LexItem(..), prLexItem, lexStart, isIdChar,lx,isSym) where
import Position
import Error
import FString
--import ListUtil
import Data.Char
import AgdaTrace

data LexItem =
          L_varid FString
        | L_modid FString
        | L_varsym FString
        | L_integer Integer
        | L_rational Rational
--      | L_float Rational
        | L_char Char
        | L_string String
        | L_lpar
        | L_rpar
        | L_comma
        | L_semi
        | L_uscore
        | L_bquote
        | L_lcurl
        | L_rcurl
        | L_lsquare
        | L_rsquare
        -- reserved words

        | L_abstract | L_axiom
        | L_case | L_class  | L_concrete | L_data
         | L_do
        | L_else
        | L_exports | L_extends | L_external

        | L_icase  | L_idata
        | L_if
        | L_in
        | L_instance  | L_interface
        | L_native | L_let | L_module
        | L_mutual
        | L_newtype
        | L_of | L_open  | L_over
        | L_package | L_private
        | L_public | L_Set | L_sig | L_struct
        | L_then | L_Type | L_type | L_use
        | L_where
        -- reserved ops
        | L_dcolon | L_eq | L_at | L_lam | L_bar | L_excl
        | L_rarrow | L_larrow | L_brarrow | L_star | L_dot

        -- pseudo items
        | L_eof StrTable
        | L_error ErrMsg

         | L_meta | L_conid FString
        | L_comment String     -- for alfa
        deriving (Eq,Show)

prLexItem (L_varid s)   = getFString s
prLexItem (L_modid s)   = getFString s
prLexItem (L_varsym s)  = getFString s
prLexItem (L_integer i) = show i
prLexItem (L_rational r) = show r
prLexItem (L_char s) = show s
prLexItem (L_string s) = show s
prLexItem L_lpar = "("
prLexItem L_rpar = ")"
prLexItem L_comma = ","
prLexItem L_semi = ";"
prLexItem L_uscore = "_"
prLexItem L_bquote = "`"
prLexItem L_lcurl = "{"
prLexItem L_rcurl = "}"
prLexItem L_lsquare = "["
prLexItem L_rsquare = "]"
prLexItem L_abstract = "abstract"
prLexItem L_case = "case"
prLexItem L_concrete = "concrete"
prLexItem L_data = "data"
prLexItem L_newtype = "newtype"
prLexItem L_do = "do"

prLexItem L_else = "else"
prLexItem L_if = "if"
prLexItem L_in = "in"
prLexItem L_interface = "interface"
prLexItem L_let = "let"
prLexItem L_module = "module"

--prLexItem L_native = "native"
prLexItem L_of = "of"
prLexItem L_open = "open"
prLexItem L_package = "package"
prLexItem L_private = "private"
prLexItem L_public = "public"
prLexItem L_sig = "sig"
prLexItem L_struct = "struct"
prLexItem L_then = "then"
prLexItem L_type = "type"
prLexItem L_use = "use"
prLexItem L_exports = "exports"
prLexItem L_dcolon = "::"
prLexItem L_eq = "="
prLexItem L_at = "@"
prLexItem L_lam = "\\"
prLexItem L_bar = "|"
prLexItem L_excl = "!"
prLexItem L_star = "#"
prLexItem L_rarrow = "->"
prLexItem L_larrow = "<-"
prLexItem L_brarrow = "|->"
prLexItem L_dot = "."
prLexItem (L_eof _) = "<EOF>"
prLexItem (L_error s) = "Lexical error: "++show s
prLexItem L_mutual = "mutual"
prLexItem L_Set = "Set"
prLexItem L_Type = "Type"
prLexItem L_meta = "{!!}"
prLexItem (L_axiom) = "postulate"
prLexItem (L_native) = "native"
prLexItem (L_comment s) = s
prLexItem L_over = "over"
prLexItem L_idata = "idata"
prLexItem L_icase = "icase"
prLexItem L_instance = "instance"
prLexItem L_class = "class"
prLexItem L_extends = "extends"
prLexItem L_external = "external"
prLexItem L_where = "where"
prLexItem e = error (show e)




data Token = Token Position LexItem deriving (Eq)
instance Show Token where
  showsPrec _ (Token _ itm) = showString (prLexItem itm)

tabStop = 8::Int
nextTab :: Int -> Int
nextTab c = ((c+tabStop-1) `div` tabStop) * tabStop

lexStart :: Bool -> String -> StrTable -> String -> [Token]
lexStart fl file tbl cs = lx fl file 1 0 tbl cs

lx :: Bool -> String -> Int -> Int -> StrTable -> String -> [Token]
--   alfa?  file      line   column hashtab     input     output
--lx f (-1)_ t cs = internalError "lx: unknown position"
--lx f _ (-1)t cs = internalError "lx: unknown position"
lx fl f l c t ""           = [Token (Position f (l+1) (-1)) (L_eof t)]
lx fl f l c t (' ':cs)     = lx fl f l (c+1) t cs
lx fl f l c t ('\n':cs)    = lx fl f (l+1) 0 t cs
lx fl f l c t ('\r':cs)    = lx fl f l (c+1) t cs
lx fl f l c t ('\t':cs)    = lx fl f l (nextTab (c+1)) t cs
lx fl f l c t ('\v':cs)    = lx fl f l 0 t cs
lx fl f l c t ('\f':cs)    = lx fl f l 0 t cs
lx fl f l c t ('-':'-':cs)
    | fl                   = spanToEOL fl f l c t cs "--"
    | otherwise            = skipToEOL fl f l t cs
lx fl f l c t ('{':'-':cs)
    | fl                   = spanComm fl (l, c) 1 f l (c+2) t cs "-{"
    | otherwise            = skipComm fl (l, c) 1 f l (c+2) t cs
lx fl f l c t ('{':'!':cs) = Token (Position f l c) L_meta : skipMeta fl (l, c) 1 f l (c+2) t cs
lx fl f l c t ('(':cs)     = Token (Position f l c) L_lpar : lx fl f l (c+1) t cs
lx fl f l c t (')':cs)     = Token (Position f l c) L_rpar : lx fl f l (c+1) t cs
lx fl f l c t (',':cs)     = Token (Position f l c) L_comma : lx fl f l (c+1) t cs
lx fl f l c t (';':cs)     = Token (Position f l c) L_semi : lx fl f l (c+1) t cs
lx fl f l c t ('`':cs)     = Token (Position f l c) L_bquote : lx fl f l (c+1) t cs
lx fl f l c t ('{':cs)     = Token (Position f l c) L_lcurl : lx fl f l (c+1) t cs
lx fl f l c t ('}':cs)     = Token (Position f l c) L_rcurl : lx fl f l (c+1) t cs
lx fl f l c t ('[':cs)     = Token (Position f l c) L_lsquare : lx fl f l (c+1) t cs
lx fl f l c t (']':cs)     = Token (Position f l c) L_rsquare : lx fl f l (c+1) t cs
--lx fl f l c t ('-':'>':cs)            = Token (Position f l c) L_rarrow : lx fl f l (c+2) t cs
lx fl f l c t (':':':':cs) = Token (Position f l c) L_dcolon : lx fl f l (c+2) t cs
lx fl f l c t  ('?':cs)    = Token (Position f l c) L_meta : lx fl f l (c+1) t cs
lx fl f l c t ('\'':cs)    =
    case lexLitChar' cs of
        Just (cc, n, '\'':cs) -> Token (Position f l c) (L_char cc) : lx fl f l (c+2+n) t cs
        _ -> lexerr f l c t EBadCharLit
lx fl f l c t ('"':cs)          =
        case lexString cs l (c+1) "" of
            Just (str, l', c', cs') -> Token (Position f l c) (L_string str) : lx fl f l' c' t cs'
            _ -> lexerr f l c t EBadStringLit
        where
                lexString :: String -> Int -> Int -> String -> Maybe (String, Int, Int, String)
                lexString ('"':s)      l c r             = Just (reverse r, l, c+1, s)
                lexString s            l c r             = lexLitChar' s >>= \ (x, n, s') -> lexString s' l (c+n) (x:r)


lx fl f l c t (x:cs) | isDigit x =
   case span isDigit cs of
    (s', cs') ->
        let s = x:s'
        in  case cs' of
                '.':cs@(y:_) | isDigit y ->
                    let (s'', cs'') = span isDigit cs
                        sf = s++'.':s''
                    in  case cs'' of
                            e:z:w:cs | (e=='e' || e=='E') && (z=='+' || z=='-') && isDigit w ->
                                let (s''', cs''') = span isDigit cs
                                in Token (Position f l c) (ldouble (sf++e:z:w:s''')) :
                                   lx fl f l (c+length sf+3+length s''') t cs'''
                            e:w:cs | (e=='e' || e=='E') && isDigit w ->
                                let (s''', cs''') = span isDigit cs
                                in Token (Position f l c) (ldouble (sf++e:w:s''')) :
                                   lx fl f l (c+length sf+2+length s''') t cs'''
                            _ -> Token (Position f l c) (ldouble sf) :
                                 lx fl f l (c+length sf) t cs''
                _ -> Token (Position f l c) (L_integer (read s)) : lx fl f l (c+length s) t cs'


lx fl f l c t (x:cs) | isSym x = spanSym [] (c+1) cs
    where
    spanSym r cn (y:cs) | isSym y = spanSym (y:r) (cn+1) cs
    spanSym r cn cs' = if cn == (-1::Int) then error "??5" else
        let s = x:reverse r
            p = Position f l c
            lxrs x = Token p x : lx fl f l cn t cs'
        in  case s of
--              "::"    -> lxrs L_dcolon
                "="     -> lxrs L_eq
                "@"     -> lxrs L_at
                "\\"    -> lxrs L_lam
                "|"     -> lxrs L_bar
                "!"     -> lxrs L_excl
                "#"     -> lxrs L_star
--              "->"    -> lxrs L_rarrow
                "<-"    -> lxrs L_larrow
--              "|->"   -> lxrs L_brarrow
                "."     -> lxrs L_dot
                ","     -> lxrs L_comma
                _       ->
                        case hmkFString t s of
                        (t', fs) ->
                            Token p (L_varsym fs) : lx fl f l cn t' cs'



lx fl f l c t (x:cs) | isAlpha x || x == '_' = spanId [] (c+1) cs
    where
    spanId r cn (y:cs) | isIdChar y = spanId (y:r) (cn+1) cs
    spanId r cn cs' = if cn == (-1::Int) then error "??6" else
        let s = x:reverse r
            p = Position f l c
            lxr x = Token p x : lx fl f l cn t cs'
        in  case s of
                "_"             -> lxr L_uscore
                "abstract"      -> lxr L_abstract
                "case"          -> lxr L_case
                "class"         -> lxr L_class
                "concrete"      -> lxr L_concrete
                "data"          -> lxr L_data
                "do"            -> lxr L_do
                "else"          -> lxr L_else
                "exports"       -> lxr L_exports
                "extends"       -> lxr L_extends
                "external"      -> lxr L_external
                "icase"         -> lxr L_icase
                "idata"         -> lxr L_idata
                "if"            -> lxr L_if
--              "import"        -> lxr L_import
                "in"            -> lxr L_in
                "instance"      -> lxr L_instance
                "interface"     -> lxr L_interface
                "let"           -> lxr L_let
                "module"        -> lxr L_module
                "mutual"        -> lxr L_mutual
                "native"        -> lxr L_native
                "newtype"       -> lxr L_newtype
                "of"            -> lxr L_of
                "open"          -> lxr L_open
                "over"          -> lxr L_over
                "package"       -> lxr L_package
                "postulate"     -> lxr L_axiom
                "private"       -> lxr L_private
                "public"        -> lxr L_public
                "Set"           -> lxr L_Set
                "sig"           -> lxr L_sig
                "struct"        -> lxr L_struct
                "then"          -> lxr L_then
                "type"          -> lxr L_type
                "Type"          -> lxr L_Type
                "use"           -> lxr L_use
                "where"         -> lxr L_where



                _               ->
                   case hmkFString t s of
                        (t', fs) ->
                           if modChar `elem` s then
                                 Token p (L_modid fs) : lx fl f l cn t' cs'
                           else Token p (L_varid fs) : lx fl f l cn t' cs'
lx fl f l c t (x:cs) = lexerr f l c t (EBadLexChar x)

isUpper_ ('_':cs) = isUpper_ cs
isUpper_ (c:_) = isUpper c
isUpper_ [] = True

lexerr f l c t msg = map (Token (Position f l c)) (L_error msg : repeat (L_eof t))

isSym '!' = True; isSym '#'  = True; isSym '$' = True; isSym '@' = True
isSym '%' = True; isSym '&'  = True; isSym '*' = True; isSym '+' = True
isSym '.' = True; isSym '/'  = True; isSym '<' = True; isSym '=' = True
isSym '>' = True; isSym '\\' = True; isSym '^' = True
isSym '|' = True; isSym ':'  = True; isSym '-' = True; isSym '~' = True
isSym ',' = True
isSym c | c >= '\x80' = c `elem` (['\xa1'..'\xb1'] ++ "\xd7\xf7")
				-- "¡¢£¤¥¦§¨©ª«¬­®¯°±²³´µ¶·¸¹º»¼½¾¿×÷"
--isSym c | c >= '\x80' = isSymbol c
isSym _   = False



isIdChar '\'' = True
isIdChar '_'  = True
isIdChar c    = c == modChar || isAlphaNum c

modChar = '$'

skipComm :: Bool -> (Int,Int) -> Int -> String -> Int -> Int -> StrTable -> String -> [Token]
skipComm fl lc 0 f l c t cs           = lx fl f l c t cs
skipComm fl lc n f l c t ('-':'}':cs) = skipComm fl lc (n-1) f l (c+2) t cs
skipComm fl lc n f l c t ('{':'-':cs) = skipComm fl lc (n+1) f l (c+2) t cs
skipComm fl lc n f l c t ('\n':cs)    = skipComm fl lc n     f (l+1) 0 t cs
skipComm fl lc n f l c t ('\t':cs)    = skipComm fl lc n f l (nextTab (c+1)) t cs
skipComm fl lc n f l c t (_:cs)       = skipComm fl lc n f l (c+1) t cs
skipComm fl (ll,cc) n f l c t ""      = lexerr f l c t (EUntermComm (Position "" ll cc))

spanComm :: Bool -> (Int,Int) -> Int -> String -> Int -> Int -> StrTable -> String -> String -> [Token]
spanComm fl (ll,cc) 0 f l c t cs s      = let pos = Position f ll cc
                                          in Token pos (L_comment (reverse s)) :
                                             lx fl f l c t cs
spanComm fl lc n f l c t ('-':'}':cs) s = spanComm fl lc (n-1) f l (c+2) t cs ('}':'-':s)
spanComm fl lc n f l c t ('{':'-':cs) s = spanComm fl lc (n+1) f l (c+2) t cs ('-':'{':s)
spanComm fl lc n f l c t ('\n':cs) s    = spanComm fl lc n     f (l+1) 0 t cs ('\n':s)
spanComm fl lc n f l c t ('\t':cs)  s   = spanComm fl lc n f l (nextTab (c+1)) t cs ('\t':s)
spanComm fl lc n f l c t (c':cs)   s    = spanComm fl lc n f l (c+1) t cs (c':s)
spanComm fl (ll,cc) n f l c t ""  s     = lexerr f l c t (EUntermComm (Position f ll cc))



skipMeta :: Bool -> (Int,Int) -> Int -> String -> Int -> Int -> StrTable -> String -> [Token]
skipMeta fl lc 0 f l c t cs           = lx fl f l c t cs
skipMeta fl lc n f l c t ('!':'}':cs) = skipMeta fl lc (n-1) f l (c+2) t cs
skipMeta fl lc n f l c t ('{':'!':cs) = skipMeta fl lc (n+1) f l (c+2) t cs
skipMeta fl lc n f l c t ('\n':cs)    = skipMeta fl lc n     f (l+1) 0 t cs
skipMeta fl lc n f l c t ('\t':cs)    = skipMeta fl lc n f l (nextTab (c+1)) t cs
skipMeta fl lc n f l c t (_:cs)       = skipMeta fl lc n f l (c+1) t cs
skipMeta fl (ll,cc) n f l c t ""      = lexerr f l c t (EUntermMeta (Position "" ll cc))






skipToEOL :: Bool -> String -> Int -> StrTable -> String -> [Token]
skipToEOL fl f l t ('\n':cs) = lx fl f (l+1) 0 t cs
skipToEOL fl f l t (_:cs)    = skipToEOL fl f l t cs
skipToEOL fl f l t ""        = lexerr f l 0 t EMissingNL

spanToEOL :: Bool -> String -> Int -> Int -> StrTable -> String -> String -> [Token]
spanToEOL fl f l c t ('\n':cs) s = let pos = Position f l c
                                   in Token pos (L_comment (reverse s)) :
                                      lx fl f (l+1) 0 t cs
spanToEOL fl f l c t (c':cs) s   = spanToEOL fl f l c t cs (c':s)
spanToEOL fl f l c t "" s        = lexerr f l c t EMissingNL



lexLitChar'             :: String -> Maybe (Char, Int, String)
lexLitChar' ('\\':s)    = lexEsc s
        where
        lexEsc ('x':s)  = let (n,s') = span isHexDigit s in Just (chr (readN 16 n), 2+length n, s')
        lexEsc ('n':s)  = Just ('\n', 1, s)
        lexEsc ('t':s)  = Just ('\t', 1, s)
        lexEsc ('"':s)  = Just ('"', 1, s)
        lexEsc ('\'':s) = Just ('\'', 1, s)
        lexEsc ('\\':s) = Just ('\\', 1, s)
        lexEsc s        = Nothing
lexLitChar' ('\n':_)    = Nothing               -- NL in strings is a bad idea
lexLitChar' (c:s)       = Just (c, 1, s)
lexLitChar' ""          = Nothing

readN radix s = foldl1 (\n d -> n * radix + d) (map (char2int . toUpper) s)
  where
    char2int :: Char -> Int
    char2int c = let n = (ord c) - (ord '0')
                 in if n < 10
                    then n
                    else ((n + (ord '0')) - (ord 'A')) + 10



ldouble s =
    let f = read s :: Double
    in L_rational (toRational f)
