module Agda.Compiler.JS.Pretty where

import GHC.Generics (Generic)

import Data.Char ( isAsciiLower, isAsciiUpper, isDigit )
import Data.List ( intercalate )
import Data.String ( IsString (fromString) )
import Data.Semigroup ( Semigroup, (<>) )
import Data.Set ( Set, toList, insert, member )
import qualified Data.Set as Set
import Data.Map ( Map, toAscList )
import qualified Data.Text as T

import Agda.Syntax.Common ( Nat )

import Agda.Utils.Function ( applyWhen )
import Agda.Utils.Hash
import Agda.Utils.List ( indexWithDefault )
import Agda.Utils.List1 ( List1, pattern (:|), (<|) )
import qualified Agda.Utils.List1 as List1

import Agda.Utils.Impossible

import Agda.Compiler.JS.Syntax hiding (exports)

-- Pretty-print a lambda-calculus expression as ECMAScript.

--- The indentation combinators of the pretty library does not fit C-like languages
--- like ECMAScript.
--- A simple pretty printer is implemented with a better `indent` and punctuation compaction.
---
--- More explanation:
---
--- I have struggled with different pretty printers, and at the end it was much easier
--- to implement and use this ~100 SLOC code pretty printer library.
--- It produces really better quality indentation than I could achieve with the
--  standard pretty printers.
--- This library code is only used in this module, and it is specialized to pretty
--- print JavaScript code for the Agda backend, so I think its best place is in this module.
data JSModuleStyle = JSCJS | JSAMD
  deriving Generic

data Doc
    = Doc String
    | Indent Int Doc
    | Group Doc
    | Beside Doc Doc
    | Above Doc Doc
    | Enclose Doc Doc Doc
    | Space
    | Empty

minifiedCodeLinesLength :: Int
minifiedCodeLinesLength = 500

render :: Bool -> Doc -> String
render minify = intercalate "\n" . joinLines . map (uncurry mkIndent) . go 0
  where
    joinLines :: [String] -> [String]
    joinLines = applyWhen minify $ chunks 0 []
      where
        chunks len acc [] = [concat (reverse acc)]
        chunks len acc (s: ss)
            | len + n <= minifiedCodeLinesLength = chunks (len + n) (s: acc) ss
            | otherwise = concat (reverse acc): chunks n [s] ss
          where
            n = length s

    joinBy f [x] (y: ys) = f x y ++ ys
    joinBy f (x:xs) ys = x: joinBy f xs ys
    joinBy f xs ys = xs ++ ys

    mkIndent n s | minify = s
    mkIndent n "" = ""
    mkIndent n s = replicate n ' ' ++ s

    overlay (i, s) (j, s') | all punctuation (s ++ s') && n > 0 = [(i, s ++ mkIndent n s')]
      where n = j - (i + length s)
    overlay (j, s') (i, s) | all punctuation (s ++ s') && n > 0 = [(i, s' ++ mkIndent n s)]
      where n = j - (i + length s)
    overlay a b = [a, b]

    punctuation = (`elem` ("(){}[];:, " :: String))

    go i Space = if minify then [] else [(i, " ")]
    go i Empty = []
    go i (Doc s) = [(i, s)]
    go i (Beside d d') = joinBy (\(i, s) (_, s') -> [(i, s ++ s')]) (go i d) (go i d')
    go i (Above d d') = joinBy overlay (go i d) (go i d')
    go i (Indent j d) = go (i + j) d
    go i (Enclose open close d) = go i $ Group $ Above open $ Above d close
    go i (Group d)
        | size ss < 40 = compact ss
        | otherwise    = ss
      where
        ss = go i d
        size = sum . map (length . snd)
        compact [] = []
        compact ((i, x): xs) = [(i, x ++ concatMap snd xs)]

instance IsString Doc where
    fromString = Doc

instance Semigroup Doc where
    Empty <> d = d
    d <> Empty = d
    d <> d' = Beside d d'

instance Monoid Doc where
    mempty = Empty
    mappend = (<>)

infixr 5 $+$
infixr 5 $++$
infixr 6 <+>  -- fixity has to match the one of Semigroup.(<>)

($+$) :: Doc -> Doc -> Doc
Empty $+$ d = d
d $+$ Empty = d
d $+$ d' = Above d d'

-- | Separate by blank line.

($++$) :: Doc -> Doc -> Doc
Empty $++$ d = d
d $++$ Empty = d
d $++$ d' = d `Above` "" `Above` d'

-- | Separate by space that will be removed by minify.
--
-- For non-removable space, use @d <> " " <> d'@.

(<+>) :: Doc -> Doc -> Doc
Empty <+> d = d
d <+> Empty = d
d <+> d' = d `Beside` Space `Beside` d'

text :: String -> Doc
text = Doc

group :: Doc -> Doc
group = Group

indentBy :: Int -> Doc -> Doc
indentBy i Empty = Empty
indentBy i (Indent j d) = Indent (i + j) d
indentBy i d = Indent i d

enclose :: Doc -> Doc -> Doc -> Doc
enclose open close (Enclose o c d) = Enclose (open <> o) (c <> close) d
enclose open close (Indent _ (Enclose o c d)) = Enclose (open <> o) (c <> close) d
enclose open close d = Enclose open close d

----------------------------------------------------------------------------------------------

space :: Doc
space = Space

indent :: Doc -> Doc
indent = indentBy 2

hcat :: [Doc] -> Doc
hcat = foldr (<>) mempty

vcat :: [Doc] -> Doc
vcat = foldr ($+$) mempty

-- | Concatenate vertically, separated by blank lines.

vsep :: [Doc] -> Doc
vsep = foldr ($++$) mempty

punctuate :: Doc -> [Doc] -> Doc
punctuate _ []     = mempty
punctuate p (x:xs) = indent $ vcat $ go x xs
                   where go y []     = [y]
                         go y (z:zs) = (y <> p) : go z zs

parens, brackets, braces :: Doc -> Doc
parens   = enclose "(" ")"
brackets = enclose "[" "]"
braces   = enclose "{" "}"

-- | Apply 'parens' to 'Doc' if boolean is true.
mparens :: Bool -> Doc -> Doc
mparens True  d = parens d
mparens False d = d

----------------------------------------------------------------------------------------------

unescape :: Char -> String
unescape '"'      = "\\\""
unescape '\\'     = "\\\\"
unescape '\n'     = "\\n"
unescape '\r'     = "\\r"
unescape '\x2028' = "\\u2028"
unescape '\x2029' = "\\u2029"
unescape c        = [c]

unescapes :: String -> Doc
unescapes s = text $ concatMap unescape s

-- pretty (n,b) i e pretty-prints e, under n levels of de Bruijn binding
--   if b is true then the output is minified

class Pretty a where
    pretty :: (Nat, Bool, JSModuleStyle) -> a -> Doc

prettyShow :: Pretty a => Bool -> JSModuleStyle -> a -> String
prettyShow minify ms = render minify . pretty (0, minify, ms)

instance Pretty a => Pretty (Maybe a) where
  pretty n = maybe mempty (pretty n)

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty n (x,y) = pretty n x <> ":" <+> pretty n y

-- Pretty-print collections

class Pretties a where
    pretties :: (Nat, Bool, JSModuleStyle) -> a -> [Doc]

instance Pretty a => Pretties [a] where
  pretties n = map (pretty n)

instance Pretty a => Pretties (List1 a) where
  pretties n = pretties n . List1.toList

instance (Pretty a, Pretty b) => Pretties (Map a b) where
  pretties n = pretties n . toAscList

-- Pretty print identifiers

instance Pretty LocalId where
  pretty (n, _, _) (LocalId x) = text $ indexWithDefault __IMPOSSIBLE__ vars (n - x - 1)
    where
      vars = ("": map show [0..]) >>= \s -> map (:s) ['a'..'z']

instance Pretty GlobalId where
  pretty n (GlobalId m) = text $ variableName $ intercalate "_" m

instance Pretty MemberId where
  pretty _ (MemberId s) = "\"" <> unescapes s <> "\""
  pretty n (MemberIndex i comment) = text (show i) <> pretty n comment

instance Pretty Comment where
  pretty _ (Comment "") = mempty
  pretty (_, True, _) _ = mempty
  pretty _ (Comment s) = text $ "/* " ++ s ++ " */"

-- Pretty print expressions

instance Pretty Exp where
  pretty n (Self)            = "exports"
  pretty n (Local x)         = pretty n x
  pretty n (Global m)        = pretty n m
  pretty n (Undefined)       = "undefined"
  pretty n (Null)            = "null"
  pretty n (String s)        = "\"" <> unescapes (T.unpack s) <> "\""
  pretty n (Char c)          = "\"" <> unescapes [c] <> "\""
  pretty n (Integer x)       = "agdaRTS.primIntegerFromString(\"" <> text (show x) <> "\")"
  pretty n (Double x)        = text $ show x
  pretty (n, min, ms) (Lambda x e) =
    mparens (x /= 1) (punctuate "," (pretties (n + x, min, ms) (map LocalId [x-1, x-2 .. 0])))
    <+> "=>" <+> block (n + x, min, ms) e
  pretty n (Object o)        = braces $ punctuate "," $ pretties n o
  pretty n (Array es)        = brackets $ punctuate "," [pretty n c <> pretty n e | (c, e) <- es]
  pretty n (Apply f es)      = pretty n f <> parens (punctuate "," $ pretties n es)
  pretty n (Lookup e l)      = pretty n e <> brackets (pretty n l)
  pretty n (If e f g)        = parens $ pretty n e <> "?" <+> pretty n f <> ":" <+> pretty n g
  pretty n (PreOp op e)      = parens $ text op <> " " <> pretty n e
  pretty n (BinOp e op f)    = parens $ pretty n e <> " " <> text op <> " " <> pretty n f
  pretty n (Const c)         = text c
  pretty n (PlainJS js)      = text js

block :: (Nat, Bool, JSModuleStyle) -> Exp -> Doc
block n e = mparens (doNest e) $ pretty n e
  where
    doNest Object{} = True
    doNest _ = False

modname :: GlobalId -> Doc
modname (GlobalId ms) = text $ "\"" ++ intercalate "." ms ++ "\""

exports :: (Nat, Bool, JSModuleStyle) -> Set JSQName -> [Export] -> Doc
exports n lss [] = Empty
exports n lss es0@(Export ls e : es)
  -- If the parent of @ls@ is already defined (or no parent exists), @ls@ can be defined
  | maybe True (`member` lss) parent =
      "exports" <> hcat (map brackets (pretties n ls)) <+> "=" <+> indent (pretty n e) <> ";" $+$
      exports n (insert ls lss) es
  -- If the parent is not yet defined, first define it as empty object, and then continue with @ls@.
  | otherwise =
      exports n lss $ maybe es0 (\ ls' -> Export ls' (Object mempty) : es0) parent
  where
  parent = List1.nonEmpty $ List1.init ls

instance Pretty [(GlobalId, Export)] where
  pretty n es
    = vcat [ pretty n g <> hcat (map brackets (pretties n ls)) <+> "=" <+> indent (pretty n e) <> ";"
           | (g, Export ls e) <- es ]

instance Pretty Module where
  pretty opt@(n, min, JSCJS) (Module m is es callMain) = vsep
    [ "var agdaRTS" <+> "=" <+> "require(\"agda-rts\");"
    , imports
    , exports opt Set.empty es
    , pretty opt callMain
    ]
    $+$ ""
    where
      imports = vcat [
        "var " <> indent (pretty opt e) <+> "=" <+> "require(" <> modname e <> ");"
        | e <- toList (globals es <> Set.fromList is)
        ]
      les = toList (globals es <> Set.fromList is)
  pretty opt@(n, min, JSAMD) (Module m is es callMain) = vsep
    [ "define(['agda-rts'"
      <+> hcat [ ", " <+> modname e | e <- les ]
      <+> "],"
    , "function(agdaRTS"
      <+> hcat [ ", " <+> pretty opt e | e <- les ]
      <+> ") {"
    , "var exports = {};"
    , exports opt Set.empty es
    , pretty opt callMain
    , "; return exports; });"
    ]
    $+$ "" -- Final newline
    where
      les = toList (globals es <> Set.fromList is)


variableName :: String -> String
variableName s = if isValidJSIdent s then "z_" ++ s else "h_" ++ show (hashString s)

-- | Check if a string is a valid JS identifier. The check ignores keywords
-- as we prepend z_ to our identifiers. The check
-- is conservative and may not admit all valid JS identifiers.

isValidJSIdent :: String -> Bool
isValidJSIdent []     = False
isValidJSIdent (c:cs) = validFirst c && all validOther cs
  where
  validFirst :: Char -> Bool
  validFirst c = isAsciiUpper c || isAsciiLower c || c == '_' || c == '$'

  validOther :: Char -> Bool
  validOther c = validFirst c || isDigit c
