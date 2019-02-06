{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}

-- | Preprocessors for literate code formats.

module Agda.Syntax.Parser.Literate
  ( literateProcessors
  , literateExtsShortList
  , literateSrcFile
  , literateTeX
  , literateRsT
  , literateMd
  , literateOrg
  , illiterate
  , atomizeLayers
  , Processor
  , Layers
  , Layer(..)
  , LayerRole(..)
  , isCode
  , isCodeLayer
  )
  where

import Prelude hiding (getLine)
import Data.Char (isSpace, isControl)
import Data.List (isPrefixOf)
import Agda.Syntax.Common
import Agda.Syntax.Position
import Text.Regex.TDFA

#include "undefined.h"
import Agda.Utils.Impossible

-- | Role of a character in the file.

data LayerRole = Markup | Comment | Code
  deriving (Show, Eq)

-- | A sequence of characters in a file playing the same role.

data Layer = Layer
  { layerRole    :: LayerRole
  , interval     :: Interval
  , layerContent :: String
  } deriving Show

-- | A list of contiguous layers.

type Layers = [Layer]

instance HasRange Layer where
  getRange = getRange . interval

-- | Annotates a tokenized string with position information.

mkLayers :: Position -> [(LayerRole, String)] -> Layers
mkLayers pos []            = emptyLiterate pos
mkLayers pos ((_,"") : xs) = mkLayers pos xs
                             -- Empty layers are ignored.
mkLayers pos ((ty,s) : xs) =
  Layer ty (Interval pos next) s : mkLayers next xs
  where
  next = movePosByString pos s

unMkLayers :: Layers -> [(LayerRole, String)]
unMkLayers = map ((,) <$> layerRole <*> layerContent)

atomizeLayers :: Layers -> [(LayerRole, Char)]
atomizeLayers = (>>= fmap <$> ((,) . fst) <*> snd) . unMkLayers

-- | Type of a literate preprocessor:
--   Invariants:
--
--   > f : Processor
--
--   prop> f pos s /= []
--
--   prop> f pos s >>= layerContent == s

type Processor = Position -> String -> [Layer]

literateSrcFile :: [Layer] -> SrcFile
literateSrcFile []                    = __IMPOSSIBLE__
literateSrcFile (Layer{interval} : _) = getIntervalFile interval

-- | List of valid extensions for literate Agda files, and their
--   corresponding preprocessors.
--
--   If you add new extensions, remember to update test/Utils.hs so
--   that test cases ending in the new extensions are found.

literateProcessors :: [(String, (Processor, FileType))]
literateProcessors =
  ((,) <$> (".lagda" ++) . fst <*> snd) <$>
    [ (""    , (literateTeX, TexFileType))
    , (".rst", (literateRsT, RstFileType))
    , (".tex", (literateTeX, TexFileType))
    , (".md",  (literateMd,  MdFileType ))
    , (".org", (literateOrg, OrgFileType))
    ]

-- | Returns @True@ if the role corresponds to Agda code.

isCode :: LayerRole -> Bool
isCode Code    = True
isCode Markup  = False
isCode Comment = False

-- | Returns @True@ if the layer contains Agda code.

isCodeLayer :: Layer -> Bool
isCodeLayer = isCode . layerRole

-- | Blanks the non-code parts of a given file, preserving positions of
--   characters corresponding to code. This way, there is a direct
--   correspondence between source positions and positions in the
--   processed result.

illiterate :: [Layer] -> String
illiterate xs = concat
  [ (if isCode layerRole then id else bleach) layerContent
  | Layer{layerRole, layerContent} <- xs
  ]

-- | Replaces non-space characters in a string with spaces.

bleach :: String -> String
bleach s = map go s
  where
  go c | isSpace c = c
  go _             = ' '

-- | Check if a character is a blank character.

isBlank :: Char -> Bool
isBlank = (&&) <$> isSpace <*> not . (== '\n')

-- | Short list of extensions for literate Agda files.
--   For display purposes.

literateExtsShortList :: [String]
literateExtsShortList = [".lagda"]

-- | Breaks a list just /after/ an element satisfying the predicate is
--   found.
--
--   >>> break1 even [1,3,5,2,4,7,8]
--   ([1,3,5,2],[4,7,8])

break1 :: (a -> Bool) -> [a] -> ([a],[a])
break1 _ []           =  ([], [])
break1 p (x:xs) | p x = (x:[],xs)
break1 p (x:xs)       = let (ys,zs) = break1 p xs in (x:ys,zs)

-- | Returns a tuple consisting of the first line of the input, and the rest
--   of the input.

getLine :: String -> (String, String)
getLine = break1 (== '\n')

-- | Canonical decomposition of an empty literate file.

emptyLiterate :: Position -> [Layer]
emptyLiterate pos = [Layer Markup (Interval pos pos) ""]

-- | Create a regular expression that:
--   - Must match the whole string
--   - Works across line boundaries

rex :: String -> Regex
rex s =
  makeRegexOpts blankCompOpt{newSyntax = True} blankExecOpt $
    "\\`" ++ s ++ "\\'"

-- | Preprocessor for literate TeX.

literateTeX :: Position -> String -> [Layer]
literateTeX pos s = mkLayers pos (tex s)
  where
  tex :: String -> [(LayerRole, String)]
  tex [] = []
  tex s  =
    let (line, rest) = getLine s in
    case r_begin `matchM` line of
      Just (getAllTextSubmatches -> [_, pre, _, markup, whitespace]) ->
        (Comment, pre) : (Markup, markup) :
        (Code, whitespace) : code rest
      Just _  -> __IMPOSSIBLE__
      Nothing -> (Comment, line):tex rest

  r_begin = rex "(([^\\%]|\\\\.)*)(\\\\begin\\{code\\}[^\n]*)(\n)?"

  code :: String -> [(LayerRole, String)]
  code [] = []
  code s  =
    let (line, rest) = getLine s in
    case r_end `matchM` line of
      Just (getAllTextSubmatches -> [_, code, markup, post]) ->
        (Code, code) : (Markup, markup) : (Comment, post) : tex rest
      Just _  -> __IMPOSSIBLE__
      Nothing -> (Code, line) : code rest

  r_end = rex "([[:blank:]]*)(\\\\end\\{code\\})(.*)"

-- | Preprocessor for Markdown.

literateMd :: Position -> String -> [Layer]
literateMd pos s = mkLayers pos$ md s
  where
  md :: String -> [(LayerRole, String)]
  md [] = []
  md s  =
    let (line, rest) = getLine s in
    case md_begin `matchM` line of
      Just (getAllTextSubmatches -> [_, pre, markup, _]) ->
        (Comment, pre) : (Markup, markup) : code rest
      Just _  -> __IMPOSSIBLE__
      Nothing ->
        (Comment, line) :
        if md_begin_other `match` line
        then code_other rest
        else md rest

  md_begin       = rex "(.*)([[:space:]]*```(agda)?[[:space:]]*)"
  md_begin_other = rex "[[:space:]]*```[a-zA-Z0-9-]*[[:space:]]*"

  code :: String -> [(LayerRole, String)]
  code [] = []
  code s  =
    let (line, rest) = getLine s in
    case md_end `matchM` line of
      Just (getAllTextSubmatches -> [_, markup]) ->
        (Markup, markup) : md rest
      Just _  -> __IMPOSSIBLE__
      Nothing -> (Code, line) : code rest

  -- A non-Agda code block.
  code_other :: String -> [(LayerRole, String)]
  code_other [] = []
  code_other s  =
    let (line, rest) = getLine s in
    (Comment, line) :
    if md_end `match` line
    then md rest
    else code_other rest

  md_end = rex "([[:space:]]*```[[:space:]]*)"

-- | Preprocessor for reStructuredText.

literateRsT :: Position -> String -> [Layer]
literateRsT pos s = mkLayers pos$ rst s
  where
  rst :: String -> [(LayerRole, String)]
  rst [] = []
  rst s  = maybe_code s

  maybe_code s =
    if r_comment `match` line then
      not_code
    else case r_code `match` line of
      []                         -> not_code
      [[_, before, "::", after]] ->
        -- Code starts
        if null before || isBlank (last before) then
          (Markup, line) : code rest
        else
          (Comment, before ++ ":") : (Markup, ":" ++ after) : code rest
      _ -> __IMPOSSIBLE__
    where
    (line, rest) = getLine s
    not_code     = (Comment, line) : rst rest

  -- Finds the next indented block in the input.
  code :: String -> [(LayerRole, String)]
  code [] = []
  code s  =
    let (line, rest) = getLine s in
    if all isSpace line then
      (Markup, line) : code rest
    else
      let xs = takeWhile isBlank line in
      if null xs
      then maybe_code s
      else (Code, line) : indented xs rest

  -- Process an indented block.
  indented :: String -> String -> [(LayerRole, String)]
  indented _   [] = []
  indented ind s  =
    let (line, rest) = getLine s in
    if all isSpace line then
      (Code, line) : indented ind rest
    else if ind `isPrefixOf` line then
      (Code, line) : indented ind rest
    else
      maybe_code s

  -- Beginning of a code block.
  r_code = rex "(.*)(::)([[:space:]]*)"

  -- Beginning of a comment block.
  r_comment = rex "[[:space:]]*\\.\\.([[:space:]].*)?"

-- | Preprocessor for Org mode documents.

literateOrg :: Position -> String -> [Layer]
literateOrg pos s = mkLayers pos$ org s
  where
  org :: String -> [(LayerRole, String)]
  org [] = []
  org s  =
    let (line, rest) = getLine s in
    if org_begin `match` line then
      (Markup, line) : code rest
    else
      (Comment, line) : org rest

  -- Valid: #+begin_src agda2 :tangle yes
  -- Valid: #+begin_src agda2
  -- Invalid: #+begin_src adga2-foo
  org_begin = rex' "\\`(.*)([[:space:]]*\\#\\+begin_src agda2[[:space:]]+)"

  code :: String -> [(LayerRole, String)]
  code [] = []
  code s  =
    let (line, rest) = getLine s in
    if org_end `match` line then
      (Markup, line) : org rest
    else
      (Code, line) : code rest

  org_end = rex' "\\`([[:space:]]*\\#\\+end_src[[:space:]]*)(.*)"

  -- Explicit type annotation required to disambiguate source.
  rex' :: String -> Regex
  -- Source blocks start with `#+begin_src` but the casing does not matter.
  rex' = makeRegexOpts blankCompOpt{newSyntax = True, caseSensitive = False} blankExecOpt
