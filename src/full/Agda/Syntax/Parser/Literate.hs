{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
-- | Preprocessors for literate code formats
module Agda.Syntax.Parser.Literate (
  literateProcessors,
  literateExts,
  literateExtsShortList,
  literateSrcFile,
  literateTeX,
  literateRsT,
  illiterate,
  isCode,
  Processor,
  Layer(..),
  LayerType(..)
  )
  where

import Prelude hiding (getLine)
import Data.Char (isSpace, isControl)
import Data.List (isPrefixOf)
import Agda.Syntax.Position
import Text.Regex.TDFA

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>),(<*>))
#endif

#include "undefined.h"
import Agda.Utils.Impossible

data LayerType = Markup | Comment | Code
                deriving (Show, Eq)

data Layer = Layer {
  layerType    :: LayerType
 ,interval     :: Interval
 ,layerContent :: String
} deriving (Show)

instance HasRange Layer where
  getRange = getRange . interval

-- | Annotates a tokenized string with position information.
mkLayers :: Position -> [(LayerType, String)] -> [Layer]
mkLayers pos [] = emptyLiterate pos
mkLayers pos ((_,""):xs) = mkLayers pos xs
mkLayers pos ((ty,s):xs) = let next = movePosByString pos s in
                           (Layer ty (Interval pos next) s):(mkLayers next xs)

-- | Checks if a layer corresponds to Agda code
isCode :: Layer -> Bool
isCode Layer{layerType=Code}    = True
isCode Layer{layerType=Markup } = False
isCode Layer{layerType=Comment} = False

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
literateSrcFile [] = __IMPOSSIBLE__
literateSrcFile (Layer{interval}:_) = getIntervalFile interval

-- | List of valid extensions for literate Agda files, and their corresponding
--   preprocessors.
--
--   If you add new extensions, remember to update test/Utils.hs so that test
--   cases ending in the new extensions are found.
literateProcessors :: [(String, Processor)]
literateProcessors = map ((,) <$> (".lagda" ++) . fst <*> snd)
                 [(""    , literateTeX)
                 ,(".rst", literateRsT)
                 ,(".tex", literateTeX)
                 ]

-- | Blanks the non-code parts of a given file, preserving positions of
--   characters corresponding to code. This way, there is a direct
--   correspondence between source positions and positions in the
--   processed result.
illiterate :: [Layer] -> String
illiterate xs = concat [
  (if isCode m then id else bleach) layerContent
  | m@Layer{layerContent} <- xs]

-- | Replaces non-space characters in a string with spaces.
bleach :: String -> String
bleach s = map go s
  where
    go c | isSpace c = c
    go _             = ' '

-- | Check if a character is a blank character.
isBlank :: Char -> Bool
isBlank = (&&) <$> isSpace <*> not . (== '\n')

-- | Possible extensions for a literate Agda file
literateExts :: [String]
literateExts = map fst literateProcessors

-- | Short list of extensions for literate Agda files
--   For display purposes.
literateExtsShortList :: [String]
literateExtsShortList = [".lagda"]

-- | break a list just *after* an element satisfying the predicate is found
--
--   >>> break1 even [1,3,5,2,4,7,8]
--   ([1,3,5,2],[4,7,8])
--
break1 :: (a -> Bool) -> [a] -> ([a],[a])
break1 _ []           =  ([], [])
break1 p (x:xs) | p x = (x:[],xs)
break1 p (x:xs)       = let (ys,zs) = break1 p xs in (x:ys,zs)

-- | Returns a tuple consisting of the first line of the input, and the rest
--   of the input.
getLine :: String -> (String, String)
getLine = break1 (== '\n')

-- | Canonical decomposition of an empty literate file
emptyLiterate :: Position -> [Layer]
emptyLiterate pos = [Layer (Markup) (Interval pos pos) ""]

-- | Create a regular expression that:
--   - Must match the whole string
--   - Works across line boundaries
rex :: String -> Regex
rex s = makeRegexOpts blankCompOpt{newSyntax = True} blankExecOpt$ "\\`" ++ s ++ "\\'"

-- | Preprocessor for literate TeX
literateTeX :: Position -> String -> [Layer]
literateTeX pos s = mkLayers pos$ tex s
  where
  tex :: String -> [(LayerType, String)]
  tex [] = []
  tex s  = let (line, rest) = getLine s in
    case r_begin `matchM` line of
      Just (getAllTextSubmatches -> [_, pre, markup]) ->
        (Comment, pre):(Markup, markup):code rest
      Just _                 -> __IMPOSSIBLE__
      Nothing                -> (Comment, line):tex rest

  r_begin = rex "(.*)([[:space:]]*\\\\begin\\{code\\}[[:space:]]*)"


  code :: String -> [(LayerType, String)]
  code [] = []
  code s = let (line, rest) = getLine s in
    case r_end `matchM` line of
      Just (getAllTextSubmatches -> [_, markup, post]) ->
        (Markup, markup):(Comment, post):tex rest
      Just _ -> __IMPOSSIBLE__
      Nothing             -> (Code, line):code rest

  r_end   = rex "([[:space:]]*\\\\end\\{code\\}[[:space:]]*)(.*)"


-- | Preprocessor for reStructuredText
literateRsT :: Position -> String -> [Layer]
literateRsT pos s = mkLayers pos$ rst s
  where
  rst :: String -> [(LayerType, String)]
  rst [] = []
  rst s  = maybe_code s

  maybe_code s =
    if r_comment `match` line then
      not_code
    else case r_code `match` line of
      []      -> not_code
      [[_, before, "::", after]] ->
        -- Code starts
          if null before || isBlank (last before) then
             (Markup,  line):code rest
          else
             (Comment, before ++ ":"):(Markup, ':':after):code rest

      _ -> __IMPOSSIBLE__
    where
      (line, rest) = getLine s
      not_code = (Comment, line):rst rest


  -- | Finds the next indented block in the input
  code :: String -> [(LayerType, String)]
  code [] = []
  code s = let (line, rest) = getLine s in
    if all isSpace line then
      (Markup, line):(code rest)
    else
      let (xs,ys) = span isBlank line in
      case xs of
        [] -> maybe_code s
        _  -> (Code, line):
              (indented xs rest)

  -- | Process an indented block
  indented :: String -> String -> [(LayerType, String)]
  indented _   [] = []
  indented ind s  = let (line, rest) = getLine s in
      if all isSpace line then
        (Code, line):(indented ind rest)
      else if ind `isPrefixOf` line then
        (Code, line):(indented ind rest)
      else
        maybe_code s

  -- | Beginning of a code block
  r_code = rex "(.*)(::)([[:space:]]*)"

  -- | Beginning of a comment block
  r_comment = rex "[[:space:]]*\\.\\.([[:space:]].*)?"
