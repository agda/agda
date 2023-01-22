
{-| Pretty printing functions.
-}
module Agda.Utils.Pretty
    ( module Agda.Utils.Pretty
    , module Text.PrettyPrint.Annotated
    -- This re-export can be removed once <GHC-8.4 is dropped.
    , module Data.Semigroup
    ) where

import Prelude hiding (null)

import qualified Data.Foldable as Fold
import Data.Int (Int32)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word64)

import qualified Text.PrettyPrint.Annotated.HughesPJ as Ph
import qualified Text.PrettyPrint.Annotated as P
import Text.PrettyPrint.Annotated hiding (Doc, TextDetails(Str), empty, (<>), sep, fsep, hsep, hcat, vcat, punctuate)
import Data.Semigroup ((<>))

import Agda.Utils.Float
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Pretty.Aspect

import Agda.Utils.Impossible

-- * Pretty class

-- | The pretty-printer generates documents annotated by a
-- 'PrintingAspect'. We abbreviate the type of annotated documents as
-- simply 'Doc'.

type Doc = P.Doc PrintingAspect

-- | While 'Show' is for rendering data in Haskell syntax,
--   'Pretty' is for displaying data to the world, i.e., the
--   user and the environment.
--
--   Atomic data has no inner document structure, so just
--   implement 'pretty' as @pretty a = text $ ... a ...@.

class Pretty a where
  pretty      :: a -> Doc
  prettyPrec  :: Int -> a -> Doc
  prettyList  :: [a] -> Doc

  pretty      = prettyPrec 0
  prettyPrec  = const pretty
  prettyList  = brackets . prettyList_

-- | Use instead of 'show' when printing to world.

prettyShow :: Pretty a => a -> String
prettyShow = render . pretty

-- * Pretty instances

instance Pretty Bool    where pretty = text . show
instance Pretty Int     where pretty = text . show
instance Pretty Int32   where pretty = text . show
instance Pretty Integer where pretty = text . show
instance Pretty Word64  where pretty = text . show
instance Pretty Double  where pretty = text . toStringWithoutDotZero
instance Pretty Text    where pretty = text . T.unpack

instance Pretty Char where
  pretty c = text [c]
  prettyList = text

instance a ~ PrintingAspect => Pretty (P.Doc a) where
  pretty = id

instance Pretty () where
  pretty _ = P.empty

instance Pretty a => Pretty (Maybe a) where
  prettyPrec p Nothing  = "(nothing)"
  prettyPrec p (Just x) = prettyPrec p x

instance Pretty a => Pretty [a] where
  pretty = prettyList

instance Pretty a => Pretty (List1 a) where
  pretty = prettyList . List1.toList

instance Pretty IntSet where
  pretty = prettySet . IntSet.toList

instance Pretty a => Pretty (Set a) where
  pretty = prettySet . Set.toList

instance Pretty a => Pretty (IntMap a) where
  pretty = prettyMap . IntMap.toList

instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty = prettyMap . Map.toList

-- * Generalizing the original type from list to Foldable

sep, fsep, hsep, hcat, vcat :: Foldable t => t Doc -> Doc
sep  = P.sep  . Fold.toList
fsep = P.fsep . Fold.toList
hsep = P.hsep . Fold.toList
hcat = P.hcat . Fold.toList
vcat = P.vcat . Fold.toList

punctuate :: Foldable t => Doc -> t Doc -> [Doc]
punctuate d = P.punctuate d . Fold.toList

-- * 'Doc' utilities

pwords :: String -> [Doc]
pwords = map text . words

fwords :: String -> Doc
fwords = fsep . pwords

-- | Separate, but only if both separees are not null.

hsepWith :: Doc -> Doc -> Doc -> Doc
hsepWith sep d1 d2
  | null d2   = d1
  | null d1   = d2
  | otherwise = d1 <+> sep <+> d2

-- | Comma separated list, without the brackets.
prettyList_ :: Pretty a => [a] -> Doc
prettyList_ = fsep . punctuate comma . map pretty

-- | Pretty print a set.
prettySet :: Pretty a => [a] -> Doc
prettySet = braces . prettyList_

-- | Pretty print an association list.
prettyMap :: (Pretty k, Pretty v) => [(k,v)] -> Doc
prettyMap = braces . fsep . punctuate comma . map prettyAssign

-- | Pretty print a single association.
prettyAssign :: (Pretty k, Pretty v) => (k,v) -> Doc
prettyAssign (k, v) = sep [ prettyPrec 1 k <+> "->", nest 2 $ pretty v ]

-- ASR (2016-12-13): In pretty >= 1.1.2.0 the below function 'mparens'
-- is called 'maybeParens'. I didn't use that name due to the issue
-- https://github.com/haskell/pretty/issues/40.

-- | Apply 'parens' to 'Doc' if boolean is true.
mparens :: Bool -> Doc -> Doc
mparens True  = parens
mparens False = id

-- | Only wrap in parens if not 'empty'
parensNonEmpty :: Doc -> Doc
parensNonEmpty d = if null d then empty else parens d

-- | @align max rows@ lays out the elements of @rows@ in two columns,
-- with the second components aligned. The alignment column of the
-- second components is at most @max@ characters to the right of the
-- left-most column.
--
-- Precondition: @max > 0@.

align :: Int -> [(String, Doc)] -> Doc
align max rows =
  vcat $ map (\(s, d) -> text s $$ nest (maxLen + 1) d) $ rows
  where maxLen = maximum $ 0 : filter (< max) (map (length . fst) rows)

-- | Handles strings with newlines properly (preserving indentation)
multiLineText :: String -> Doc
multiLineText = vcat . map text . lines

infixl 6 <?>
-- | @a <?> b = hang a 2 b@
(<?>) :: Doc -> Doc -> Doc
a <?> b = hang a 2 b

-- | @pshow = text . show@
pshow :: Show a => a -> Doc
pshow = text . show

singPlural :: Sized a => a -> c -> c -> c
singPlural xs singular plural = if natSize xs == 1 then singular else plural

-- | Used for with-like 'telescopes'

prefixedThings :: Doc -> [Doc] -> Doc
prefixedThings kw = \case
  []           -> P.empty
  (doc : docs) -> fsep $ (kw <+> doc) : map ("|" <+>) docs

-- * Syntax highlighting

withAspect :: PrintingAspect -> Doc -> Doc
withAspect = P.annotate

hiComment, hiKeyword, hiString, hiNumber, hiHole, hiSymbol, hiPrimitiveType,
  hiPragma, hiDatatype, hiPostulate, hiRecord, hiField, hiFunction, hiPrimitive,
  hiArgument, hiMacro, hiConstructor, hiInteraction :: Doc -> Doc

hiComment       = withAspect (Highlight Comment)
hiKeyword       = withAspect (Highlight Keyword)
hiString        = withAspect (Highlight String)
hiNumber        = withAspect (Highlight Number)
hiHole          = withAspect (Highlight Hole)
hiSymbol        = withAspect (Highlight Symbol)
hiPrimitiveType = withAspect (Highlight PrimitiveType)
hiPragma        = withAspect (Highlight Pragma)
hiInteraction   = withAspect (Highlight Interaction)
hiDatatype      = withAspect (Highlight (Name (Just Datatype) False))
hiPostulate     = withAspect (Highlight (Name (Just Postulate) False))
hiRecord        = withAspect (Highlight (Name (Just Record) False))
hiField         = withAspect (Highlight (Name (Just Field) False))
hiFunction      = withAspect (Highlight (Name (Just Function) False))
hiPrimitive     = withAspect (Highlight (Name (Just Primitive) False))
hiArgument      = withAspect (Highlight (Name (Just Argument) False))
hiMacro         = withAspect (Highlight (Name (Just Macro) False))
hiConstructor   = withAspect (Highlight (Name (Just (Constructor ())) False))

hiTooltip :: String -> Doc -> Doc
hiTooltip s = withAspect (WithTooltip s)

renderAnsi3Bit :: Doc -> String
renderAnsi3Bit =
  Ph.renderDecorated to'
    -- Always clear after an aspect:
    (\_ -> reset)
  where
    reset, red, green, yellow, blue, magenta, cyan  :: String
    reset   = "\ESC[0m"
    red     = "\ESC[31m"
    green   = "\ESC[32m"
    yellow  = "\ESC[33m"
    blue    = "\ESC[34m"
    magenta = "\ESC[35m"
    cyan    = "\ESC[36m"
    bold    = "\ESC[1"

    to' :: PrintingAspect -> String
    to' (Highlight x)       = to x
    to' (TriggerCallback _) = ""
    to' (WithTooltip _)     = ""

    to :: Aspect' a -> String
    to Comment = reset
    to Keyword = yellow
    to String = green
    to Number = green
    to Hole = reset
    to Symbol = reset
    to PrimitiveType = bold ++ blue
    to (Name nm _) = case nm of
      Just Function        -> blue
      Just Datatype        -> bold ++ blue
      Just Record          -> bold ++ blue
      Just Primitive       -> bold ++ blue
      Just Postulate       -> blue
      Just (Constructor _) -> bold ++ green
      Just Argument        -> reset
      Just Macro           -> cyan
      _                    -> reset
    to Pragma      = reset
    to Background  = reset
    to Markup      = reset
    to Interaction = reset
