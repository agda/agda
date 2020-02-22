{-# LANGUAGE CPP                        #-}
-- | Types used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Precise
  ( -- * Files
    Aspect(..)
  , NameKind(..)
  , OtherAspect(..)
  , Aspects(..)
  , DefinitionSite(..)
  , TokenBased(..)
  , File(..)
  , HighlightingInfo
    -- ** Creation
  , parserBased
  , singleton
  , several
    -- ** Merging
  , merge
    -- ** Inspection
  , smallestPos
  , toMap
    -- * Compressed files
  , CompressedFile(..)
  , compressedFileInvariant
  , compress
  , decompress
  , noHighlightingInRange
    -- ** Creation
  , singletonC
  , severalC
  , splitAtC
  , selectC
    -- ** Inspection
  , smallestPosC
    -- ** Merge
  , mergeC
  ) where

import Control.Arrow (second)
import Control.Monad

import Data.Function
import qualified Data.List as List
import Data.Maybe
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Agda.Syntax.Position as P
import qualified Agda.Syntax.Common as Common
import qualified Agda.Syntax.Concrete as SC

import Agda.Interaction.Highlighting.Range

import Agda.Utils.String
import Agda.Utils.List

------------------------------------------------------------------------
-- Files

-- | Syntactic aspects of the code. (These cannot overlap.)

data Aspect
  = Comment
  | Keyword
  | String
  | Number
  | Symbol                     -- ^ Symbols like forall, =, ->, etc.
  | PrimitiveType              -- ^ Things like Set and Prop.
  | Name (Maybe NameKind) Bool -- ^ Is the name an operator part?
  | Pragma                     -- ^ Text occurring in pragmas that
                               --   does not have a more specific
                               --   aspect.
  | Background                 -- ^ Non-code contents in literate Agda
  | Markup
    -- ^ Delimiters used to separate the Agda code blocks from the
    -- other contents in literate Agda
    deriving (Eq, Show)

-- | @NameKind@s are figured out during scope checking.

data NameKind
  = Bound                         -- ^ Bound variable.
  | Generalizable                 -- ^ Generalizable variable.
                                  --   (This includes generalizable
                                  --   variables that have been
                                  --   generalized).
  | Constructor Common.Induction  -- ^ Inductive or coinductive constructor.
  | Datatype
  | Field                         -- ^ Record field.
  | Function
  | Module                        -- ^ Module name.
  | Postulate
  | Primitive                     -- ^ Primitive.
  | Record                        -- ^ Record type.
  | Argument                      -- ^ Named argument, like x in {x = v}
  | Macro                         -- ^ Macro.
    deriving (Eq, Show)

-- | Other aspects, generated by type checking.
--   (These can overlap with each other and with 'Aspect's.)

data OtherAspect
  = Error
  | DottedPattern
  | UnsolvedMeta
  | UnsolvedConstraint
    -- ^ Unsolved constraint not connected to meta-variable. This
    -- could for instance be an emptyness constraint.
  | TerminationProblem
  | PositivityProblem
  | Deadcode
    -- ^ Used for highlighting unreachable clauses, unreachable RHS
    -- (because of an absurd pattern), etc.
  | ShadowingInTelescope
    -- ^ Used for shadowed repeated variable names in telescopes.
  | CoverageProblem
  | IncompletePattern
    -- ^ When this constructor is used it is probably a good idea to
    -- include a 'note' explaining why the pattern is incomplete.
  | TypeChecks
    -- ^ Code which is being type-checked.
  | MissingDefinition
    -- ^ Function declaration without matching definition
  -- NB: We put CatchallClause last so that it is overwritten by other,
  -- more important, aspects in the emacs mode.
  | CatchallClause
  | ConfluenceProblem
    deriving (Eq, Ord, Show, Enum, Bounded)

-- | Meta information which can be associated with a
-- character\/character range.

data Aspects = Aspects
  { aspect       :: Maybe Aspect
  , otherAspects :: Set OtherAspect
  , note         :: Maybe String
    -- ^ This note, if present, can be displayed as a tool-tip or
    -- something like that. It should contain useful information about
    -- the range (like the module containing a certain identifier, or
    -- the fixity of an operator).
  , definitionSite :: Maybe DefinitionSite
    -- ^ The definition site of the annotated thing, if applicable and
    --   known.
  , tokenBased :: !TokenBased
    -- ^ Is this entry token-based?
  }
  deriving Show

data DefinitionSite = DefinitionSite
  { defSiteModule :: SC.TopLevelModuleName
      -- ^ The defining module.
  , defSitePos    :: Int
      -- ^ The file position in that module. File positions are
      -- counted from 1.
  , defSiteHere   :: Bool
      -- ^ Has this @DefinitionSite@ been created at the defining site of the name?
  , defSiteAnchor :: Maybe String
      -- ^ A pretty name for the HTML linking.
  }
  deriving Show

instance Eq DefinitionSite where
  DefinitionSite m p _ _ == DefinitionSite m' p' _ _ = m == m' && p == p'

-- | Is the highlighting \"token-based\", i.e. based only on
-- information from the lexer?

data TokenBased = TokenBased | NotOnlyTokenBased
  deriving (Eq, Show)

instance Eq Aspects where
  Aspects a o _ d t == Aspects a' o' _ d' t' =
    (a, o, d, t) == (a', o', d', t')

-- | A 'File' is a mapping from file positions to meta information.
--
-- The first position in the file has number 1.

newtype File = File { mapping :: IntMap Aspects }
  deriving (Eq, Show)

-- | Syntax highlighting information.

type HighlightingInfo = CompressedFile

------------------------------------------------------------------------
-- Creation

-- | A variant of 'mempty' with 'tokenBased' set to
-- 'NotOnlyTokenBased'.

parserBased :: Aspects
parserBased = mempty { tokenBased = NotOnlyTokenBased }

-- | @'singleton' rs m@ is a file whose positions are those in @rs@,
-- and in which every position is associated with @m@.

singleton :: Ranges -> Aspects -> File
singleton rs m = File {
 mapping = IntMap.fromAscList [ (p, m) | p <- rangesToPositions rs ] }

-- | Like 'singleton', but with several 'Ranges' instead of only one.

several :: [Ranges] -> Aspects -> File
several rs m = mconcat $ map (\r -> singleton r m) rs

------------------------------------------------------------------------
-- Merging

instance Semigroup TokenBased where
  b1@NotOnlyTokenBased <> b2 = b1
  TokenBased           <> b2 = b2

instance Monoid TokenBased where
  mempty  = TokenBased
  mappend = (<>)

-- | Merges meta information.

mergeAspects :: Aspects -> Aspects -> Aspects
mergeAspects m1 m2 = Aspects
  { aspect       = (mplus `on` aspect) m1 m2
  , otherAspects = (Set.union `on` otherAspects) m1 m2
  , note         = case (note m1, note m2) of
      (Just n1, Just n2) -> Just $
         if n1 == n2
           then n1
           else addFinalNewLine n1 ++ "----\n" ++ n2
      (Just n1, Nothing) -> Just n1
      (Nothing, Just n2) -> Just n2
      (Nothing, Nothing) -> Nothing
  , definitionSite = (mplus `on` definitionSite) m1 m2
  , tokenBased     = tokenBased m1 <> tokenBased m2
  }

instance Semigroup Aspects where
  (<>) = mergeAspects

instance Monoid Aspects where
  mempty = Aspects
    { aspect         = Nothing
    , otherAspects   = Set.empty
    , note           = Nothing
    , definitionSite = Nothing
    , tokenBased     = mempty
    }
  mappend = (<>)

-- | Merges files.

merge :: File -> File -> File
merge f1 f2 =
  File { mapping = (IntMap.unionWith mappend `on` mapping) f1 f2 }

instance Semigroup File where
  (<>) = merge

instance Monoid File where
  mempty  = File { mapping = IntMap.empty }
  mappend = (<>)

------------------------------------------------------------------------
-- Inspection

-- | Returns the smallest position, if any, in the 'File'.

smallestPos :: File -> Maybe Int
smallestPos = fmap (fst . fst) . IntMap.minViewWithKey . mapping

-- | Convert the 'File' to a map from file positions (counting from 1)
-- to meta information.

toMap :: File -> IntMap Aspects
toMap = mapping

------------------------------------------------------------------------
-- Compressed files

-- | A compressed 'File', in which consecutive positions with the same
-- 'Aspects' are stored together.

newtype CompressedFile =
  CompressedFile { ranges :: [(Range, Aspects)] }
  deriving (Eq, Show)

-- | Invariant for compressed files.
--
-- Note that these files are not required to be /maximally/
-- compressed, because ranges are allowed to be empty, and the
-- 'Aspects's in adjacent ranges are allowed to be equal.

compressedFileInvariant :: CompressedFile -> Bool
compressedFileInvariant (CompressedFile []) = True
compressedFileInvariant (CompressedFile f)  =
  all rangeInvariant rs &&
  all (not . empty) rs &&
  and (zipWith (<=) (map to $ init rs) (map from $ tail rs))
  where rs = map fst f

-- | Compresses a file by merging consecutive positions with equal
-- meta information into longer ranges.

compress :: File -> CompressedFile
compress f =
  CompressedFile $ map join $ groupBy' p (IntMap.toAscList $ mapping f)
  where
  p (pos1, m1) (pos2, m2) = pos2 == pos1 + 1 && m1 == m2
  join pms = ( Range { from = head ps, to = last ps + 1 }
             , head ms
             )
    where (ps, ms) = unzip pms

-- | Decompresses a compressed file.

decompress :: CompressedFile -> File
decompress =
  File .
  IntMap.fromList .
  concatMap (\(r, m) -> [ (p, m) | p <- rangeToPositions r ]) .
  ranges

-- | Clear any highlighting info for the given ranges. Used to make sure
--   unsolved meta highlighting overrides error highlighting.
noHighlightingInRange :: Ranges -> CompressedFile -> CompressedFile
noHighlightingInRange rs (CompressedFile hs) =
    CompressedFile $ concatMap clear hs
  where
    clear (r, i) =
      case minus (Ranges [r]) rs of
        Ranges [] -> []
        Ranges rs -> [ (r, i) | r <- rs ]

------------------------------------------------------------------------
-- Operations that work directly with compressed files

-- | @'singletonC' rs m@ is a file whose positions are those in @rs@,
-- and in which every position is associated with @m@.

singletonC :: Ranges -> Aspects -> CompressedFile
singletonC (Ranges rs) m =
  CompressedFile [(r, m) | r <- rs, not (empty r)]

-- | Like 'singletonR', but with a list of 'Ranges' instead of a
-- single one.

severalC :: [Ranges] -> Aspects -> CompressedFile
severalC rss m = mconcat $ map (\rs -> singletonC rs m) rss

-- | Merges compressed files.

mergeC :: CompressedFile -> CompressedFile -> CompressedFile
mergeC (CompressedFile f1) (CompressedFile f2) =
  CompressedFile (mrg f1 f2)
  where
  mrg []             f2             = f2
  mrg f1             []             = f1
  mrg (p1@(i1,_):f1) (p2@(i2,_):f2)
    | to i1 <= from i2 = p1 : mrg f1      (p2:f2)
    | to i2 <= from i1 = p2 : mrg (p1:f1) f2
    | to i1 <= to i2   = ps1 ++ mrg f1 (ps2 ++ f2)
    | otherwise        = ps1 ++ mrg (ps2 ++ f1) f2
      where (ps1, ps2) = fuse p1 p2

  -- Precondition: The ranges are overlapping.
  fuse (i1, m1) (i2, m2) =
    ( fix [ (Range { from = a, to = b }, ma)
          , (Range { from = b, to = c }, mergeAspects m1 m2)
          ]
    , fix [ (Range { from = c, to = d }, md)
          ]
    )
    where
    [(a, ma), (b, _), (c, _), (d, md)] =
      List.sortBy (compare `on` fst)
             [(from i1, m1), (to i1, m1), (from i2, m2), (to i2, m2)]
    fix = filter (not . empty . fst)

instance Semigroup CompressedFile where
  (<>) = mergeC

instance Monoid CompressedFile where
  mempty  = CompressedFile []
  mappend = (<>)

-- | @splitAtC p f@ splits the compressed file @f@ into @(f1, f2)@,
-- where all the positions in @f1@ are @< p@, and all the positions
-- in @f2@ are @>= p@.

splitAtC :: Int -> CompressedFile ->
            (CompressedFile, CompressedFile)
splitAtC p f = (CompressedFile f1, CompressedFile f2)
  where
  (f1, f2) = split $ ranges f

  split [] = ([], [])
  split (rx@(r,x) : f)
    | p <= from r = ([], rx:f)
    | to r <= p   = (rx:f1, f2)
    | otherwise   = ([ (toP, x) ], (fromP, x) : f)
    where (f1, f2) = split f
          toP      = Range { from = from r, to = p    }
          fromP    = Range { from = p,      to = to r }

selectC :: P.Range -> CompressedFile -> CompressedFile
selectC r cf = cf'
  where
    empty         = (0,0)
    (from, to)    = fromMaybe empty (rangeToEndPoints r)
    (_, (cf', _)) = (second (splitAtC to)) . splitAtC from $ cf


-- | Returns the smallest position, if any, in the 'CompressedFile'.

smallestPosC :: CompressedFile -> Maybe Int
smallestPosC (CompressedFile [])           = Nothing
smallestPosC (CompressedFile ((r, _) : _)) = Just (from r)
