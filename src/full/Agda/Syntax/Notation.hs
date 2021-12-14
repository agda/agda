

{-| As a concrete name, a notation is a non-empty list of alternating 'IdPart's and holes.
    In contrast to concrete names, holes can be binders.

    Example:
    @
       syntax fmap (λ x → e) xs = for x ∈ xs return e
    @

    The declared notation for @fmap@ is @for_∈_return_@ where the first hole is a binder.
-}

module Agda.Syntax.Notation where

import Prelude hiding (null)

import Control.DeepSeq
import Control.Monad
import Control.Monad.Except

import qualified Data.List as List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import GHC.Generics (Generic)

import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Pretty()
import Agda.Syntax.Position

import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Utils.Pretty

import Agda.Utils.Impossible

-- | Data type constructed in the Happy parser; converted to
-- 'NotationPart' before it leaves the Happy code.
data HoleName
  = LambdaHole { _bindHoleNames :: List1 RString
               , holeName       :: RString
               }
    -- ^ @λ x₁ … xₙ → y@: The first argument contains the bound names.
  | ExprHole   { holeName      :: RString }
    -- ^ Simple named hole with hiding.

-- | Is the hole a binder?
isLambdaHole :: HoleName -> Bool
isLambdaHole (LambdaHole _ _) = True
isLambdaHole _ = False

-- | Get a flat list of identifier parts of a notation.
stringParts :: Notation -> [String]
stringParts gs = [ rangedThing x | IdPart x <- gs ]

-- | Target argument position of a part (Nothing if it is not a hole).
holeTarget :: NotationPart -> Maybe Int
holeTarget (VarPart _ n)  = Just $ holeNumber $ rangedThing n
holeTarget (WildPart n)   = Just $ holeNumber $ rangedThing n
holeTarget (HolePart _ n) = Just $ rangedThing $ namedArg n
holeTarget IdPart{}       = Nothing

-- | Is the part a hole?
isAHole :: NotationPart -> Bool
isAHole HolePart{} = True
isAHole VarPart{}  = False
isAHole WildPart{} = False
isAHole IdPart{}   = False

-- | Is the part a binder?
isBinder :: NotationPart -> Bool
isBinder HolePart{} = False
isBinder VarPart{}  = True
isBinder WildPart{} = True
isBinder IdPart{}   = False

-- | Classification of notations.

data NotationKind
  = InfixNotation   -- ^ Ex: @_bla_blub_@.
  | PrefixNotation  -- ^ Ex: @_bla_blub@.
  | PostfixNotation -- ^ Ex: @bla_blub_@.
  | NonfixNotation  -- ^ Ex: @bla_blub@.
  | NoNotation
   deriving (Eq, Show, Generic)

-- | Classify a notation by presence of leading and/or trailing
-- /normal/ holes.
notationKind :: Notation -> NotationKind
notationKind []  = NoNotation
notationKind (h:syn) =
  case (isAHole h, isAHole $ last1 h syn) of
    (True , True ) -> InfixNotation
    (True , False) -> PostfixNotation
    (False, True ) -> PrefixNotation
    (False, False) -> NonfixNotation

-- | From notation with names to notation with indices.
--
--   An example (with some parts of the code omitted):
--   The lists
--   @["for", "x", "∈", "xs", "return", "e"]@
--   and
--   @['LambdaHole' ("x" :| []) "e", 'ExprHole' "xs"]@
--   are mapped to the following notation:
--   @
--      [ 'IdPart' "for"    , 'VarPart' ('BoundVariablePosition' 0 0)
--      , 'IdPart' "∈"      , 'HolePart' 1
--      , 'IdPart' "return" , 'HolePart' 0
--      ]
--   @
mkNotation :: [NamedArg HoleName] -> [RString] -> Either String Notation
mkNotation _ [] = throwError "empty notation is disallowed"
mkNotation holes ids = do
  unless uniqueHoleNames     $ throwError "syntax must use unique argument names"
  let xs :: Notation = map mkPart ids
  unless (noAdjacentHoles xs)  $ throwError $ concat
     [ "syntax must not contain adjacent holes ("
     , prettyHoles
     , ")"
     ]
  unless (isExprLinear xs)   $ throwError "syntax must use holes exactly once"
  unless (isLambdaLinear xs) $ throwError "syntax must use binding holes exactly once"
  -- Andreas, 2018-10-18, issue #3285:
  -- syntax that is just a single hole is ill-formed and crashes the operator parser
  when   (isSingleHole xs)   $ throwError "syntax cannot be a single hole"
  return $ insertWildParts xs
    where
      holeNames :: [RString]
      holeNames = map namedArg holes >>= \case
        LambdaHole _ y -> [y]
        ExprHole y     -> [y]

      prettyHoles :: String
      prettyHoles = List.unwords $ map (rawNameToString . rangedThing) holeNames

      mkPart ident = maybe (IdPart ident) (`withRangeOf` ident) $ lookup ident holeMap

      holeNumbers   = [0 .. length holes - 1]

      numberedHoles :: [(Int, NamedArg HoleName)]
      numberedHoles = zip holeNumbers holes

      -- The WildParts don't correspond to anything in the right-hand side so
      -- we add them next to their corresponding body. Slightly subtle: due to
      -- the way the operator parsing works they can't be added first or last.
      insertWildParts :: [NotationPart] -> [NotationPart]
      insertWildParts xs = foldr ins xs wilds
        where
          wilds = [ i | (_, WildPart i) <- holeMap ]

          ins w (HolePart r h : hs)
            | namedArg h == fmap holeNumber w =
              HolePart r h : WildPart w : hs
          ins w (h : hs) = h : insBefore w hs
          ins _ [] = __IMPOSSIBLE__

          insBefore w (HolePart r h : hs)
            | namedArg h == fmap holeNumber w =
              WildPart w : HolePart r h : hs
          insBefore w (h : hs) = h : insBefore w hs
          insBefore _ [] = __IMPOSSIBLE__

      -- A map (association list) from hole names to notation parts. A
      -- @LambdaHole@ contributes one or more entries, one @HolePart@
      -- and zero or more @VarPart@s or @WildParts@, all mapped to the
      -- same number.
      holeMap :: [(RString, NotationPart)]
      holeMap = do
        (i, h) <- numberedHoles
        let ri x   = Ranged (getRange x) i
            rp x n = Ranged (getRange x) $
                     BoundVariablePosition
                       { holeNumber = i
                       , varNumber  = n
                       }
            hole y = HolePart noRange $ fmap (ri y <$) h
                              -- This range is filled in by mkPart.
        case namedArg h of
          ExprHole y      -> [(y, hole y)]
          LambdaHole xs y ->
            [(y, hole y)] ++
            map
              (\(n, x) -> case rangedThing x of
                "_" -> (x, WildPart (rp x n))
                _   -> (x, VarPart noRange (rp x n)))
                                   -- Filled in by mkPart.
               (zip [0..] $ List1.toList xs)

      -- Check whether all hole names are distinct.
      -- The hole names are the keys of the @holeMap@.
      uniqueHoleNames = distinct [ x | (x, _) <- holeMap, rangedThing x /= "_" ]

      isExprLinear xs =
        List.sort [ i | x <- xs, isAHole x, let Just i = holeTarget x ]
          ==
        holeNumbers

      isLambdaLinear xs =
        List.sort [ rangedThing x | VarPart _ x <- xs ]
          ==
        [ BoundVariablePosition { holeNumber = i, varNumber = v }
        | (i, h) <- numberedHoles
        , LambdaHole vs _ <- [namedArg h]
        , (v, x) <- zip [0..] $ map rangedThing $ List1.toList vs
        , x /= "_"
        ]

      noAdjacentHoles :: [NotationPart] -> Bool
      noAdjacentHoles =
        noAdj .
        filter (\h -> case h of
                   HolePart{} -> True
                   IdPart{}   -> True
                   _          -> False)
        where
        noAdj []       = __IMPOSSIBLE__
        noAdj [x]      = True
        noAdj (x:y:xs) =
          not (isAHole x && isAHole y) &&
          noAdj (y:xs)

      isSingleHole :: [NotationPart] -> Bool
      isSingleHole = \case
        [ IdPart{} ] -> False
        [ _hole ]    -> True
        _            -> False

-- | All the notation information related to a name.
data NewNotation = NewNotation
  { notaName  :: QName
  , notaNames :: Set A.Name
    -- ^ The names the syntax and/or fixity belong to.
    --
    -- Invariant: The set is non-empty. Every name in the list matches
    -- 'notaName'.
  , notaFixity :: Fixity
    -- ^ Associativity and precedence (fixity) of the names.
  , notation :: Notation
    -- ^ Syntax associated with the names.
  , notaIsOperator :: Bool
    -- ^ True if the notation comes from an operator (rather than a
    -- syntax declaration).
  } deriving (Show, Generic)

instance LensFixity NewNotation where
  lensFixity f nota = f (notaFixity nota) <&> \ fx -> nota { notaFixity = fx }

-- | If an operator has no specific notation, then it is computed from
-- its name.
namesToNotation :: QName -> A.Name -> NewNotation
namesToNotation q n = NewNotation
  { notaName       = q
  , notaNames      = Set.singleton n
  , notaFixity     = f
  , notation       = if null syn then syntaxOf (unqualify q) else syn
  , notaIsOperator = null syn
  }
  where Fixity' f syn _ = A.nameFixity n

-- | Replace 'noFixity' by 'defaultFixity'.
useDefaultFixity :: NewNotation -> NewNotation
useDefaultFixity n
  | notaFixity n == noFixity = n { notaFixity = defaultFixity }
  | otherwise                = n

-- | Return the 'IdPart's of a notation, the first part qualified,
--   the other parts unqualified.
--   This allows for qualified use of operators, e.g.,
--   @M.for x ∈ xs return e@, or @x ℕ.+ y@.
notationNames :: NewNotation -> [QName]
notationNames (NewNotation q _ _ parts _) =
  zipWith ($) (reQualify : repeat QName) [simpleName $ rangedThing x | IdPart x <- parts ]
  where
    -- The qualification of @q@.
    modules     = List1.init (qnameParts q)
    -- Putting the qualification onto @x@.
    reQualify x = List.foldr Qual (QName x) modules

-- | Create a 'Notation' (without binders) from a concrete 'Name'.
--   Does the obvious thing:
--   'Hole's become 'HolePart's, 'Id's become 'IdParts'.
--   If 'Name' has no 'Hole's, it returns 'noNotation'.
syntaxOf :: Name -> Notation
syntaxOf y
  | isOperator y = mkSyn 0 $ List1.toList $ nameNameParts y
  | otherwise    = noNotation
  where
    -- Turn a concrete name into a Notation,
    -- numbering the holes from left to right.
    -- Result will have no 'BindingHole's.
    mkSyn :: Int -> [NamePart] -> Notation
    mkSyn n []          = []
    mkSyn n (Hole : xs) = HolePart noRange (defaultNamedArg $ unranged n) : mkSyn (1 + n) xs
    mkSyn n (Id x : xs) = IdPart (unranged x) : mkSyn n xs

-- | Merges 'NewNotation's that have the same precedence level and
-- notation, with two exceptions:
--
-- * Operators and notations coming from syntax declarations are kept
--   separate.
--
-- * If /all/ instances of a given 'NewNotation' have the same
--   precedence level or are \"unrelated\", then they are merged. They
--   get the given precedence level, if any, and otherwise they become
--   unrelated (but related to each other).
--
-- If 'NewNotation's that are merged have distinct associativities,
-- then they get 'NonAssoc' as their associativity.
--
-- Precondition: No 'A.Name' may occur in more than one list element.
-- Every 'NewNotation' must have the same 'notaName'.
--
-- Postcondition: No 'A.Name' occurs in more than one list element.
mergeNotations :: [NewNotation] -> [NewNotation]
mergeNotations =
  map merge .
  concatMap groupIfLevelsMatch .
  groupOn (\n -> ( notation n
                 , notaIsOperator n
                 ))
  where
  groupIfLevelsMatch :: [NewNotation] -> [[NewNotation]]
  groupIfLevelsMatch []         = __IMPOSSIBLE__
  groupIfLevelsMatch ns@(n : _) =
    if allEqual (map fixityLevel related)
    then [sameAssoc (sameLevel ns)]
    else map (: []) ns
    where
    -- Fixities of operators whose precedence level is not Unrelated.
    related = mapMaybe ((\f -> case fixityLevel f of
                                Unrelated  -> Nothing
                                Related {} -> Just f)
                              . notaFixity) ns

    -- Precondition: All related operators have the same precedence
    -- level.
    --
    -- Gives all unrelated operators the same level.
    sameLevel = map (set (_notaFixity . _fixityLevel) level)
      where
      level = case related of
        f : _ -> fixityLevel f
        []    -> Unrelated

    -- If all related operators have the same associativity, then the
    -- unrelated operators get the same associativity, and otherwise
    -- all operators get the associativity NonAssoc.
    sameAssoc = map (set (_notaFixity . _fixityAssoc) assoc)
      where
      assoc = case related of
        f : _ | allEqual (map fixityAssoc related) -> fixityAssoc f
        _                                          -> NonAssoc

  merge :: [NewNotation] -> NewNotation
  merge []         = __IMPOSSIBLE__
  merge ns@(n : _) = n { notaNames = Set.unions $ map notaNames ns }

-- | Lens for 'Fixity' in 'NewNotation'.

_notaFixity :: Lens' Fixity NewNotation
_notaFixity f r = f (notaFixity r) <&> \x -> r { notaFixity = x }

-- * Sections

-- | Sections, as well as non-sectioned operators.

data NotationSection = NotationSection
  { sectNotation  :: NewNotation
  , sectKind      :: NotationKind
    -- ^ For non-sectioned operators this should match the notation's
    -- 'notationKind'.
  , sectLevel     :: Maybe FixityLevel
    -- ^ Effective precedence level. 'Nothing' for closed notations.
  , sectIsSection :: Bool
    -- ^ 'False' for non-sectioned operators.
  }
  deriving (Show, Generic)

-- | Converts a notation to a (non-)section.

noSection :: NewNotation -> NotationSection
noSection n = NotationSection
  { sectNotation  = n
  , sectKind      = notationKind (notation n)
  , sectLevel     = Just (fixityLevel (notaFixity n))
  , sectIsSection = False
  }


-- * Pretty printing

instance Pretty NewNotation where
  pretty (NewNotation x _xs fx nota isOp) = hsepWith "=" px pn
    where
    px = fsep [ if isOp then empty else "syntax" , pretty fx , pretty x ]
    pn = if isOp then empty else pretty nota

instance Pretty NotationKind where pretty = pshow

instance Pretty NotationSection where
  pretty (NotationSection nota kind mlevel isSection)
    | isSection = fsep
        [ "section"
        , pretty kind
        , maybe empty pretty mlevel
        , pretty nota
        ]
    | otherwise = pretty nota

-- NFData instances

instance NFData NotationKind
instance NFData NewNotation
instance NFData NotationSection
