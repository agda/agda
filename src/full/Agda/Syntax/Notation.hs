{-# LANGUAGE DeriveDataTypeable  #-}

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

import Control.Monad

import qualified Data.List as List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Pretty()
import Agda.Syntax.Position

import Agda.Utils.Except ( MonadError(throwError) )
import Agda.Utils.Lens
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Utils.Pretty

import Agda.Utils.Impossible

-- | Data type constructed in the Happy parser; converted to 'GenPart'
--   before it leaves the Happy code.
data HoleName
  = LambdaHole { _bindHoleName :: RString
               , holeName      :: RString }
    -- ^ @\ x -> y@; 1st argument is the bound name (unused for now).
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
holeTarget :: GenPart -> Maybe Int
holeTarget (BindHole _   n) = Just $ rangedThing n
holeTarget (WildHole     n) = Just $ rangedThing n
holeTarget (NormalHole _ n) = Just $ rangedThing $ namedArg n
holeTarget IdPart{}         = Nothing

-- | Is the part a hole? WildHoles don't count since they don't correspond to
--   anything the user writes.
isAHole :: GenPart -> Bool
isAHole BindHole{}   = True
isAHole NormalHole{} = True
isAHole WildHole{}   = False
isAHole IdPart{}     = False

-- | Is the part a normal hole?
isNormalHole :: GenPart -> Bool
isNormalHole NormalHole{} = True
isNormalHole BindHole{}   = False
isNormalHole WildHole{}   = False
isNormalHole IdPart{}     = False

-- | Is the part a binder?
isBindingHole :: GenPart -> Bool
isBindingHole BindHole{} = True
isBindingHole WildHole{} = True
isBindingHole _          = False

-- | Classification of notations.

data NotationKind
  = InfixNotation   -- ^ Ex: @_bla_blub_@.
  | PrefixNotation  -- ^ Ex: @_bla_blub@.
  | PostfixNotation -- ^ Ex: @bla_blub_@.
  | NonfixNotation  -- ^ Ex: @bla_blub@.
  | NoNotation
   deriving (Eq, Show)

-- | Classify a notation by presence of leading and/or trailing
-- /normal/ holes.
notationKind :: Notation -> NotationKind
notationKind []  = NoNotation
notationKind syn =
  case (isNormalHole $ head syn, isNormalHole $ last syn) of
    (True , True ) -> InfixNotation
    (True , False) -> PostfixNotation
    (False, True ) -> PrefixNotation
    (False, False) -> NonfixNotation

-- | From notation with names to notation with indices.
--
--   Example:
--   @
--      ids   = ["for", "x", "∈", "xs", "return", "e"]
--      holes = [ LambdaHole "x" "e",  ExprHole "xs" ]
--   @
--   creates the notation
--   @
--      [ IdPart "for"    , BindHole 0
--      , IdPart "∈"      , NormalHole 1
--      , IdPart "return" , NormalHole 0
--      ]
--   @
mkNotation :: [NamedArg HoleName] -> [RString] -> Either String Notation
mkNotation _ [] = throwError "empty notation is disallowed"
mkNotation holes ids = do
  unless uniqueHoleNames     $ throwError "syntax must use unique argument names"
  let xs :: Notation = map mkPart ids
  unless (isAlternating xs)  $ throwError $ concat
     [ "syntax must alternate holes ("
     , prettyHoles
     , ") and non-holes ("
     , prettyNonHoles xs
     , ")"
     ]
  unless (isExprLinear xs)   $ throwError "syntax must use holes exactly once"
  unless (isLambdaLinear xs) $ throwError "syntax must use binding holes exactly once"
  -- Andreas, 2018-10-18, issue #3285:
  -- syntax that is just a single hole is ill-formed and crashes the operator parser
  when   (isSingleHole xs)   $ throwError "syntax cannot be a single hole"
  return $ insertWildHoles xs
    where
      holeNames :: [RString]
      holeNames = map namedArg holes >>= \case
        LambdaHole x y -> [x, y]
        ExprHole y     -> [y]

      prettyHoles :: String
      prettyHoles = List.unwords $ map (rawNameToString . rangedThing) holeNames

      nonHoleNames :: Notation -> [RString]
      nonHoleNames xs = flip mapMaybe xs $ \case
        WildHole{}   -> Just $ unranged "_"
        IdPart x     -> Just x
        BindHole{}   -> Nothing
        NormalHole{} -> Nothing

      prettyNonHoles :: Notation -> String
      prettyNonHoles = List.unwords . map (rawNameToString . rangedThing) . nonHoleNames

      mkPart ident = maybe (IdPart ident) (`withRangeOf` ident) $ lookup ident holeMap

      holeNumbers   = [0 .. length holes - 1]

      numberedHoles :: [(Int, NamedArg HoleName)]
      numberedHoles = zip holeNumbers holes

      -- The WildHoles don't correspond to anything in the right-hand side so
      -- we add them next to their corresponding body. Slightly subtle: due to
      -- the way the operator parsing works they can't be added first or last.
      insertWildHoles :: [GenPart] -> [GenPart]
      insertWildHoles xs = foldr ins xs wilds
        where
          wilds = [ i | (_, WildHole i) <- holeMap ]
          ins w (NormalHole r h : hs)
            | namedArg h == w = NormalHole r h : WildHole w : hs
          ins w (h : hs) = h : insBefore w hs
          ins _ [] = __IMPOSSIBLE__

          insBefore w (NormalHole r h : hs)
            | namedArg h == w = WildHole w : NormalHole r h : hs
          insBefore w (h : hs) = h : insBefore w hs
          insBefore _ [] = __IMPOSSIBLE__

      -- Create a map (association list) from hole names to holes.
      -- A @LambdaHole@ contributes two entries:
      -- both names are mapped to the same number,
      -- but distinguished by BindHole vs. NormalHole.
      holeMap :: [(RString, GenPart)]
      holeMap = do
        (i, h) <- numberedHoles    -- v This range is filled in by mkPart
        let ri x = Ranged (getRange x) i
            normalHole y = NormalHole noRange $ fmap (ri y <$) h
        case namedArg h of
          ExprHole y       -> [(y, normalHole y)]
          LambdaHole x y
            | "_" <- rangedThing x -> [(x, WildHole (ri x)),         (y, normalHole y)]
            | otherwise            -> [(x, BindHole noRange (ri x)), (y, normalHole y)]
                                                 -- Filled in by mkPart

      -- Check whether all hole names are distinct.
      -- The hole names are the keys of the @holeMap@.
      uniqueHoleNames = distinct [ x | (x, _) <- holeMap, rangedThing x /= "_" ]

      isExprLinear   xs = List.sort [ i | x <- xs, isNormalHole x, let Just i = holeTarget x ] == holeNumbers
      isLambdaLinear xs = List.sort [ rangedThing x | BindHole _ x <- xs ] ==
                          [ i | (i, h) <- numberedHoles,
                                LambdaHole x _ <- [namedArg h], rangedThing x /= "_" ]

      isAlternating :: [GenPart] -> Bool
      isAlternating []       = __IMPOSSIBLE__
      isAlternating [x]      = True
      isAlternating (x:y:xs) = isAHole x /= isAHole y && isAlternating (y:xs)

      isSingleHole :: [GenPart] -> Bool
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
  } deriving Show

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
  zipWith ($) (reQualify : repeat QName) [Name noRange InScope [Id $ rangedThing x] | IdPart x <- parts ]
  where
    -- The qualification of @q@.
    modules     = List1.init (qnameParts q)
    -- Putting the qualification onto @x@.
    reQualify x = List.foldr Qual (QName x) modules

-- | Create a 'Notation' (without binders) from a concrete 'Name'.
--   Does the obvious thing:
--   'Hole's become 'NormalHole's, 'Id's become 'IdParts'.
--   If 'Name' has no 'Hole's, it returns 'noNotation'.
syntaxOf :: Name -> Notation
syntaxOf (NoName _ _)    = noNotation
syntaxOf (Name _ _ [_])  = noNotation
syntaxOf (Name _ _ xs)   = mkSyn 0 xs
  where
    -- Turn a concrete name into a Notation,
    -- numbering the holes from left to right.
    -- Result will have no 'BindingHole's.
    mkSyn :: Int -> [NamePart] -> Notation
    mkSyn n []          = []
    mkSyn n (Hole : xs) = NormalHole noRange (defaultNamedArg $ unranged n) : mkSyn (1 + n) xs
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
  deriving Show

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
