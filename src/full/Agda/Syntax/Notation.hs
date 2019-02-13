{-# LANGUAGE CPP                 #-}
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

import Control.DeepSeq
import Control.Monad

import qualified Data.List as List
import Data.Maybe

import Data.Data (Data)

import Agda.Syntax.Common
import Agda.Syntax.Position

import Agda.Utils.Except ( MonadError(throwError) )
import Agda.Utils.List

import Agda.Utils.Impossible
#include "undefined.h"

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

-- | Notation as provided by the @syntax@ declaration.
type Notation = [GenPart]

-- | Part of a Notation
data GenPart
  = BindHole Range (Ranged Int)
    -- ^ Argument is the position of the hole (with binding) where the binding should occur.
    --   First range is the rhs range and second is the binder.
  | NormalHole Range (NamedArg (Ranged Int))
    -- ^ Argument is where the expression should go.
  | WildHole (Ranged Int)
    -- ^ An underscore in binding position.
  | IdPart RString
  deriving (Data, Show)

instance Eq GenPart where
  BindHole _ i   == BindHole _ j   = i == j
  NormalHole _ x == NormalHole _ y = x == y
  WildHole i     == WildHole j     = i == j
  IdPart x       == IdPart y       = x == y
  _              == _              = False

instance Ord GenPart where
  BindHole _ i   `compare` BindHole _ j   = i `compare` j
  NormalHole _ x `compare` NormalHole _ y = x `compare` y
  WildHole i     `compare` WildHole j     = i `compare` j
  IdPart x       `compare` IdPart y       = x `compare` y
  BindHole{}     `compare` _              = LT
  _              `compare` BindHole{}     = GT
  NormalHole{}   `compare` _              = LT
  _              `compare` NormalHole{}   = GT
  WildHole{}     `compare` _              = LT
  _              `compare` WildHole{}     = GT

instance HasRange GenPart where
  getRange p = case p of
    IdPart x       -> getRange x
    BindHole r _   -> r
    WildHole i     -> getRange i
    NormalHole r _ -> r

instance SetRange GenPart where
  setRange r p = case p of
    IdPart x       -> IdPart x
    BindHole _ i   -> BindHole r i
    WildHole i     -> WildHole i
    NormalHole _ i -> NormalHole r i

instance KillRange GenPart where
  killRange p = case p of
    IdPart x       -> IdPart $ killRange x
    BindHole _ i   -> BindHole noRange $ killRange i
    WildHole i     -> WildHole $ killRange i
    NormalHole _ x -> NormalHole noRange $ killRange x

instance NFData GenPart where
  rnf (BindHole _ a)   = rnf a
  rnf (NormalHole _ a) = rnf a
  rnf (WildHole a)     = rnf a
  rnf (IdPart a)       = rnf a

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

noNotation :: Notation
noNotation = []
