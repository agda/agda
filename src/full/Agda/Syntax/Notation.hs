-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE CPP,
             DeriveDataTypeable,
             DeriveGeneric,
             ScopedTypeVariables #-}

{-| As a concrete name, a notation is a non-empty list of alternating 'IdPart's and holes.
    In contrast to concrete names, holes can be binders.

    Example:
    @
       syntax fmap (λ x → e) xs = for x ∈ xs return e
    @

    The declared notation for @fmap@ is @for_∈_return_@ where the first hole is a binder.
-}

module Agda.Syntax.Notation where

import Control.Applicative
import Control.Monad

import Data.List
import Data.Maybe
import Data.Typeable (Typeable)

import GHC.Generics (Generic)

import Agda.Syntax.Common
import Agda.Syntax.Position

import Agda.Utils.Except ( MonadError(throwError) )
import Agda.Utils.List

import Agda.Utils.Impossible
#include "undefined.h"

-- | Data type constructed in the Happy parser; converted to 'GenPart'
--   before it leaves the Happy code.
data HoleName
  = LambdaHole { _bindHoleName :: RawName
               , holeName      :: RawName }
    -- ^ @\ x -> y@; 1st argument is the bound name (unused for now).
  | ExprHole   { holeName      :: RawName }
    -- ^ Simple named hole with hiding.

-- | Is the hole a binder?
isLambdaHole :: HoleName -> Bool
isLambdaHole (LambdaHole _ _) = True
isLambdaHole _ = False

-- | Notation as provided by the @syntax@ declaration.
type Notation = [GenPart]

-- | Part of a Notation
data GenPart
  = BindHole Int
    -- ^ Argument is the position of the hole (with binding) where the binding should occur.
  | NormalHole (NamedArg () Int)
    -- ^ Argument is where the expression should go.
  | IdPart RawName
  deriving (Typeable, Generic, Show, Eq, Ord)

instance KillRange GenPart where
  killRange p = case p of
    IdPart x     -> IdPart x
    BindHole i   -> BindHole i
    NormalHole x -> NormalHole $ killRange x

-- | Get a flat list of identifier parts of a notation.
stringParts :: Notation -> [RawName]
stringParts gs = [ x | IdPart x <- gs ]

-- | Target argument position of a part (Nothing if it is not a hole).
holeTarget :: GenPart -> Maybe Int
holeTarget (BindHole   n) = Just n
holeTarget (NormalHole n) = Just $ namedArg n
holeTarget IdPart{}       = Nothing

-- | Is the part a hole?
isAHole :: GenPart -> Bool
isAHole = isJust . holeTarget

-- | Is the part a binder?
isBindingHole :: GenPart -> Bool
isBindingHole (BindHole _) = True
isBindingHole _ = False

-- | Classification of notations.

data NotationKind
  = InfixNotation   -- ^ Ex: @_bla_blub_@.
  | PrefixNotation  -- ^ Ex: @_bla_blub@.
  | PostfixNotation -- ^ Ex: @bla_blub_@.
  | NonfixNotation  -- ^ Ex: @bla_blub@.
  | NoNotation
   deriving (Eq, Show)

-- | Classify a notation by presence of leading and/or trailing hole.
notationKind :: Notation -> NotationKind
notationKind []  = NoNotation
notationKind syn =
  case (isAHole $ head syn, isAHole $ last syn) of
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
mkNotation :: [NamedArg c HoleName] -> [RawName] -> Either String Notation
mkNotation _ [] = throwError "empty notation is disallowed"
mkNotation holes ids = do
  unless uniqueHoleNames     $ throwError "syntax must use unique argument names"
  let xs :: Notation = map mkPart ids
  unless (isAlternating xs)  $ throwError "syntax must alternate holes and non-holes"
  unless (isExprLinear xs)   $ throwError "syntax must use holes exactly once"
  unless (isLambdaLinear xs) $ throwError "syntax must use binding holes exactly once"
  return xs
    where
      mkPart ident = fromMaybe (IdPart ident) $ lookup ident holeMap

      holeNumbers   = [0 .. length holes - 1]
      numberedHoles = zip holeNumbers holes

      -- Create a map (association list) from hole names to holes.
      -- A @LambdaHole@ contributes two entries:
      -- both names are mapped to the same number,
      -- but distinguished by BindHole vs. NormalHole.
      holeMap = do
        (i, h) <- numberedHoles
        let normalHole = NormalHole $ setArgColors [] $ fmap (i <$) h
        case namedArg h of
          ExprHole y     -> [(y, normalHole)]
          LambdaHole x y -> [(x, BindHole i), (y, normalHole)]

      -- Check whether all hole names are distinct.
      -- The hole names are the keys of the @holeMap@.
      uniqueHoleNames = distinct $ map fst holeMap

      isExprLinear   xs = sort [ namedArg x | NormalHole x <- xs] == holeNumbers
      isLambdaLinear xs = sort [ x          | BindHole   x <- xs] == [ i | (i, h) <- numberedHoles, isLambdaHole (namedArg h) ]

      isAlternating :: [GenPart] -> Bool
      isAlternating []       = __IMPOSSIBLE__
      isAlternating [x]      = True
      isAlternating (x:y:xs) = isAHole x /= isAHole y && isAlternating (y:xs)

-- | No notation by default.
defaultNotation, noNotation :: Notation
defaultNotation = []
noNotation = []
