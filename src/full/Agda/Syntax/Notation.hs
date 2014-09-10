{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Agda.Syntax.Notation where

import Control.Applicative
import Control.Monad

import Data.List
import Data.Maybe
import Data.Typeable (Typeable)

import Agda.Syntax.Common

import Agda.Utils.Except ( MonadError(throwError) )

import Agda.Utils.Impossible
#include "../undefined.h"

{-| A name is a non-empty list of alternating 'Id's and 'Hole's. A normal name
    is represented by a singleton list, and operators are represented by a list
    with 'Hole's where the arguments should go. For instance: @[Hole,Id "+",Hole]@
    is infix addition.

    Equality and ordering on @Name@s are defined to ignore range so same names
    in different locations are equal.
-}

-- | Data type constructed in the Happy parser; converted to 'GenPart'
-- before it leaves the Happy code.
data HoleName = LambdaHole RawName RawName -- ^ (\x -> y) ; 1st argument is the bound name (unused for now)
              | ExprHole RawName           -- ^ simple named hole with hiding

-- | Target of a hole
holeName (LambdaHole _ n) = n
holeName (ExprHole n) = n

type Notation = [GenPart]

-- | Part of a Notation
data GenPart = BindHole Int                 -- ^ Argument is the position of the hole (with binding) where the binding should occur.
             | NormalHole (NamedArg () Int) -- ^ Argument is where the expression should go
             | IdPart RawName
  deriving (Typeable, Show, Eq)

-- | Get a flat list of identifier parts of a notation.
stringParts :: Notation -> [RawName]
stringParts gs = [ x | IdPart x <- gs ]

-- | Target argument position of a part (Nothing if it is not a hole)
holeTarget :: GenPart -> Maybe Int
holeTarget (BindHole n) = Just n
holeTarget (NormalHole n) = Just (namedArg n)
holeTarget (IdPart _) = Nothing

-- | Is the part a hole?
isAHole :: GenPart -> Bool
isAHole = isJust . holeTarget

isBindingHole (BindHole _) = True
isBindingHole _ = False

isLambdaHole (LambdaHole _ _) = True
isLambdaHole _ = False


-- | From notation with names to notation with indices.
mkNotation :: [NamedArg c HoleName] -> [RawName] -> Either String Notation
mkNotation _ [] = throwError "empty notation is disallowed"
mkNotation holes ids = do
  unless (uniqueNames holes) $ throwError "syntax must use unique argument names"
  let xs = map mkPart ids
  unless (isAlternating xs)  $ throwError "syntax must alternate holes and non-holes"
  unless (isExprLinear xs)   $ throwError "syntax must use holes exactly once"
  unless (isLambdaLinear xs) $ throwError "syntax must use binding holes exactly once"
  return xs
    where mkPart ident = fromMaybe (IdPart ident) $ lookup ident holeMap

          holeMap = concat $ zipWith mkHole [0..] holes
            where mkHole i h =
                    case namedArg h of
                      ExprHole x     -> [(x, normalHole)]
                      LambdaHole x y -> [(x, BindHole i), (y, normalHole)]
                    where normalHole = NormalHole $ setArgColors [] $ fmap (i <$) h

          uniqueNames hs = nub xs == xs
            where xs = concatMap (names . namedArg) hs
                  names (ExprHole x)     = [x]
                  names (LambdaHole x y) = [x, y]

          isExprLinear   xs = sort [ namedArg x | NormalHole x <- xs] == [ i | (i, h) <- zip [0..] holes ]
          isLambdaLinear xs = sort [ x          | BindHole   x <- xs] == [ i | (i, h) <- zip [0..] holes, isLambdaHole (namedArg h) ]

          isAlternating :: [GenPart] -> Bool
          isAlternating [] = __IMPOSSIBLE__
          isAlternating [x] = True
          isAlternating (x:y:xs) = isAHole x /= isAHole y && isAlternating (y:xs)


-- | No notation by default
defaultNotation = []
noNotation = []
