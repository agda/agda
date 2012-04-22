{-# LANGUAGE CPP, DeriveDataTypeable #-}


module Agda.Syntax.Notation where

import Control.Applicative
import Control.Monad (when)
import Control.Monad.Error (throwError)
import Data.List
import Data.Maybe
import Data.Typeable (Typeable)

import System.FilePath

import Test.QuickCheck

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Utils.FileName
import Agda.Utils.Pretty

#include "../undefined.h"
import Agda.Utils.Impossible

{-| A name is a non-empty list of alternating 'Id's and 'Hole's. A normal name
    is represented by a singleton list, and operators are represented by a list
    with 'Hole's where the arguments should go. For instance: @[Hole,Id "+",Hole]@
    is infix addition.

    Equality and ordering on @Name@s are defined to ignore range so same names
    in different locations are equal.
-}

-- | Data type constructed in the Happy parser; converted to 'GenPart'
-- before it leaves the Happy code.
data HoleName = LambdaHole String String -- ^ (\x -> y) ; 1st argument is the bound name (unused for now)
              | ExprHole String          -- ^ simple named hole

-- | Target of a hole
holeName (LambdaHole _ n) = n
holeName (ExprHole n) = n

type Notation = [GenPart]

-- | Part of a Notation
data GenPart = BindHole Int  -- ^ Argument is the position of the hole (with binding) where the binding should occur.
             | NormalHole Int -- ^ Argument is where the expression should go
             | IdPart String
  deriving (Typeable, Show, Eq)

-- | Get a flat list of identifier parts of a notation.
stringParts :: Notation -> [String]
stringParts gs = [ x | IdPart x <- gs ]

-- | Target argument position of a part (Nothing if it is not a hole)
holeTarget (BindHole n) = Just n
holeTarget (NormalHole n) = Just n
holeTarget (IdPart _) = Nothing

-- | Is the part a hole?
isAHole :: GenPart -> Bool
isAHole = isJust . holeTarget

isBindingHole (BindHole _) = True
isBindingHole _ = False

isLambdaHole (LambdaHole _ _) = True
isLambdaHole _ = False


-- | From notation with names to notation with indices.
mkNotation :: [HoleName] -> [String] -> Either String Notation
mkNotation _ [] = throwError "empty notation is disallowed"
mkNotation holes ids = do
  xs <- mapM mkPart ids
  when (not (isAlternating xs)) $ throwError "syntax must alternate holes and non-holes"
  when (not (isExprLinear xs)) $ throwError "syntax must use holes exactly once"
  when (not (isLambdaLinear xs)) $ throwError "syntax must use binding holes exactly once"
  return xs
    where mkPart ident =
             case (findIndices (\x -> ident == holeName x) holes,
                   findIndices (\x -> case x of LambdaHole ident' _ -> ident == ident';_ -> False) holes)  of
                           ([],[x])   -> return $ BindHole x
                           ([x], [])  -> return $ NormalHole x
                           ([], []) -> return $ IdPart ident
                           _ -> throwError "hole names must be unique"

          isExprLinear   xs = sort [ x | NormalHole x <- xs] == [ i | (i,h) <- zip [0..] holes ]
          isLambdaLinear xs = sort [ x | BindHole   x <- xs] == [ i | (i,h) <- zip [0..] holes, isLambdaHole h ]


          isAlternating :: [GenPart] -> Bool
          isAlternating [] = __IMPOSSIBLE__
          isAlternating [x] = True
          isAlternating (x:y:xs) = isAHole x /= isAHole y && isAlternating (y:xs)


-- | No notation by default
defaultNotation = []
noNotation = []
