{-# LANGUAGE CPP, DeriveDataTypeable #-}


module Agda.Syntax.Notation where

import Control.Applicative

import Data.List
import Data.Maybe
import Data.Generics (Typeable, Data)

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
data GenPart = BindHole Int  -- ^ Unused for now
             | NormalHole Int -- ^ Argument is where the expression should go
             | IdPart String
  deriving (Data, Typeable, Show, Eq)

-- | Target argument position of a part (Nothing if it is not a hole)
holeTarget (BindHole n) = Just n
holeTarget (NormalHole n) = Just n
holeTarget (IdPart _) = Nothing

-- | Is the part a hole?
isAHole :: GenPart -> Bool
isAHole = isJust . holeTarget

isBindingHole (BindHole _) = True
isBindingHole _ = False

isAlternating :: [GenPart] -> Bool
isAlternating [] = __IMPOSSIBLE__
isAlternating [x] = True
isAlternating (x:y:xs) = isAHole x /= isAHole y && isAlternating (y:xs)

-- | From notation with names to notation with indices.
mkNotation :: [HoleName] -> [String] -> Either String Notation
mkNotation _ [] = fail "empty notation is disallowed"
mkNotation holes ids = do
  xs <- mapM mkPart ids
  if isAlternating xs then return xs else fail "notation must alternate holes and non-holes"
    where mkPart ident = 
             case (findIndex (\x -> ident == holeName x) holes, 
                   findIndex (\x -> case x of LambdaHole ident' _ -> ident == ident';_ -> False) holes)  of
                           (Nothing,Just x)   -> return $ BindHole x
                           (Just x, Nothing)  -> return $ NormalHole x
                           (Nothing, Nothing) -> return $ IdPart ident
                           _ -> fail "name used both in lambda and an regular hole"

-- | No notation by default
defaultNotation = []
noNotation = []


