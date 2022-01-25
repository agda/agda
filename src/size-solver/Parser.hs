-- Andreas, 2016-02-01 auxiliary module for stand-alone program
-- Agda.TypeChecking.SizedTypes.Main

-- | Parser combinator parser for constraints.

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}


{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Parser where

-- Andreas, 2016-02-01 because of dependency on parsec, we do not compile this
-- KEEP commented out code to follow:

-- {-
import Control.Applicative hiding (Const)

import Data.Char

import Text.Parsec (Parsec)
import qualified Text.Parsec as P
import qualified Text.Parsec.Token as T
import Text.Parsec.Language (haskellDef)

import Agda.TypeChecking.SizedTypes.Syntax
import Agda.Utils.Functor (($>))

-- | Size meta variable identifiers are upper case or start with x, y, or z.
isFlexId :: String -> Bool
isFlexId []     = False
isFlexId (x:xs) = isUpper x || x `elem` ['x','y','z']

-- * Parsing with Parsec

languageDef = haskellDef
--  { T.identLetter = T.identLetter haskellDef <|> P.oneOf "'"
--  }

tokenParser = T.makeTokenParser languageDef

-- skip whitespace
white       = T.whiteSpace tokenParser
-- lexeme      = T.lexeme tokenParser -- UNUSED
ident       = T.identifier tokenParser
symbol s    = T.symbol tokenParser s
number      = T.natural tokenParser

type Parser a = Parsec String () a

class Parse a where
  parser :: Parser a
  parse  :: String -> a
  parse s = either (error . show) id $ P.parse parser "stdin" s

instance Parse Cmp where
  parser =
      ((symbol "≤" $> Le) <|>
       (symbol "<" *> P.option Lt (symbol "=" $> Le)))

instance Parse Polarity where
  parser = (symbol "+" $> Greatest) <|> (symbol "-" $> Least)

instance Parse Flex where
  parser = FlexId <$> ident

instance Parse Rigid where
  parser = RigidId <$> ident

instance Parse flex => Parse (PolarityAssignment flex) where
  parser = PolarityAssignment <$> parser <*> parser

instance Parse SizeExpr where
  parser = white >> do
      (Infty <$ (symbol "oo" <|> symbol "∞")) <|>
       (Const . fromInteger <$> number) <|>
       (rigidOrFlexN <$> ident <*> P.option 0 (symbol "+" *> number))

instance Parse Constraint where
  parser = white >> Constraint <$> parser <*> parser <*> parser

rigidOrFlex :: String -> SizeExpr
rigidOrFlex  x   = if isFlexId x then Flex (FlexId x) 0 else Rigid (RigidId x) 0

rigidOrFlexN :: String -> Integer -> SizeExpr
rigidOrFlexN x n = (rigidOrFlex x) { offset = fromInteger $ n }

-- * Testing

simplify :: [Constraint] -> [Either Error [Constraint]]
simplify = map (simplify1 (\ c -> return [c]))

cs = simplify $ map parse
  [ "x<y+ 1"
  , "z+1 < i+4"
  , "x + 3 < oo"
  , " 1 < i+2"
  , "1 < oo"
  , " X + 2 < oo"
  , "2 < 7"
  , "oo <= 5"
  , "i < j"
  , "x < i + 2"
  , "x + 2 < i"
  , "x < i"
  ]
-- -}
