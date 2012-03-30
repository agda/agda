------------------------------------------------------------------------
-- | Tokens
--
-- The token data type is somewhat complicated in order to simplify
-- parsing of sections; see ExpressionParser.
------------------------------------------------------------------------

{-# LANGUAGE GADTs, FlexibleContexts, NoMonomorphismRestriction #-}

module Token
  ( Token(..)
  , Pos(..)
  , tokensInvariant
  , nameToTokens
  , parseName
  , pretty
  , lex
  , tests
  ) where

import qualified Name
import Name hiding (pretty, tests)
import Parser
import qualified MemoisedCPS
import IndexedOrd

import Test.QuickCheck
import Control.Monad
import Control.Applicative
import Data.Char
import Data.List
import Data.Maybe
import Data.Foldable (asum)
import Prelude hiding (lex)

------------------------------------------------------------------------
-- Type

-- | Tokens. Placeholders are used to indicate sections. Wildcards
-- indicate things the type checker should fill in automatically
-- (hopefully).

data Token = QualifiedName [String] String
             -- ^ A name part, possibly with a (perhaps incomplete)
             -- module prefix.
           | Placeholder Pos
           | Wildcard | LParen | RParen
  deriving (Eq, Ord, Show)

-- | Placeholder positions.

data Pos = Beg  -- ^ At the beginning of an operator.
         | Mid  -- ^ In the middle of an operator.
         | End  -- ^ At the end of an operator.
  deriving (Eq, Ord, Show)

-- | Characters which may not occur in name parts.

specialChar :: Char -> Bool
specialChar c = c `elem` "()_." || isSpace c

-- | Token invariant.

tokenInvariant :: Token -> Bool
tokenInvariant (QualifiedName ms n) = all p (n : ms)
  where p n = not (null n) && not (any specialChar n)
tokenInvariant (Placeholder _)      = True
tokenInvariant Wildcard             = True
tokenInvariant LParen               = True
tokenInvariant RParen               = True

-- | Invariant for a list of tokens. The placeholders have to be
-- correctly annotated, and all qualified names corresponding to a
-- name have to use the same module name.

tokensInvariant :: [Token] -> Bool
tokensInvariant ts =
  all tokenInvariant ts && inv1 ts && inv2 Nothing ts
  where
  inv1 [] = True
  inv1 (Placeholder Beg : rest@(QualifiedName _ _ : _)) = inv1 rest
  inv1 (QualifiedName _ _ : Placeholder Mid
                          : rest@(QualifiedName _ _ : _)) = inv1 rest
  inv1 (QualifiedName _ _ : Placeholder End : rest) = inv1 rest
  inv1 (QualifiedName _ _ : rest)                   = inv1 rest
  inv1 (t : rest) | t `elem` [Wildcard, LParen, RParen] = inv1 rest
  inv1 _ = False

  inv2 m (QualifiedName ms _ : Placeholder Mid : rest) =
    check m ms && inv2 (Just ms) rest
  inv2 m (QualifiedName ms _ : rest) =
    check m ms && inv2 Nothing rest
  inv2 _ (_ : rest) = inv2 Nothing rest
  inv2 _ [] = True

  check Nothing    _   = True
  check (Just ms1) ms2 = ms1 == ms2

------------------------------------------------------------------------
-- Conversion from and to names

-- | Converts names to lists of tokens.

nameToTokens :: Name -> [Token]
nameToTokens n =
  fixUp $
  intersperse (Placeholder Mid) $
  map (QualifiedName (moduleName n)) (nameParts n)
  where
  fixUp = case fixity n of
    Nothing      -> id
    Just Prefix  -> (++ [Placeholder End])
    Just Postfix -> ([Placeholder Beg] ++)
    Just Infix   -> ([Placeholder Beg] ++) . (++ [Placeholder End])

prop_nameToTokens n =
  tokensInvariant (nameToTokens n)

prop_nameToTokens_pretty n =
  pretty (nameToTokens n) == Name.pretty n

-- | Tries to convert lists of tokens to names.

parseName :: Parser p Token => p Name
parseName = do
   beg <- optional (sym $ Placeholder Beg)
   mid <- qName `sepBy` sym (Placeholder Mid)
   end <- optional (sym $ Placeholder End)
   return $ Name (fst $ head mid) (fix beg end) (map snd mid)
  where
  qName = symbol >>= \s -> case s of
    QualifiedName ms n -> return (ms, n)
    _                  -> empty

  fix Nothing  Nothing  = Nothing
  fix (Just _) Nothing  = Just Postfix
  fix Nothing  (Just _) = Just Prefix
  fix (Just _) (Just _) = Just Infix

prop_parseName_nameToTokens n =
  MemoisedCPS.parse undefined parseName (nameToTokens n) == [n]

------------------------------------------------------------------------
-- Pretty-printing

-- | Pretty-prints a token sequence.

pretty :: [Token] -> String
pretty = concat . addSpaces . pretty'
  where
  addSpaces ((_, s1, w1) : s2@(w2, _, _) : ss)
    | w1 && w2  = s1 : " " : addSpaces (s2 : ss)
    | otherwise = s1 : addSpaces (s2 : ss)
  addSpaces [(_, s, _)] = [s]
  addSpaces []          = []

  -- The boolean indicates when surrounding white space might be
  -- necessary.

  pretty' [] = []
  pretty' (Placeholder Beg : QualifiedName ms n : rest) =
    nameToTokens True ms n "_" : pretty' rest
  pretty' (Placeholder Mid : QualifiedName ms n : rest) =
    nameToTokens False [] n "_" : pretty' rest
  pretty' (t : rest) = (: pretty' rest) $ case t of
    Placeholder End    -> (False, "_", True)
    QualifiedName ms n -> nameToTokens True ms n ""
    Wildcard           -> (True, "_", True)
    LParen             -> (False, "(", False)
    RParen             -> (False, ")", False)

  nameToTokens space ms n extra =
    (space, intercalate "." (ms ++ [extra ++ n]), True)

------------------------------------------------------------------------
-- Lexing

-- | Token grammar non-terminals.

data LexerNT a where
  NamePartNT      :: LexerNT String
  QualifiedNameNT :: LexerNT [Token]
  TokensNT        :: LexerNT [Token]

-- | Grammar for tokens.

grammar :: NTParser p LexerNT Char => LexerNT r -> p r
grammar NamePartNT      = some (sat (not . specialChar))
grammar QualifiedNameNT = do
  mod     <- many (nonTerm NamePartNT <* sym '.')
  initial <- optional (Placeholder Beg <$ sym '_')
  ps      <- nonTerm NamePartNT `sepBy` sym '_'
  final   <- optional (Placeholder End <$ sym '_')
  return $ maybeToList initial ++
           intersperse (Placeholder Mid) (map (QualifiedName mod) ps) ++
           maybeToList final
grammar TokensNT = concat <$>
                     (many white *>
                      tokensAndParens `sepBy` some white <*
                      many white)
  where
  tokensAndParens =
    some parens
      <|>
    (\ts1 ts2 ts3 -> ts1 ++ concat ts2 ++ ts3) <$>
      many parens <*>
      other `sepByKeep` some parens <*>
      many parens

  p `sepByKeep` sep = (:) <$> p <*> many ((++) <$> sep <*> p)

  white  = sat isSpace
  parens = asum [ LParen <$ sym '('
                , RParen <$ sym ')'
                ]
  other  = asum [ nonTerm QualifiedNameNT
                , [Wildcard] <$ sym '_'
                ]

-- | Lexer.

lexer :: String -> [[Token]]
lexer s = MemoisedCPS.parse grammar (nonTerm TokensNT) s

prop_lexer =
  forAll (listOf $ elements "ab_.() ") $ \s ->
  let result = lexer s in
    classify (not $ null result) "syntactically correct" $
      length result <= 1 &&
      all tokensInvariant result

-- | Lexer.

-- The lexer is unambiguous, so the following type is more precise.

lex :: String -> Maybe [Token]
lex = listToMaybe . lexer

prop_lex_pretty = forAll tokens $ \ts ->
  lex (pretty ts) == case ts of
    [] -> Nothing
    _  -> Just ts

------------------------------------------------------------------------
-- Test data generators

instance Arbitrary Token where
  arbitrary = oneof [ liftM2 QualifiedName (listOf name) name
                    , liftM  Placeholder arbitrary
                    , return Wildcard
                    , return LParen
                    , return RParen
                    ]
    where name = string 1 3

-- | Generates a well-formed sequence of tokens.

tokens :: Gen [Token]
tokens = fmap concat $
  listOf (oneof [ fmap nameToTokens arbitrary
                , listOf $ elements [Wildcard, LParen, RParen]
                ])

instance Arbitrary Pos where
  arbitrary = elements [Beg, Mid, End]

------------------------------------------------------------------------
-- Tests.

-- | All tests.

tests = do
  quickCheck tokenInvariant
  quickCheck (forAll tokens tokensInvariant)
  quickCheck prop_nameToTokens
  quickCheck prop_nameToTokens_pretty
  quickCheck prop_parseName_nameToTokens
  quickCheck prop_lexer
  quickCheck prop_lex_pretty

------------------------------------------------------------------------
-- Boring instances

instance IndexedEq LexerNT where
  iEq NamePartNT      NamePartNT      = Just Refl
  iEq QualifiedNameNT QualifiedNameNT = Just Refl
  iEq TokensNT        TokensNT        = Just Refl
  iEq _               _               = Nothing

instance IndexedOrd LexerNT where
  iCompare NamePartNT      NamePartNT      = EQ
  iCompare NamePartNT      _               = LT
  iCompare QualifiedNameNT NamePartNT      = GT
  iCompare QualifiedNameNT QualifiedNameNT = EQ
  iCompare QualifiedNameNT _               = LT
  iCompare TokensNT        NamePartNT      = GT
  iCompare TokensNT        QualifiedNameNT = GT
  iCompare TokensNT        TokensNT        = EQ
