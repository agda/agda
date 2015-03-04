{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Control.Applicative
import Control.Exception (throw)

import Data.Either
import Data.Hashable
import Data.Maybe
import Data.Set (Set)

import GHC.Generics (Generic)

import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Common as C
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete
import Agda.TypeChecking.Monad.Base (TCErr(Exception))
import qualified Agda.Utils.Parser.MemoisedCPS as MemoisedCPS
import Agda.Utils.Parser.MemoisedCPS hiding (Parser)
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

data MemoKey = NodeK      (Either Integer Integer)
             | PostLeftsK (Either Integer Integer)
             | HigherK Integer
             | TopK
             | AppK
             | NonfixK
  deriving (Eq, Generic)

instance Hashable MemoKey

type Parser tok a = MemoisedCPS.Parser MemoKey tok tok a

data ExprView e
    = LocalV QName
    | WildV e
    | OtherV e
    | AppV e (NamedArg e)
    | OpAppV QName (Set A.Name) [NamedArg (OpApp e)]
      -- ^ The 'QName' is possibly ambiguous, but it must correspond
      -- to one of the names in the set.
    | HiddenArgV (Named_ e)
    | InstanceArgV (Named_ e)
    | LamV [LamBinding] e
    | ParenV e
--    deriving (Show)

class HasRange e => IsExpr e where
    exprView   :: e -> ExprView e
    unExprView :: ExprView e -> e

instance IsExpr e => HasRange (ExprView e) where
  getRange = getRange . unExprView

---------------------------------------------------------------------------
-- * Parser combinators
---------------------------------------------------------------------------

----------------------------
-- Specific combinators

-- | Parse a specific identifier as a NamePart
partP :: IsExpr e => [Name] -> RawName -> Parser e Range
partP ms s = do
    tok <- token
    case isLocal tok of
      Just p  -> return p
      Nothing -> empty
    where
        str = show (foldr Qual (QName (Name noRange [Id s])) ms)
        isLocal e = case exprView e of
            LocalV y | str == show y -> Just (getRange y)
            _                        -> Nothing

-- | Used to define the return type of 'opP'.

type family OperatorType (k :: NotationKind) (e :: *) :: *
type instance OperatorType InfixNotation   e = e -> e -> e
type instance OperatorType PrefixNotation  e = e -> e
type instance OperatorType PostfixNotation e = e -> e
type instance OperatorType NonfixNotation  e = e

-- | A singleton type for 'NotationKind' (except for the constructor
-- 'NoNotation').

data NK (k :: NotationKind) :: * where
  In   :: NK InfixNotation
  Pre  :: NK PrefixNotation
  Post :: NK PostfixNotation
  Non  :: NK NonfixNotation

-- | Parse the \"operator part\" of the given syntax. Normal holes
-- (but not binders) at the beginning and end are ignored.
opP :: forall e k. IsExpr e =>
       NK k -> Parser e e -> NewNotation -> Parser e (OperatorType k e)
opP kind p (NewNotation q names _ syn) = do

  (range, hs) <- worker (init $ qnameParts q) withoutExternalHoles

  let (normal, binders) = partitionEithers hs
      lastHole          = maximum $ mapMaybe holeTarget syn

      app :: ([(e, C.NamedArg () Int)] -> [(e, C.NamedArg () Int)]) -> e
      app f = unExprView $
              OpAppV (setRange range q) names $
              map (findExprFor (f normal) binders) [0..lastHole]

  return $ case kind of
    In   -> \x y -> app (\es -> (x, leadingHole) : es ++ [(y, trailingHole)])
    Pre  -> \  y -> app (\es ->                    es ++ [(y, trailingHole)])
    Post -> \x   -> app (\es -> (x, leadingHole) : es)
    Non  ->         app (\es ->                    es)

  where

  (leadingHoles,  syn1) = span isNormalHole syn
  (trailingHoles, syn2) = span isNormalHole (reverse syn1)
  withoutExternalHoles  = reverse syn2

  leadingHole = case leadingHoles of
    [NormalHole h] -> h
    _              -> __IMPOSSIBLE__

  trailingHole = case trailingHoles of
    [NormalHole h] -> h
    _              -> __IMPOSSIBLE__

  worker ::
    [Name] -> Notation ->
    Parser e (Range, [Either (e, C.NamedArg () Int) (LamBinding, Int)])
  worker ms []                  = return (noRange, [])
  worker ms (IdPart x     : xs) = do r1       <- partP ms x
                                     (r2, es) <- worker [] xs
                                                 -- Only the first
                                                 -- part is qualified.
                                     return (fuseRanges r1 r2, es)
  worker ms (NormalHole h : xs) = do e       <- p
                                     (r, es) <- worker ms xs
                                     return (r, Left (e, h) : es)
  worker ms (BindHole h   : xs) = do
    e <- token
    case exprView e of
      LocalV (QName name) -> ret name
      WildV e             -> ret (Name noRange [Hole])
      _                   -> empty
        -- Old error message: "Expected variable name in binding
        -- position".
    where
    ret x = do
      (r, es) <- worker ms xs
      return (r, Right (DomainFree defaultArgInfo $ mkBoundName_ x, h) : es)
      -- Andreas, 2011-04-07 put just 'Relevant' here, is this correct?

  findExprFor ::
    [(e, C.NamedArg () Int)] -> [(LamBinding, Int)] -> Int ->
    NamedArg (OpApp e)
  findExprFor normalHoles binders n =
    case [ setArgColors [] $ fmap (e <$) m
         | (e, m) <- normalHoles, namedArg m == n
         ] of
      [x] -> case [e | (e, m) <- binders, m == n] of
               [] -> (fmap . fmap) Ordinary x -- no variable to bind
               bs ->
                 (fmap . fmap) (SyntaxBindingLambda (fuseRange bs x) bs) x
      _   -> __IMPOSSIBLE__

argsP :: IsExpr e => Parser e e -> Parser e [NamedArg e]
argsP p = many (nothidden <|> hidden <|> instanceH)
    where
        isHidden (HiddenArgV _) = True
        isHidden _              = False

        isInstance (InstanceArgV _) = True
        isInstance _                = False

        nothidden = defaultArg . unnamed <$> do
            e <- p
            case exprView e of
                HiddenArgV   _ -> empty
                InstanceArgV _ -> empty
                _              -> return e

        instanceH = do
            InstanceArgV e <- exprView <$> sat (isInstance . exprView)
            return $ makeInstance $ defaultArg e

        hidden = do
            HiddenArgV e <- exprView <$> sat (isHidden . exprView)
            return $ hide $ defaultArg e

appP :: IsExpr e => Parser e e -> Parser e [NamedArg e] -> Parser e e
appP p pa = do
    h  <- p
    es <- pa
    return $ foldl app h es
    where
        app e = unExprView . AppV e

atomP :: IsExpr e => (QName -> Bool) -> Parser e e
atomP p = do
    e <- token
    case exprView e of
        LocalV x | not (p x) -> empty
        _                    -> return e
