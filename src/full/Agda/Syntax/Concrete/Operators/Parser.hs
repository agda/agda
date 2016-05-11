{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Control.Applicative

import Data.Either
import Data.Hashable
import Data.Maybe
import qualified Data.Strict.Maybe as Strict
import Data.Set (Set)

import GHC.Generics (Generic)

import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete

import qualified Agda.Utils.Parser.MemoisedCPS as MemoisedCPS
import Agda.Utils.Parser.MemoisedCPS hiding (Parser, parse)
import qualified Agda.Utils.Parser.MemoisedCPS as Parser

#include "undefined.h"
import Agda.Utils.Impossible

data MemoKey = NodeK      (Either Integer Integer)
             | PostLeftsK (Either Integer Integer)
             | TopK
             | AppK
             | NonfixK
  deriving (Eq, Generic)

instance Hashable MemoKey

type Parser tok a =
  MemoisedCPS.Parser MemoKey tok (MaybePlaceholder tok) a

placeholder :: PositionInName -> Parser e (MaybePlaceholder e)
placeholder p = sat $ \t ->
  case t of
    Placeholder p' | p' == p -> True
    _                        -> False

maybePlaceholder ::
  Maybe PositionInName -> Parser e e -> Parser e (MaybePlaceholder e)
maybePlaceholder mp p = case mp of
  Nothing -> p'
  Just h  -> placeholder h <|> p'
  where
  p' = noPlaceholder <$> p

notPlaceholder :: Parser e e
notPlaceholder = do
  tok <- token
  case tok of
    Placeholder _     -> empty
    NoPlaceholder _ e -> return e

sat' :: (e -> Bool) -> Parser e e
sat' p = do
  tok <- notPlaceholder
  if p tok then return tok else empty

data ExprView e
    = LocalV QName
    | WildV e
    | OtherV e
    | AppV e (NamedArg e)
    | OpAppV QName (Set A.Name) [NamedArg (MaybePlaceholder (OpApp e))]
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

instance IsExpr Expr where
    exprView e = case e of
        Ident x         -> LocalV x
        App _ e1 e2     -> AppV e1 e2
        OpApp r d ns es -> OpAppV d ns es
        HiddenArg _ e   -> HiddenArgV e
        InstanceArg _ e -> InstanceArgV e
        Paren _ e       -> ParenV e
        Lam _ bs    e   -> LamV bs e
        Underscore{}    -> WildV e
        _               -> OtherV e
    unExprView e = case e of
        LocalV x       -> Ident x
        AppV e1 e2     -> App (fuseRange e1 e2) e1 e2
        OpAppV d ns es -> OpApp (fuseRange d es) d ns es
        HiddenArgV e   -> HiddenArg (getRange e) e
        InstanceArgV e -> InstanceArg (getRange e) e
        ParenV e       -> Paren (getRange e) e
        LamV bs e      -> Lam (fuseRange bs e) bs e
        WildV e        -> e
        OtherV e       -> e

instance IsExpr Pattern where
    exprView e = case e of
        IdentP x         -> LocalV x
        AppP e1 e2       -> AppV e1 e2
        OpAppP r d ns es -> OpAppV d ns ((map . fmap . fmap)
                                           (noPlaceholder . Ordinary) es)
        HiddenP _ e      -> HiddenArgV e
        InstanceP _ e    -> InstanceArgV e
        ParenP _ e       -> ParenV e
        WildP{}          -> WildV e
        _                -> OtherV e
    unExprView e = case e of
        LocalV x       -> IdentP x
        AppV e1 e2     -> AppP e1 e2
        OpAppV d ns es -> let ess :: [NamedArg Pattern]
                              ess = (map . fmap . fmap)
                                      (\x -> case x of
                                          Placeholder{}     -> __IMPOSSIBLE__
                                          NoPlaceholder _ x -> fromOrdinary __IMPOSSIBLE__ x)
                                      es
                          in OpAppP (fuseRange d ess) d ns ess
        HiddenArgV e   -> HiddenP (getRange e) e
        InstanceArgV e -> InstanceP (getRange e) e
        ParenV e       -> ParenP (getRange e) e
        LamV _ _       -> __IMPOSSIBLE__
        WildV e        -> e
        OtherV e       -> e

-- | Should sections be parsed?
data ParseSections = ParseSections | DoNotParseSections
  deriving (Eq, Show)

-- | Runs a parser. If sections should be parsed, then identifiers
-- with at least two name parts are split up into multiple tokens,
-- using 'PositionInName' to record the tokens' original positions
-- within their respective identifiers.

parse :: IsExpr e => (ParseSections, Parser e a) -> [e] -> [a]
parse (DoNotParseSections, p) es = Parser.parse p (map noPlaceholder es)
parse (ParseSections,      p) es = Parser.parse p
                                     (concat $ map splitExpr es)
  where
  splitExpr :: IsExpr e => e -> [MaybePlaceholder e]
  splitExpr e = case exprView e of
    LocalV n -> splitName n
    _        -> noSplit
    where
    noSplit = [noPlaceholder e]

    splitName n = case last ns of
      Name r ps@(_ : _ : _) -> splitParts r (init ns) Beginning ps
      _                     -> noSplit
      where
      ns = qnameParts n

      -- Note that the same range is used for every name part. This is
      -- not entirely correct, but will hopefully not lead to any
      -- problems.

      -- Note also that the module qualifier, if any, is only applied
      -- to the first name part.

      splitParts _ _ _ []          = __IMPOSSIBLE__
      splitParts _ _ _ (Hole : []) = [Placeholder End]
      splitParts r m _ (Id s : []) = [part r m End s]
      splitParts r m w (Hole : ps) = Placeholder w : splitParts r m  Middle ps
      splitParts r m w (Id s : ps) = part r m w s  : splitParts r [] Middle ps

      part r m w s =
        NoPlaceholder (Strict.Just w)
                      (unExprView $ LocalV $
                         foldr Qual (QName (Name r [Id s])) m)

---------------------------------------------------------------------------
-- * Parser combinators
---------------------------------------------------------------------------

----------------------------
-- Specific combinators

-- | Parse a specific identifier as a NamePart
partP :: IsExpr e => [Name] -> RawName -> Parser e Range
partP ms s = do
    tok <- notPlaceholder
    case isLocal tok of
      Just p  -> return p
      Nothing -> empty
    where
        str = show (foldr Qual (QName (Name noRange [Id s])) ms)
        isLocal e = case exprView e of
            LocalV y | str == show y -> Just (getRange y)
            _                        -> Nothing

-- | Parses a split-up, unqualified name consisting of at least two
-- name parts.
--
-- The parser does not check that underscores and other name parts
-- alternate. The range of the resulting name is the range of the
-- first name part that is not an underscore.

atLeastTwoParts :: IsExpr e => Parser e Name
atLeastTwoParts = do
  (r, ps) <- parts Beginning
  case r of
    Nothing -> __IMPOSSIBLE__
    Just r  -> return (Name r ps)
  where
  parts pos = do
    tok          <- token
    (pos', r, p) <- case tok of
      Placeholder pos'                   -> return (pos', Nothing, Hole)
      NoPlaceholder (Strict.Just pos') e -> case exprView e of
        LocalV (QName (Name r [Id s])) -> return (pos', Just r, Id s)
        _                              -> empty
      _ -> empty
    if pos == Middle && pos' == End then
      return (r, [p])
     else if pos' == pos then do
      (r', ps) <- parts Middle
      return (maybe r' Just r, p : ps)
     else
      empty

-- | Either a wildcard (@_@), or an unqualified name (possibly
-- containing multiple name parts).

wildOrUnqualifiedName :: IsExpr e => Parser e (Maybe Name)
wildOrUnqualifiedName =
  (Nothing <$ partP [] "_")
    <|>
  (do e <- notPlaceholder
      case exprView e of
        LocalV (QName n) -> return (Just n)
        WildV _          -> return Nothing
        _                -> empty)
    <|>
  Just <$> atLeastTwoParts

-- | Used to define the return type of 'opP'.

type family OperatorType (k :: NotationKind) (e :: *) :: *
type instance OperatorType 'InfixNotation   e = MaybePlaceholder e -> MaybePlaceholder e -> e
type instance OperatorType 'PrefixNotation  e = MaybePlaceholder e -> e
type instance OperatorType 'PostfixNotation e = MaybePlaceholder e -> e
type instance OperatorType 'NonfixNotation  e = e

-- | A singleton type for 'NotationKind' (except for the constructor
-- 'NoNotation').

data NK (k :: NotationKind) :: * where
  In   :: NK 'InfixNotation
  Pre  :: NK 'PrefixNotation
  Post :: NK 'PostfixNotation
  Non  :: NK 'NonfixNotation

-- | Parse the \"operator part\" of the given notation.
--
-- Normal holes (but not binders) at the beginning and end are
-- ignored.
--
-- If the notation does not contain any binders, then a section
-- notation is allowed.
opP :: forall e k. IsExpr e
    => ParseSections
    -> Parser e e -> NewNotation -> NK k -> Parser e (OperatorType k e)
opP parseSections p (NewNotation q names _ syn isOp) kind = do

  (range, hs) <- worker (init $ qnameParts q) withoutExternalHoles

  let (normal, binders) = partitionEithers hs
      lastHole          = maximum $ mapMaybe holeTarget syn

      app :: ([(MaybePlaceholder e, NamedArg Int)] ->
              [(MaybePlaceholder e, NamedArg Int)]) -> e
      app f =
        -- If we have an operator and there is exactly one
        -- placeholder for every hole, then we only return
        -- the operator.
        if isOp && noPlaceholders args == lastHole + 1 then
          -- Note that the information in the set "names" is thrown
          -- away here.
          unExprView (LocalV q')
        else
          unExprView (OpAppV q' names args)
        where
        args = map (findExprFor (f normal) binders) [0..lastHole]
        q'   = setRange range q

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
    Parser e (Range, [Either (MaybePlaceholder e, NamedArg Int)
                             (LamBinding, Int)])
  worker ms []              = return (noRange, [])
  worker ms (IdPart x : xs) = do
    r1       <- partP ms x
    (r2, es) <- worker [] xs
                -- Only the first
                -- part is qualified.
    return (fuseRanges r1 r2, es)
  worker ms (NormalHole h : xs) = do
    e <- maybePlaceholder
           (if isOp && parseSections == ParseSections
            then Just Middle else Nothing)
           p
    (r, es) <- worker ms xs
    return (r, Left (e, h) : es)
  worker ms (WildHole h : xs) = do
    (r, es) <- worker ms xs
    return (r, Right (mkBinding h $ Name noRange [Hole]) : es)
  worker ms (BindHole h : xs) = do
    e <- wildOrUnqualifiedName
    case e of
      Just name -> ret name
      Nothing   -> ret (Name noRange [Hole])
    where
    ret x = do
      (r, es) <- worker ms xs
      return (r, Right (mkBinding h x) : es)
      -- Andreas, 2011-04-07 put just 'Relevant' here, is this correct?

  mkBinding h x = (DomainFree defaultArgInfo $ mkBoundName_ x, h)

  set x arg = fmap (fmap (const x)) arg

  findExprFor ::
    [(MaybePlaceholder e, NamedArg Int)] ->
    [(LamBinding, Int)] -> Int ->
    NamedArg (MaybePlaceholder (OpApp e))
  findExprFor normalHoles binders n =
    case [ h | h@(_, m) <- normalHoles, namedArg m == n ] of
      [(Placeholder p,     arg)] -> set (Placeholder p) arg
      [(NoPlaceholder _ e, arg)] -> case [b | (b, m) <- binders, m == n] of
        [] -> set (noPlaceholder (Ordinary e)) arg -- no variable to bind
        bs -> set (noPlaceholder (SyntaxBindingLambda (fuseRange bs e) bs e)) arg
      _ -> __IMPOSSIBLE__

  noPlaceholders :: [NamedArg (MaybePlaceholder (OpApp e))] -> Int
  noPlaceholders = sum . map (isPlaceholder . namedArg)
    where
    isPlaceholder NoPlaceholder{} = 0
    isPlaceholder Placeholder{}   = 1

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
            InstanceArgV e <- exprView <$> sat' (isInstance . exprView)
            return $ makeInstance $ defaultArg e

        hidden = do
            HiddenArgV e <- exprView <$> sat' (isHidden . exprView)
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
    e <- notPlaceholder
    case exprView e of
        LocalV x | not (p x) -> empty
        _                    -> return e
