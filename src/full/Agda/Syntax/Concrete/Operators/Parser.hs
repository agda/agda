{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds    #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Control.Applicative ( Alternative((<|>), many) )

import Data.Either
import Data.Kind ( Type )
import Data.Maybe
import qualified Data.Strict.Maybe as Strict
import Data.Set (Set)

import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Operators.Parser.Monad hiding (parse)
import qualified Agda.Syntax.Concrete.Operators.Parser.Monad as P

import Agda.Utils.Pretty
import Agda.Utils.List ( spanEnd )

import Agda.Utils.Impossible

placeholder :: PositionInName -> Parser e (MaybePlaceholder e)
placeholder p =
  doc (text ("_" ++ show p)) $
  sat $ \t ->
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

satNoPlaceholder :: (e -> Maybe a) -> Parser e a
satNoPlaceholder p = sat' $ \tok ->
  case tok of
    NoPlaceholder _ e -> p e
    Placeholder _     -> Nothing

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
  exprView    :: e -> ExprView e
  unExprView  :: ExprView e -> e
  patternView :: e -> Maybe Pattern

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

    patternView = isPattern

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

    patternView = pure

-- | Should sections be parsed?
data ParseSections = ParseSections | DoNotParseSections
  deriving (Eq, Show)

-- | Runs a parser. If sections should be parsed, then identifiers
-- with at least two name parts are split up into multiple tokens,
-- using 'PositionInName' to record the tokens' original positions
-- within their respective identifiers.

parse :: IsExpr e => (ParseSections, Parser e a) -> [e] -> [a]
parse (DoNotParseSections, p) es = P.parse p (map noPlaceholder es)
parse (ParseSections,      p) es = P.parse p (concat $ map splitExpr es)
  where
  splitExpr :: IsExpr e => e -> [MaybePlaceholder e]
  splitExpr e = case exprView e of
    LocalV n -> splitName n
    _        -> noSplit
    where
    noSplit = [noPlaceholder e]

    splitName n = case last ns of
      Name r nis ps@(_ : _ : _) -> splitParts r nis (init ns) Beginning ps
      _                         -> noSplit
      where
      ns = qnameParts n

      -- Note that the same range is used for every name part. This is
      -- not entirely correct, but will hopefully not lead to any
      -- problems.

      -- Note also that the module qualifier, if any, is only applied
      -- to the first name part.

      splitParts _ _   _ _ []          = __IMPOSSIBLE__
      splitParts _ _   _ _ (Hole : []) = [Placeholder End]
      splitParts r nis m _ (Id s : []) = [part r nis m End s]
      splitParts r nis m w (Hole : ps) = Placeholder w : splitParts r nis m  Middle ps
      splitParts r nis m w (Id s : ps) = part r nis m w s : splitParts r nis [] Middle ps

      part r nis m w s =
        NoPlaceholder (Strict.Just w)
                      (unExprView $ LocalV $
                         foldr Qual (QName (Name r nis [Id s])) m)

---------------------------------------------------------------------------
-- * Parser combinators
---------------------------------------------------------------------------

----------------------------
-- Specific combinators

-- | Parse a specific identifier as a NamePart
partP :: IsExpr e => [Name] -> RawName -> Parser e Range
partP ms s =
  doc (text (show str)) $
  satNoPlaceholder isLocal
  where
  str = prettyShow $ foldr Qual (QName $ Name noRange InScope [Id s]) ms
  isLocal e = case exprView e of
      LocalV y | str == prettyShow y -> Just $ getRange y
      _ -> Nothing

-- | Parses a split-up, unqualified name consisting of at least two
-- name parts.
--
-- The parser does not check that underscores and other name parts
-- alternate. The range of the resulting name is the range of the
-- first name part that is not an underscore.

atLeastTwoParts :: IsExpr e => Parser e Name
atLeastTwoParts =
  (\p1 ps p2 ->
      let all = p1 : ps ++ [p2] in
      case mapMaybe fst all of
        (r,nis) : _ -> Name r nis (map snd all)
        []          -> __IMPOSSIBLE__)
  <$> part Beginning
  <*> many (part Middle)
  <*> part End
  where
  part pos = sat' $ \tok -> case tok of
    Placeholder pos'                   | pos == pos' -> Just ( Nothing
                                                             , Hole
                                                             )
    NoPlaceholder (Strict.Just pos') e | pos == pos' ->
      case exprView e of
        LocalV (QName (Name r nis [Id s])) -> Just (Just (r,nis), Id s)
        _                                  -> Nothing
    _ -> Nothing

-- | Parses a potentially pattern-matching binder

patternBinder :: IsExpr e => Parser e Binder
patternBinder = inOnePart <|> mkBinder_ <$> atLeastTwoParts
  where inOnePart = satNoPlaceholder $ \ e -> isBinderP =<< patternView e

-- | Used to define the return type of 'opP'.

type family OperatorType (k :: NotationKind) (e :: Type) :: Type
type instance OperatorType 'InfixNotation   e = MaybePlaceholder e -> MaybePlaceholder e -> e
type instance OperatorType 'PrefixNotation  e = MaybePlaceholder e -> e
type instance OperatorType 'PostfixNotation e = MaybePlaceholder e -> e
type instance OperatorType 'NonfixNotation  e = e

-- | A singleton type for 'NotationKind' (except for the constructor
-- 'NoNotation').

data NK (k :: NotationKind) :: Type where
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
opP parseSections p (NewNotation q names _ syn isOp) kind =
  flip fmap (worker (init $ qnameParts q)
                    withoutExternalHoles) $ \(range, hs) ->

  let (normal, binders) = partitionEithers hs
      lastHole          = maximum $ mapMaybe holeTarget syn

      app :: ([(MaybePlaceholder e, NamedArg (Ranged Int))] ->
              [(MaybePlaceholder e, NamedArg (Ranged Int))]) -> e
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
  in

  case kind of
    In   -> \x y -> app (\es -> (x, leadingHole) : es ++ [(y, trailingHole)])
    Pre  -> \  y -> app (\es ->                    es ++ [(y, trailingHole)])
    Post -> \x   -> app (\es -> (x, leadingHole) : es)
    Non  ->         app (\es ->                    es)

  where

  (leadingHoles, syn1)                  = span    isNormalHole syn
  (withoutExternalHoles, trailingHoles) = spanEnd isNormalHole syn1

  leadingHole = case leadingHoles of
    [NormalHole _ h] -> h
    _                -> __IMPOSSIBLE__

  trailingHole = case trailingHoles of
    [NormalHole _ h] -> h
    _                -> __IMPOSSIBLE__

  worker ::
    [Name] -> Notation ->
    Parser e (Range, [Either (MaybePlaceholder e, NamedArg (Ranged Int))
                             (LamBinding, Ranged Int)])
  worker ms []              = pure (noRange, [])
  worker ms (IdPart x : xs) =
    (\r1 (r2, es) -> (fuseRanges r1 r2, es))
      <$> partP ms (rangedThing x)
      <*> worker [] xs
          -- Only the first part is qualified.
  worker ms (NormalHole _ h : xs) =
    (\e (r, es) -> (r, Left (e, h) : es))
      <$> maybePlaceholder
            (if isOp && parseSections == ParseSections
             then Just Middle else Nothing)
            p
      <*> worker ms xs
  worker ms (WildHole h : xs) =
    (\(r, es) -> let anon = mkBinder_ (Name noRange InScope [Hole])
                 in (r, Right (mkBinding h anon) : es))
      <$> worker ms xs
  worker ms (BindHole _ h : xs) = do
    (\ b (r, es) -> (r, Right (mkBinding h b) : es))
           -- Andreas, 2011-04-07 put just 'Relevant' here, is this
           -- correct?
      <$> patternBinder
      <*> worker ms xs

  mkBinding h b = (DomainFree $ defaultNamedArg b, h)

  set x arg = fmap (fmap (const x)) arg

  findExprFor ::
    [(MaybePlaceholder e, NamedArg (Ranged Int))] ->
    [(LamBinding, Ranged Int)] -> Int ->
    NamedArg (MaybePlaceholder (OpApp e))
  findExprFor normalHoles binders n =
    case [ h | h@(_, m) <- normalHoles, rangedThing (namedArg m) == n ] of
      [(Placeholder p,     arg)] -> set (Placeholder p) arg
      [(NoPlaceholder _ e, arg)] -> case [b | (b, m) <- binders, rangedThing m == n] of
        [] -> set (noPlaceholder (Ordinary e)) arg -- no variable to bind
        bs -> set (noPlaceholder (SyntaxBindingLambda (fuseRange bs e) bs e)) arg
      _ -> __IMPOSSIBLE__

  noPlaceholders :: [NamedArg (MaybePlaceholder (OpApp e))] -> Int
  noPlaceholders = sum . map (isPlaceholder . namedArg)
    where
    isPlaceholder NoPlaceholder{} = 0
    isPlaceholder Placeholder{}   = 1

argsP :: IsExpr e => Parser e e -> Parser e [NamedArg e]
argsP p = many (mkArg <$> p)
  where
  mkArg e = case exprView e of
    HiddenArgV   e -> hide (defaultArg e)
    InstanceArgV e -> makeInstance (defaultArg e)
    _              -> defaultArg (unnamed e)

appP :: IsExpr e => Parser e e -> Parser e [NamedArg e] -> Parser e e
appP p pa = foldl app <$> p <*> pa
    where
        app e = unExprView . AppV e

atomP :: IsExpr e => (QName -> Bool) -> Parser e e
atomP p =
  doc "<atom>" $
  satNoPlaceholder $ \e ->
  case exprView e of
    LocalV x | not (p x) -> Nothing
    _                    -> Just e
