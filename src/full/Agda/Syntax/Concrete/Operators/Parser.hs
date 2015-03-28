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
import Agda.Utils.Parser.MemoisedCPS hiding (Parser, parse)
import qualified Agda.Utils.Parser.MemoisedCPS as Parser
import Agda.Utils.Monad
import Agda.Utils.Suffix
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

data MemoKey = NodeK      (Either Integer Integer)
             | PostLeftsK (Either Integer Integer)
             | TopK
             | AppK
             | NonfixK
  deriving (Eq, Generic)

instance Hashable MemoKey

data Placeholder
  = Beginning
    -- ^ @_foo@.
  | Middle
    -- ^ @foo_bar@.
  | End
    -- ^ @foo_@.
  deriving (Eq, Ord, Show)

-- | Placeholders are used to represent the underscores in a section.
data MaybePlaceholder e
  = Placeholder Placeholder
  | NoPlaceholder e
  deriving (Eq, Ord, Show)

type Parser tok a =
  MemoisedCPS.Parser MemoKey tok (MaybePlaceholder tok) a

placeholder :: Placeholder -> Parser e (MaybePlaceholder e)
placeholder p = sat $ \t ->
  case t of
    Placeholder p' | p' == p -> True
    _                        -> False

maybePlaceholder ::
  Maybe Placeholder -> Parser e e -> Parser e (MaybePlaceholder e)
maybePlaceholder mp p = case mp of
  Nothing -> p'
  Just h  -> placeholder h <|> p'
  where
  p' = NoPlaceholder <$> p

notPlaceholder :: Parser e e
notPlaceholder = do
  tok <- token
  case tok of
    Placeholder _   -> empty
    NoPlaceholder e -> return e

sat' :: (e -> Bool) -> Parser e e
sat' p = do
  tok <- notPlaceholder
  if p tok then return tok else empty

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

-- | Should sections be parsed?
data ParseSections = ParseSections | DoNotParseSections
  deriving (Eq, Show)

parse :: IsExpr e => (ParseSections, Parser e a) -> [e] -> [a]
parse (DoNotParseSections, p) es = Parser.parse p (map NoPlaceholder es)
parse (ParseSections,      p) es = Parser.parse p
                                     (concat $ map splitExpr es)
  where
  splitExpr :: IsExpr e => e -> [MaybePlaceholder e]
  splitExpr e = case exprView e of
    LocalV n -> splitName n
    _        -> noSplit
    where
    noSplit = [NoPlaceholder e]

    splitName n = case last ns of
      NoName{}  -> noSplit
      Name r ps -> splitParts r (init ns) Beginning ps
      where
      ns = qnameParts n

      -- Note that the same range is used for every name part. This is
      -- not entirely correct, but will hopefully not lead to any
      -- problems.

      -- Note also that the module qualifier, if any, is only applied
      -- to the first name part.

      splitParts _ _ _ []          = []
      splitParts _ _ _ (Hole : []) = [Placeholder End]
      splitParts r m w (Hole : ps) = Placeholder w : splitParts r m  Middle ps
      splitParts r m _ (Id s : ps) = part          : splitParts r [] Middle ps
        where
        part = NoPlaceholder $ unExprView $ LocalV $
                 foldr Qual (QName (Name r [Id s])) m

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

      app :: ([(MaybePlaceholder e, C.NamedArg () Int)] ->
              [(MaybePlaceholder e, C.NamedArg () Int)]) -> e
      app f = case bs of
        [] -> opApp
        bs -> -- Turn a section into a lambda, unless we have an
              -- operator and there is exactly one placeholder for
              -- every hole, in which case we only return the
              -- operator.
              if isOp && length bs == lastHole + 1
              then -- Note that the information in the set
                   -- "names" is thrown away here.
                   unExprView (LocalV q')
              else unExprView (LamV bs opApp)
        where
        args        = map (findExprFor (f normal) binders) [0..lastHole]
        (bs, args') = replacePlaceholders 0 args
        q'          = setRange range q
        opApp       = unExprView (OpAppV q' names args')

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
    Parser e (Range, [Either (MaybePlaceholder e, C.NamedArg () Int)
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
  worker ms (BindHole h : xs) = do
    e <- notPlaceholder
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

  set x arg = fmap (fmap (const x)) arg

  findExprFor ::
    [(MaybePlaceholder e, C.NamedArg () Int)] ->
    [(LamBinding, Int)] -> Int ->
    NamedArg (MaybePlaceholder (OpApp e))
  findExprFor normalHoles binders n =
    case [ (e, setArgColors [] m)
         | (e, m) <- normalHoles, namedArg m == n
         ] of
      [(Placeholder p,   arg)] -> set (Placeholder p) arg
      [(NoPlaceholder e, arg)] -> case [b | (b, m) <- binders, m == n] of
        [] -> set (NoPlaceholder (Ordinary e)) arg -- no variable to bind
        bs -> set (NoPlaceholder (SyntaxBindingLambda (fuseRange bs e) bs e)) arg
      _ -> __IMPOSSIBLE__


  -- Note that the bound names introduced below have the form
  -- .section-variable-n (for some natural number n). These names must
  -- not clash with any other names.
  --
  -- This hack can perhaps be avoided by translating sections to
  -- lambda expressions in the type checker instead of in the parser.
  -- Such a change could also lead to improved error messages.

  replacePlaceholders ::
    Integer ->
    [NamedArg (MaybePlaceholder (OpApp e))] ->
    ([LamBinding], [NamedArg (OpApp e)])
  replacePlaceholders n []       = ([], [])
  replacePlaceholders n (a : as) = case namedArg a of
    NoPlaceholder x -> mapSnd (set x a :) (replacePlaceholders n as)
    Placeholder p   ->
      ((b :) -*- (set (Ordinary (unExprView (LocalV (QName x)))) a :))
        (replacePlaceholders (succ n) as)
      where
      name = ".section" ++ map toSubscriptDigit (show n)
      x    = Name noRange [Id name]
      b    = DomainFree (argInfo a) (mkBoundName_ x)

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
