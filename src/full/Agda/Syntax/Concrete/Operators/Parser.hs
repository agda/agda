{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Control.Applicative
import Control.Exception (throw)

import Data.Hashable
import Data.Maybe

import GHC.Generics (Generic)

import Agda.Syntax.Position
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

data MemoKey = Node Integer | PostLefts Integer
  deriving (Eq, Generic)

instance Hashable MemoKey

type Parser tok a = MemoisedCPS.Parser MemoKey tok tok a

data ExprView e
    = LocalV QName
    | WildV e
    | OtherV e
    | AppV e (NamedArg e)
    | OpAppV QName [NamedArg (OpApp e)]
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

binop ::
  IsExpr e =>
  Parser e (NewNotation,Range,[e]) -> Parser e (e -> e -> e)
binop middleP = do
  (nsyn,r,es) <- middleP
  return $ \x y -> rebuild nsyn r (x : es ++ [y])

preop, postop ::
  IsExpr e =>
  Parser e (NewNotation,Range,[e]) -> Parser e (e -> e)
preop middleP = do
  (nsyn,r,es) <- middleP
  return $ \x -> rebuild nsyn r (es ++ [x])

postop middleP = do
  (nsyn,r,es) <- middleP
  return $ \x -> rebuild nsyn r (x : es)


-- | Parse the "operator part" of the given syntax.
-- holes at beginning and end are IGNORED.

-- Note: it would be better to take the decision of "postprocessing" at the same
-- place as where the holes are discarded, however that would require a dependently
-- typed function (or duplicated code)
opP :: IsExpr e =>
       Parser e e -> NewNotation -> Parser e (NewNotation,Range,[e])
opP p nsyn@(NewNotation q _ syn) = do
  (range,es) <- worker (init $ qnameParts q) $ removeExternalHoles syn
  return (nsyn,range,es)
 where worker ms [IdPart x] = do r <- partP ms x; return (r,[])
       worker ms (IdPart x : _ : xs) = do
            r1        <- partP ms x
            e         <- p
            (r2 , es) <- worker [] xs -- only the first part is qualified
            return (fuseRanges r1 r2, e : es)
       worker _ x = __IMPOSSIBLE__ -- holes and non-holes must be alternated.

       removeExternalHoles = reverse . removeLeadingHoles . reverse . removeLeadingHoles
           where removeLeadingHoles = dropWhile isAHole

-- | Given a name with a syntax spec, and a list of parsed expressions
-- fitting it, rebuild the expression.
rebuild :: forall e. IsExpr e => NewNotation -> Range -> [e] -> e
rebuild (NewNotation name _ syn) r es = unExprView $ OpAppV (setRange r name) exprs
  where
    exprs = map findExprFor [0..lastHole]
    filledHoles = zip es (filter isAHole syn)
    lastHole = maximum $ mapMaybe holeTarget syn
    findExprFor :: Int -> NamedArg (OpApp e)
    findExprFor n =
      case [setArgColors [] $ fmap (e <$) m | (e, NormalHole m) <- filledHoles, namedArg m == n] of
        [x] -> case [e | (e, BindHole m) <- filledHoles, m == n] of
                 [] -> (fmap . fmap) Ordinary x -- no variable to bind
                 vars ->
                  let bs = map (rebuildBinding . exprView) vars in
                  (fmap . fmap) (SyntaxBindingLambda (fuseRange bs x) bs) x
        _  -> __IMPOSSIBLE__

rebuildBinding :: IsExpr e => ExprView e -> LamBinding
  -- Andreas, 2011-04-07 put just 'Relevant' here, is this correct?
rebuildBinding (LocalV (QName name)) = DomainFree defaultArgInfo $ mkBoundName_ name
rebuildBinding (WildV e) =
  DomainFree defaultArgInfo $ mkBoundName_ $ Name noRange [Hole]
rebuildBinding e = throw $ Exception (getRange e) "Expected variable name in binding position"

-- | Parse a \"nonfix\" operator application, given a parser parsing
-- the operator part, the name of the operator, and a parser of
-- subexpressions.
nonfixP ::
  IsExpr e =>
  Parser e (NewNotation,Range,[e]) -> Parser e e -> Parser e e
nonfixP op p = do
  (nsyn,r,es) <- op
  return $ rebuild nsyn r es
 <|> p

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
