{-# LANGUAGE CPP, ScopedTypeVariables #-}

{-| The parser doesn't know about operators and parses everything as normal
    function application. This module contains the functions that parses the
    operators properly. For a stand-alone implementation of this see
    @src\/prototyping\/mixfix@.

    It also contains the function that puts parenthesis back given the
    precedence of the context.
-}
module Agda.Syntax.Concrete.Operators
    ( parseApplication
    , parseLHS
    , paren
    , mparen
    ) where

import Control.Applicative
import Control.Monad.Trans
import Data.Typeable
import Data.Traversable (traverse)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Data.Function

import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Operators.Parser
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (typeError, TypeError(..))
import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Statistics

import Agda.Utils.ReadP
import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.List

import Debug.Trace

#include "../../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Building the parser
---------------------------------------------------------------------------

partsInScope :: ScopeM (Set Name)
partsInScope = do
    (names, ops) <- localNames
    let xs = concatMap parts names ++ concatMap notationNames ops
    return $ Set.fromList xs
    where
        parts (NoName _ _)   = []
        parts x@(Name _ [_]) = [x]
        parts x@(Name _ xs)  = x : [ Name noRange [i] | i@(Id {}) <- xs ]

-- | Compute all unqualified defined names in scope and their fixities.
getDefinedNames :: [KindOfName] -> ScopeM [(Name, Fixity')]
getDefinedNames kinds = do
  names <- nsNames . everythingInScope <$> getScope
  reportSLn "scope.operators" 20 $ "everythingInScope: " ++ show names
  return [ (x, A.nameFixity $ A.qnameName $ anameName d)
         | (x, ds) <- Map.assocs names
         , d       <- take 1 ds
         , anameKind d `elem` kinds
         ]

-- | Compute all names (first component) and operators (second component) in
--   scope.
localNames :: ScopeM ([Name], [NewNotation])
localNames = do
  defs   <- getDefinedNames [DefName, ConName]
  locals <- scopeLocals <$> getScope
  return $ split $ uniqBy fst $ map localOp locals ++ defs
  where
    localOp (x, y) = (x, A.nameFixity y)
    split ops = ([ x | Left x <- zs], [ y | Right y <- zs ])
        where
            zs = concatMap opOrNot ops

    opOrNot (x, Fixity' fx syn) = Left x
                                :  case x of
                                      Name _ [_] -> []
                                      _ -> [Right (x, fx, syntaxOf x)]
                                ++ case syn of
                                    [] -> []
                                    _ -> [Right (x, fx, syn)]

data UseBoundNames = UseBoundNames | DontUseBoundNames





{-| Builds parser for operator applications from all the operators and function
    symbols in scope. When parsing a pattern we use 'DontUseBoundNames'.

    The effect is that operator parts (that are not constructor parts)
    can be used as atomic names in the pattern (so they can be
    rebound). See test/succeed/OpBind.agda for an example.

    To avoid problems with operators of the same precedence but different
    associativity we decide (completely arbitrary) to fix the precedences of
    operators with the same given precedence in the following order (from
    loosest to hardest):

    - non-associative

    - left associative

    - right associative

    - prefix

    - postfix

    This has the effect that if you mix operators with the same precedence but
    different associativity the parser won't complain. One could argue that
    this is a Bad Thing, but since it's not trivial to implement the check it
    will stay this way until people start complaining about it.

-}

data NotationStyle = InfixS | Prefix | Postfix | Nonfix | None
   deriving (Eq)

fixStyle :: Notation -> NotationStyle
fixStyle [] = None
fixStyle syn = case (isAHole (head syn), isAHole (last syn)) of
  (True,True) -> InfixS
  (True,False) -> Postfix
  (False,True) -> Prefix
  (False,False) -> Nonfix


notationNames :: NewNotation -> [Name]
notationNames (_, _, ps) = [Name noRange [Id x] | IdPart x <- ps ]

buildParser :: forall e. IsExpr e => Range -> UseBoundNames -> ScopeM (ReadP e e)
buildParser r use = do
    (names, ops) <- localNames
    cons         <- getDefinedNames [ConName]
    let conparts   = Set.fromList $ concatMap notationNames $ map oldToNewNotation cons
        opsparts   = Set.fromList $ concatMap notationNames $ ops
        allParts   = Set.union conparts opsparts
        connames   = Set.fromList $ map fst cons
        (non, fix) = partition nonfix ops
        set        = Set.fromList names
        isAtom   x = case use of
                       UseBoundNames     -> not (Set.member x allParts) || Set.member x set
                       DontUseBoundNames -> not (Set.member x conparts) || Set.member x connames
        -- If string is a part of notation, it cannot be used as an identifier,
        -- unless it is also used as an identifier. See issue 307.
    return $ -- traceShow ops $
           recursive $ \p -> -- p is a parser for an arbitrary expression
        concatMap (mkP p) (order fix) -- for infix operators (with outer "holes")
        ++ [ appP p ] -- parser for simple applications
        ++ map (nonfixP . opP p) non -- for things with no outer "holes"
        ++ [ const $ atomP isAtom ]
    where


        level :: NewNotation -> Nat
        level (_name, fixity, _syn) = fixityLevel fixity

        on f g x y = f (g x) (g y)

        isinfixl, isinfixr, isinfix, nonfix, isprefix, ispostfix :: NewNotation -> Bool

        isinfixl (_, LeftAssoc _ _, syn)  = isInfix syn
        isinfixl _                    = False

        isinfixr (_, RightAssoc _ _, syn) = isInfix syn
        isinfixr _                    = False

        isinfix (_, NonAssoc _ _,syn)    = isInfix syn
        isinfix _                     = False

        nonfix (_,_,syn) = fixStyle syn == Nonfix
        isprefix (_,_,syn) = fixStyle syn == Prefix
        ispostfix (_,_,syn) = fixStyle syn == Postfix
        isInfix :: Notation -> Bool
        isInfix syn = fixStyle syn == InfixS

        -- | Group operators by precedence level
        order :: [NewNotation] -> [[NewNotation]]
        order = groupBy ((==) `on` level) . sortBy (compare `on` level)

        -- | Each element of the returned list takes the parser for an
        -- expression of higher precedence as parameter.
        mkP :: ReadP e e -> [NewNotation] -> [ReadP e e -> ReadP e e]
        mkP p0 ops = case concat [infx, inlfx, inrfx, prefx, postfx] of
            []      -> [id]
            fs      -> fs
            where
                inlfx   = fixP infixlP  isinfixl
                inrfx   = fixP infixrP  isinfixr
                infx    = fixP infixP   isinfix
                prefx   = fixP prefixP  isprefix
                postfx  = fixP postfixP ispostfix

                fixP :: (ReadP e (NewNotation,Range,[e]) -> ReadP e e -> ReadP e e) -> (NewNotation -> Bool) -> [ReadP e e -> ReadP e e]
                fixP f g =
                    case filter g ops of
                        []  -> []
                        ops -> [ f $ choice $ map (opP p0) ops ]

---------------------------------------------------------------------------
-- * Expression instances
---------------------------------------------------------------------------

instance IsExpr Expr where
    exprView e = case e of
        Ident (QName x) -> LocalV x
        App _ e1 e2     -> AppV e1 e2
        OpApp r d es    -> OpAppV d es
        HiddenArg _ e   -> HiddenArgV e
        InstanceArg _ e -> InstanceArgV e
        Paren _ e       -> ParenV e
        Lam _ bs    e   -> LamV bs e
        Underscore{}    -> WildV e
        _               -> OtherV e
    unExprView e = case e of
        LocalV x      -> Ident (QName x)
        AppV e1 e2    -> App (fuseRange e1 e2) e1 e2
        OpAppV d es   -> OpApp (fuseRange d es) d es
        HiddenArgV e  -> HiddenArg (getRange e) e
        InstanceArgV e -> InstanceArg (getRange e) e
        ParenV e      -> Paren (getRange e) e
        LamV bs e     -> Lam (fuseRange bs e) bs e
        WildV e       -> e
        OtherV e      -> e


instance IsExpr Pattern where
    exprView e = case e of
        IdentP (QName x) -> LocalV x
        AppP e1 e2       -> AppV e1 e2
        OpAppP r d es    -> OpAppV d (map Ordinary es)
        HiddenP _ e      -> HiddenArgV e
        InstanceP _ e    -> InstanceArgV e
        ParenP _ e       -> ParenV e
        WildP{}          -> WildV e
        _                -> OtherV e
    unExprView e = case e of
        LocalV x         -> IdentP (QName x)
        AppV e1 e2       -> AppP e1 e2
        OpAppV d es      -> let ess :: [Pattern]
                                ess = (map (fromOrdinary __IMPOSSIBLE__) es)
                            in OpAppP (fuseRange d es) d ess
        HiddenArgV e     -> HiddenP (getRange e) e
        InstanceArgV e   -> InstanceP (getRange e) e
        ParenV e         -> ParenP (getRange e) e
        LamV _ _         -> __IMPOSSIBLE__
        WildV e          -> e
        OtherV e         -> e



---------------------------------------------------------------------------
-- * Parse functions
---------------------------------------------------------------------------

-- | Returns the list of possible parses.
parsePattern :: ReadP Pattern Pattern -> Pattern -> [Pattern]
parsePattern prs p = case p of
    AppP p (Arg h r q) -> fullParen' <$> (AppP <$> parsePattern prs p <*> (Arg h r <$> traverse (parsePattern prs) q))
    RawAppP _ ps     -> fullParen' <$> (parsePattern prs =<< parse prs ps)
    OpAppP r d ps    -> fullParen' . OpAppP r d <$> mapM (parsePattern prs) ps
    HiddenP _ _      -> fail "bad hidden argument"
    InstanceP _ _    -> fail "bad instance argument"
    AsP r x p        -> AsP r x <$> parsePattern prs p
    DotP r e         -> return $ DotP r e
    ParenP r p       -> fullParen' <$> parsePattern prs p
    WildP _          -> return p
    AbsurdP _        -> return p
    LitP _           -> return p
    IdentP _         -> return p


-- | Parses a left-hand side, and makes sure that it defined the expected name.
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--      Assume _ * is a constructor. Then 'true *' can be parsed as either the
--      intended _* applied to true, or as true applied to a variable *. If we
--      check arities this problem won't appear.
parseLHS :: Maybe Name -> Pattern -> ScopeM Pattern
parseLHS top p = do
    patP <- buildParser (getRange p) DontUseBoundNames
    cons <- getNames [ConName]
    case filter (validPattern top cons) $ parsePattern patP p of
        [p] -> return p
        []  -> typeError $ NoParseForLHS p
        ps  -> typeError $ AmbiguousParseForLHS p $ map fullParen ps
    where
        getNames kinds = map fst <$> getDefinedNames kinds

        validPattern :: Maybe Name -> [Name] -> Pattern -> Bool
        validPattern (Just top) cons p = case appView p of
            IdentP (QName x) : ps -> x == top && all (validPat cons) ps
            _                     -> False
        validPattern Nothing cons p = validPat cons p

        validPat :: [Name] -> Pattern -> Bool
        validPat cons p = case appView p of
            [_]                   -> True
            IdentP (QName x) : ps -> elem x cons && all (validPat cons) ps
            ps                    -> all (validPat cons) ps

        appView :: Pattern -> [Pattern]
        appView p = case p of
            AppP p a         -> appView p ++ [namedThing (unArg a)]
            OpAppP _ op ps   -> IdentP (QName op) : ps
            ParenP _ p       -> appView p
            RawAppP _ _      -> __IMPOSSIBLE__
            HiddenP _ _      -> __IMPOSSIBLE__
            InstanceP _ _    -> __IMPOSSIBLE__
            _                -> [p]

parseApplication :: [Expr] -> ScopeM Expr
parseApplication [e] = return e
parseApplication es = do
    -- Build the parser
    p <- buildParser (getRange es) UseBoundNames

    -- Parse
    case parse p es of
        [e] -> return e
        []  -> do
          -- When the parser fails and a name is not in scope, it is more
          -- useful to say that to the user rather than just "failed".
          inScope <- partsInScope
          case [ QName x | Ident (QName x) <- es, not (Set.member x inScope) ] of
               []  -> typeError $ NoParseForApplication es
               xs  -> typeError $ NotInScope xs

        es' -> typeError $ AmbiguousParseForApplication es $ map fullParen es'

-- Inserting parenthesis --------------------------------------------------

fullParen :: IsExpr e => e -> e
fullParen e = case exprView $ fullParen' e of
    ParenV e    -> e
    e'          -> unExprView e'

fullParen' :: IsExpr e => e -> e
fullParen' e = case exprView e of
    LocalV _     -> e
    WildV _      -> e
    OtherV _     -> e
    HiddenArgV _ -> e
    InstanceArgV _ -> e
    ParenV _     -> e
    AppV e1 (Arg h r e2) -> par $ unExprView $ AppV (fullParen' e1) (Arg h r e2')
        where
            e2' = case h of
                Hidden    -> e2
                Instance  -> e2
                NotHidden -> fullParen' <$> e2
    OpAppV x es -> par $ unExprView $ OpAppV x $ map (fmap fullParen') es
    LamV bs e -> par $ unExprView $ LamV bs (fullParen e)
    where
        par = unExprView . ParenV

paren :: Monad m => (Name -> m Fixity) -> Expr -> m (Precedence -> Expr)
paren _   e@(App _ _ _)        = return $ \p -> mparen (appBrackets p) e
paren f   e@(OpApp _ op _)     = do fx <- f op; return $ \p -> mparen (opBrackets fx p) e
paren _   e@(Lam _ _ _)        = return $ \p -> mparen (lamBrackets p) e
paren _   e@(AbsurdLam _ _)    = return $ \p -> mparen (lamBrackets p) e
paren _   e@(ExtendedLam _ _)    = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Fun _ _ _)        = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Pi _ _)           = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Let _ _ _)        = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Rec _ _)          = return $ \p -> mparen (appBrackets p) e
paren _   e@(RecUpdate _ _ _)  = return $ \p -> mparen (appBrackets p) e
paren _   e@(WithApp _ _ _)    = return $ \p -> mparen (withAppBrackets p) e
paren _   e@(Ident _)          = return $ \p -> e
paren _   e@(Lit _)            = return $ \p -> e
paren _   e@(QuestionMark _ _) = return $ \p -> e
paren _   e@(Underscore _ _)   = return $ \p -> e
paren _   e@(Set _)            = return $ \p -> e
paren _   e@(SetN _ _)         = return $ \p -> e
paren _   e@(Prop _)           = return $ \p -> e
paren _   e@(Paren _ _)        = return $ \p -> e
paren _   e@(As _ _ _)         = return $ \p -> e
paren _   e@(Dot _ _)          = return $ \p -> e
paren _   e@(Absurd _)         = return $ \p -> e
paren _   e@(ETel _)           = return $ \p -> e
paren _   e@(RawApp _ _)       = __IMPOSSIBLE__
paren _   e@(HiddenArg _ _)    = __IMPOSSIBLE__
paren _   e@(InstanceArg _ _)  = __IMPOSSIBLE__
paren _   e@(QuoteGoal _ _ _)  = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Quote _)          = return $ \p -> e
paren _   e@(QuoteTerm _)      = return $ \p -> e
paren _   e@(Unquote _)        = return $ \p -> e
paren _   e@(DontCare _)       = return $ \p -> e

mparen :: Bool -> Expr -> Expr
mparen True  e = Paren (getRange e) e
mparen False e = e
