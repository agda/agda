{-# LANGUAGE CPP, ScopedTypeVariables #-}

{-| The parser doesn't know about operators and parses everything as normal
    function application. This module contains the functions that parses the
    operators properly. For a stand-alone implementation of this see
    @src\/prototyping\/mixfix\/old@.

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
import Agda.Syntax.Concrete hiding (appView)
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

partsInScope :: FlatScope -> ScopeM (Set QName)
partsInScope flat = do
    (names, ops) <- localNames flat
    let xs = concatMap parts names ++ concatMap notationNames ops
    return $ Set.fromList xs
    where
        qual xs x = foldr Qual (QName x) xs
        parts q = parts' (init $ qnameParts q) (unqualify q)
        parts' ms (NoName _ _)   = []
        parts' ms x@(Name _ [_]) = [qual ms x]
                                   -- The first part should be qualified, but not the rest
        parts' ms x@(Name _ xs)  = qual ms x : qual ms (Name noRange [first]) : [ QName $ Name noRange [i] | i <- iparts ]
          where
            first:iparts = [ i | i@(Id {}) <- xs ]

type FlatScope = Map.Map QName [AbstractName]

-- | Compute all unqualified defined names in scope and their fixities.
getDefinedNames :: [KindOfName] -> FlatScope -> [(QName, Fixity')]
getDefinedNames kinds names =
  [ (x, A.nameFixity $ A.qnameName $ anameName d)
  | (x, ds) <- Map.toList names
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
    localOp (x, y) = (QName x, A.nameFixity y)
    split ops = ([ x | Left x <- zs], [ y | Right y <- zs ])
        where
            zs = concatMap opOrNot ops

    opOrNot (q, Fixity' fx syn) = Left q
                                :  case unqualify q of
                                      Name _ [_] -> []
                                      x -> [Right (q, fx, syntaxOf x)]
                                ++ case syn of
                                    [] -> []
                                    _ -> [Right (q, fx, syn)]

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


notationNames :: NewNotation -> [QName]
notationNames (q, _, ps) = zipWith ($) (requal : repeat QName) [Name noRange [Id x] | IdPart x <- ps ]
  where
    ms       = init (qnameParts q)
    requal x = foldr Qual (QName x) ms

buildParser :: forall e. IsExpr e => Range -> FlatScope -> UseBoundNames -> ScopeM (ReadP e e)
buildParser r flat use = do
    (names, ops) <- localNames flat
    let cons = getDefinedNames [ConName, PatternSynName] flat
    reportSLn "scope.operators" 50 $ unlines
      [ "names = " ++ show names
      , "ops   = " ++ show ops
      , "cons  = " ++ show cons ]
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
        Ident x         -> LocalV x
        App _ e1 e2     -> AppV e1 e2
        OpApp r d es    -> OpAppV d es
        HiddenArg _ e   -> HiddenArgV e
        InstanceArg _ e -> InstanceArgV e
        Paren _ e       -> ParenV e
        Lam _ bs    e   -> LamV bs e
        Underscore{}    -> WildV e
        _               -> OtherV e
    unExprView e = case e of
        LocalV x      -> Ident x
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
        IdentP x      -> LocalV x
        AppP e1 e2    -> AppV e1 e2
        OpAppP r d es -> OpAppV d (map Ordinary es)
        HiddenP _ e   -> HiddenArgV e
        InstanceP _ e -> InstanceArgV e
        ParenP _ e    -> ParenV e
        WildP{}       -> WildV e
        _             -> OtherV e
    unExprView e = case e of
        LocalV x       -> IdentP x
        AppV e1 e2     -> AppP e1 e2
        OpAppV d es    -> let ess :: [Pattern]
                              ess = (map (fromOrdinary __IMPOSSIBLE__) es)
                          in OpAppP (fuseRange d es) d ess
        HiddenArgV e   -> HiddenP (getRange e) e
        InstanceArgV e -> InstanceP (getRange e) e
        ParenV e       -> ParenP (getRange e) e
        LamV _ _       -> __IMPOSSIBLE__
        WildV e        -> e
        OtherV e       -> e

{- TRASH
instance IsExpr LHSCore where
    exprView e = case e of
        LHSHead f ps -> foldl AppV (LocalV f) $ map exprView ps
        LHSProj d ps1 e ps2 -> foldl AppV (LocalV d) $
          map exprView ps1 ++ exprView e : map exprView ps2
    unExprView e = LHSHead f ps
      where p :: Pattern
            p = unExprView
            (f, ps) = lhsArgs p
-}

-- Andreas, 2011-11-24 moved here from ConcreteToAbstract
lhsArgs :: Pattern -> (Name, [NamedArg Pattern])
lhsArgs p = case lhsArgs' p of
              Just (x, args) -> (x, args)
              Nothing        -> __IMPOSSIBLE__

lhsArgs' :: Pattern -> Maybe (Name, [NamedArg Pattern])
lhsArgs' p = case appView p of
    Arg _ _ (Named _ (IdentP (QName x))) : ps -> Just (x, ps)
    _                                         -> Nothing
    where
        mkHead    = Arg NotHidden Relevant . unnamed
        notHidden = Arg NotHidden Relevant . unnamed
        appView p = case p of
            AppP p arg    -> appView p ++ [arg]
            OpAppP _ x ps -> mkHead (IdentP $ QName x) : map notHidden ps
            ParenP _ p    -> appView p
            RawAppP _ _   -> __IMPOSSIBLE__
            _             -> [ mkHead p ]


---------------------------------------------------------------------------
-- * Parse functions
---------------------------------------------------------------------------

-- | Returns the list of possible parses.
parsePat :: ReadP Pattern Pattern -> Pattern -> [Pattern]
parsePat prs p = case p of
    AppP p (Arg h r q) -> fullParen' <$> (AppP <$> parsePat prs p <*> (Arg h r <$> traverse (parsePat prs) q))
    RawAppP _ ps     -> fullParen' <$> (parsePat prs =<< parse prs ps)
    OpAppP r d ps    -> fullParen' . OpAppP r d <$> mapM (parsePat prs) ps
    HiddenP _ _      -> fail "bad hidden argument"
    InstanceP _ _    -> fail "bad instance argument"
    AsP r x p        -> AsP r x <$> parsePat prs p
    DotP r e         -> return $ DotP r e
    ParenP r p       -> fullParen' <$> parsePat prs p
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
parseLHS :: Name -> Pattern -> ScopeM LHSCore
parseLHS = parseLhsOrPatternSyn True

parsePatternSyn :: Pattern -> ScopeM Pattern
parsePatternSyn = parseLhsOrPatternSyn False Nothing

parseLhsOrPatternSyn :: Bool -> Maybe Name -> Pattern -> ScopeM Pattern
parseLhsOrPatternSyn isLHS top p = do
    let ms = qualifierModules $ patternQNames p
    flat <- flattenScope ms <$> getScope
    patP <- buildParser (getRange p) flat DontUseBoundNames
    let cons = getNames [ConName, PatternSynName] flat
    reportSLn "parse.op" 10 $ "cons = " ++ show cons ++ "\np = " ++ show p
    reportSLn "parse.op" 10 $ "parsed = " ++ show (parsePattern patP p)
    case filter (validPattern top cons) $ parsePattern patP p of
        [p] -> return p
        []  -> typeError $ NoParseForLHS p
        ps  -> typeError $ AmbiguousParseForLHS p $ map fullParen ps
    where
        getNames kinds flat = map fst $ getDefinedNames kinds flat

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
            OpAppP _ op ps   -> IdentP op : ps
            ParenP _ p       -> appView p
            RawAppP _ _      -> __IMPOSSIBLE__
            HiddenP _ _      -> __IMPOSSIBLE__
            InstanceP _ _    -> __IMPOSSIBLE__
            _                -> [p]
-}

-- | Parses a pattern.
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--      Assume _ * is a constructor. Then 'true *' can be parsed as either the
--      intended _* applied to true, or as true applied to a variable *. If we
--      check arities this problem won't appear.
parsePattern :: Pattern -> ScopeM Pattern
parsePattern p = do
    patP <- buildParser (getRange p) DontUseBoundNames
    cons <- getNames [ConName]
    case filter (validPat cons) $ parsePat patP p of
        [p] -> return p
        []  -> typeError $ NoParseForLHS p
        ps  -> typeError $ AmbiguousParseForLHS p $ map fullParen ps
    where
        getNames kinds = map fst <$> getDefinedNames kinds

-- | Helper function for 'parseLHS' and 'parsePattern'.
validPat :: [Name] -> Pattern -> Bool
validPat cons p = case appView p of
    [_]                   -> True
    IdentP (QName x) : ps -> elem x cons && all (validPat cons) ps
    ps                    -> all (validPat cons) ps

-- | Helper function for 'parseLHS' and 'parsePattern'.
appView :: Pattern -> [Pattern]
appView p = case p of
    AppP p a         -> appView p ++ [namedThing (unArg a)]
    OpAppP _ op ps   -> IdentP (QName op) : ps
    ParenP _ p       -> appView p
    RawAppP _ _      -> __IMPOSSIBLE__
    HiddenP _ _      -> __IMPOSSIBLE__
    InstanceP _ _    -> __IMPOSSIBLE__
    _                -> [p]



patternQNames :: Pattern -> [QName]
patternQNames p = case p of
  RawAppP _ ps     -> concatMap patternQNames ps
  IdentP q         -> [q]
  ParenP _ p       -> patternQNames p
  OpAppP r d ps    -> __IMPOSSIBLE__
  AppP{}           -> __IMPOSSIBLE__
  _                -> []

qualifierModules :: [QName] -> [[Name]]
qualifierModules qs =
  nub $ filter (not . null) $ map (init . qnameParts) qs

parseApplication :: [Expr] -> ScopeM Expr
parseApplication [e] = return e
parseApplication es = do
    -- Build the parser
    let ms = qualifierModules [ q | Ident q <- es ]
    flat <- flattenScope ms <$> getScope
    p <- buildParser (getRange es) flat UseBoundNames

    -- Parse
    case parse p es of
        [e] -> return e
        []  -> do
          -- When the parser fails and a name is not in scope, it is more
          -- useful to say that to the user rather than just "failed".
          inScope <- partsInScope flat
          case [ x | Ident x <- es, not (Set.member x inScope) ] of
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

paren :: Monad m => (QName -> m Fixity) -> Expr -> m (Precedence -> Expr)
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
