{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-| The parser doesn't know about operators and parses everything as normal
    function application. This module contains the functions that parses the
    operators properly. For a stand-alone implementation of this see
    @src\/prototyping\/mixfix\/old@.

    It also contains the function that puts parenthesis back given the
    precedence of the context.
-}
module Agda.Syntax.Concrete.Operators
    ( parseApplication
    , parseModuleApplication
    , parseLHS
    , parsePattern
    , parsePatternSyn
    ) where

import Control.DeepSeq
import Control.Applicative
import Control.Monad

import Data.Either (partitionEithers)
import Data.Function
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse)
import qualified Data.Traversable as Trav

import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Concrete hiding (appView)
import Agda.Syntax.Concrete.Operators.Parser
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (typeError, TypeError(..), LHSOrPatSyn(..))
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.State (getScope)
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Either
import Agda.Utils.ReadP
#if MIN_VERSION_base(4,8,0)
import Agda.Utils.List hiding ( uncons )
#else
import Agda.Utils.List
#endif

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Billing
---------------------------------------------------------------------------

-- | Bills the operator parser.

billToParser :: ScopeM a -> ScopeM a
billToParser = Bench.billTo [Bench.Parsing, Bench.Operators]

---------------------------------------------------------------------------
-- * Building the parser
---------------------------------------------------------------------------

type FlatScope = Map QName [AbstractName]

-- | Compute all defined names in scope and their fixities/notations.
-- Note that overloaded names (constructors) can have several
-- fixities/notations. Then we 'mergeNotations'. (See issue 1194.)
getDefinedNames :: [KindOfName] -> FlatScope -> [[NewNotation]]
getDefinedNames kinds names =
  [ mergeNotations $
      map (\d -> namesToNotation x (A.qnameName $ anameName d)) ds
  | (x, ds) <- Map.toList names
  , any ((`elem` kinds) . anameKind) ds
  , not (null ds)
  -- Andreas, 2013-03-21 see Issue 822
  -- Names can have different kinds, i.e., 'defined' and 'constructor'.
  -- We need to consider all names that have *any* matching kind,
  -- not only those whose first appearing kind is matching.
  ]

-- | Compute all names (first component) and operators/notations
-- (second component) in scope.
localNames :: FlatScope -> ScopeM ([QName], [NewNotation])
localNames flat = do
  let defs = getDefinedNames allKindsOfNames flat
  locals <- notShadowedLocals <$> getLocalVars
  -- Note: Debug printout aligned with the one in buildParsers.
  reportSLn "scope.operators" 50 $ unlines
    [ "flat  = " ++ show flat
    , "defs  = " ++ show defs
    , "locals= " ++ show locals
    ]
  let localNots  = map localOp locals
      localNames = Set.fromList $ map notaName localNots
      otherNots  = filter (\n -> not (Set.member (notaName n) localNames))
                          (concat defs)
  return $ split $ localNots ++ otherNots
  where
    localOp (x, y) = namesToNotation (QName x) y
    split ops      = partitionEithers $ concatMap opOrNot ops
    opOrNot n      = Left (notaName n) :
                     if null (notation n) then [] else [Right n]

-- | Data structure filled in by @buildParsers@.
--   The top-level parser @pTop@ is of primary interest,
--   but @pArgs@ is used to convert module application
--   from concrete to abstract syntax.
data Parsers e = Parsers
  { pTop    :: ReadP e e
  , pApp    :: ReadP e e
  , pArgs   :: ReadP e [NamedArg e]
  , pNonfix :: ReadP e e
  , pAtom   :: ReadP e e
  }

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
buildParsers :: forall e. IsExpr e => Range -> FlatScope -> UseBoundNames -> ScopeM (Parsers e)
buildParsers r flat use = do
    (names, ops) <- localNames flat
    let cons = getDefinedNames [ConName, PatternSynName] flat
    reportSLn "scope.operators" 50 $ unlines
      [ "names = " ++ show names
      , "ops   = " ++ show ops
      , "cons  = " ++ show cons ]
    let conparts   = Set.fromList $ concatMap notationNames $ concat cons
        opsparts   = Set.fromList $ concatMap notationNames ops
        allParts   = Set.union conparts opsparts
        connames   = Set.fromList $ map (notaName . head) cons
        (non, fix) = partition nonfix ops
        set        = Set.fromList names
        isAtom   x = case use of
                       UseBoundNames     -> not (Set.member x allParts) || Set.member x set
                       DontUseBoundNames -> not (Set.member x conparts) || Set.member x connames
        -- If string is a part of notation, it cannot be used as an identifier,
        -- unless it is also used as an identifier. See issue 307.

    let chain = foldr ( $ )

    return $ Data.Function.fix $ \p -> Parsers
        { pTop    = chain (pApp p) (concatMap (mkP (pTop p)) (order fix))
        , pApp    = appP (pNonfix p) (pArgs p)
        , pArgs   = argsP (pNonfix p)
        , pNonfix = chain (pAtom p) (map (nonfixP . opP (pTop p)) non)
        , pAtom   = atomP isAtom
        }
    where
        level :: NewNotation -> Integer
        level = fixityLevel . notaFixity

        nonfix, isprefix, ispostfix :: NewNotation -> Bool
        nonfix    = (== NonfixNotation)  . notationKind . notation
        isprefix  = (== PrefixNotation)  . notationKind . notation
        ispostfix = (== PostfixNotation) . notationKind . notation

        isinfix :: Associativity -> NewNotation -> Bool
        isinfix ass syn =
          notationKind (notation syn) == InfixNotation
            &&
          fixityAssoc (notaFixity syn) == ass

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
                inlfx   = fixP infixlP  (isinfix LeftAssoc)
                inrfx   = fixP infixrP  (isinfix RightAssoc)
                infx    = fixP infixP   (isinfix NonAssoc)
                prefx   = fixP prefixP  isprefix
                postfx  = fixP postfixP ispostfix

                fixP :: (ReadP e (NewNotation,Range,[e]) -> ReadP e e -> ReadP e e) -> (NewNotation -> Bool) -> [ReadP e e -> ReadP e e]
                fixP f g =
                    case filter g ops of
                        []  -> []
                        ops -> [ f $ choice $ map (opP p0) ops ]

---------------------------------------------------------------------------
-- * Helpers for pattern and lhs parsing
---------------------------------------------------------------------------

-- | View a pattern @p@ as a list @p0 .. pn@ where @p0@ is the identifier
--   (in most cases a constructor).
--
--  Pattern needs to be parsed already (operators resolved).
patternAppView :: Pattern -> [NamedArg Pattern]
patternAppView p = case p of
    AppP p arg      -> patternAppView p ++ [arg]
    OpAppP _ x _ ps -> defaultNamedArg (IdentP x) : ps
    ParenP _ p      -> patternAppView p
    RawAppP _ _     -> __IMPOSSIBLE__
    _               -> [ defaultNamedArg p ]


---------------------------------------------------------------------------
-- * Parse functions
---------------------------------------------------------------------------

-- | Returns the list of possible parses.
parsePat :: ReadP Pattern Pattern -> Pattern -> [Pattern]
parsePat prs p = case p of
    AppP p (Common.Arg info q) ->
        fullParen' <$> (AppP <$> parsePat prs p <*> (Common.Arg info <$> traverse (parsePat prs) q))
    RawAppP _ ps     -> fullParen' <$> (parsePat prs =<< parse prs ps)
    OpAppP r d ns ps -> fullParen' . OpAppP r d ns <$> (mapM . traverse . traverse) (parsePat prs) ps
    HiddenP _ _      -> fail "bad hidden argument"
    InstanceP _ _    -> fail "bad instance argument"
    AsP r x p        -> AsP r x <$> parsePat prs p
    DotP r e         -> return $ DotP r e
    ParenP r p       -> fullParen' <$> parsePat prs p
    WildP _          -> return p
    AbsurdP _        -> return p
    LitP _           -> return p
    QuoteP _         -> return p
    IdentP _         -> return p


{- Implement parsing of copattern left hand sides, e.g.

  record Tree (A : Set) : Set where
    field
      label : A
      child : Bool -> Tree A

  -- corecursive function defined by copattern matching
  alternate : {A : Set}(a b : A) -> Tree A
  -- shallow copatterns
         label (alternate a b)              = a
         child (alternate a b) True         = alternate b a
  -- deep copatterns:
  label (child (alternate a b) False)       = b
  child (child (alternate a b) False) True  = alternate a b
  child (child (alternate a b) False) False = alternate a b

  Delivers an infinite tree

                   a
              b        b
            a   a    a   a
           b b b b  b b b b
                 ...

  Each lhs is a pattern tree with a distinct path of destructors
  ("child", "label") from the root to the defined symbol ("alternate").
  All branches besides this distinct path are patterns.

  Syntax.Concrete.LHSCore represents a lhs
   - the destructor path
   - the side patterns
   - the defined function symbol
   - the applied patterns
-}

type ParseLHS = Either Pattern (Name, LHSCore)

parseLHS' :: LHSOrPatSyn -> Maybe Name -> Pattern -> ScopeM ParseLHS
parseLHS' lhsOrPatSyn top p = do
    let ms = qualifierModules $ patternQNames p
    flat <- flattenScope ms <$> getScope
    parsers <- buildParsers (getRange p) flat DontUseBoundNames
    let patP = pTop parsers
    let cons = getNames [ConName, PatternSynName] flat
    let flds = getNames [FldName] flat
    case [ res | p' <- force $ parsePat patP p
               , res <- validPattern (PatternCheckConfig top cons flds) p' ] of
        [(p,lhs)] -> return lhs
        []        -> typeError $ NoParseForLHS lhsOrPatSyn p
        rs        -> typeError $ AmbiguousParseForLHS lhsOrPatSyn p $
                       map (fullParen . fst) rs
    where
        getNames kinds flat =
          map (notaName . head) $ getDefinedNames kinds flat

        -- validPattern returns an empty or singleton list (morally a Maybe)
        validPattern :: PatternCheckConfig -> Pattern -> [(Pattern, ParseLHS)]
        validPattern conf p = case (classifyPattern conf p, top) of
            (Just r@(Left _), Nothing) -> [(p, r)] -- expect pattern
            (Just r@(Right _), Just{}) -> [(p, r)] -- expect lhs
            _ -> []

-- | Name sets for classifying a pattern.
data PatternCheckConfig = PatternCheckConfig
  { topName  :: Maybe Name  -- ^ name of defined symbol
  , conNames :: [QName]     -- ^ valid constructor names
  , fldNames :: [QName]     -- ^ valid field names
  }

-- | Returns zero or one classified patterns.
classifyPattern :: PatternCheckConfig -> Pattern -> Maybe ParseLHS
classifyPattern conf p =
  case patternAppView p of

    -- case @f ps@
    Common.Arg _ (Named _ (IdentP x@(QName f))) : ps | Just f == topName conf -> do
      guard $ all validPat ps
      return $ Right (f, LHSHead f ps)

    -- case @d ps@
    Common.Arg _ (Named _ (IdentP x)) : ps | x `elem` fldNames conf -> do
      -- ps0 :: [NamedArg ParseLHS]
      ps0 <- mapM classPat ps
      let (ps1, rest) = span (isLeft . namedArg) ps0
      (p2, ps3) <- uncons rest -- when (null rest): no field pattern or def pattern found
      guard $ all (isLeft . namedArg) ps3
      let (f, lhs)      = fromR p2
          (ps', _:ps'') = splitAt (length ps1) ps
      return $ Right (f, LHSProj x ps' lhs ps'')

    -- case: ordinary pattern
    _ -> do
      guard $ validConPattern (conNames conf) p
      return $ Left p

  where -- allNames = conNames conf ++ fldNames conf
        validPat = validConPattern (conNames conf) . namedArg
        classPat :: NamedArg Pattern -> Maybe (NamedArg ParseLHS)
        classPat = Trav.mapM (Trav.mapM (classifyPattern conf))
        fromR :: NamedArg (Either a (b, c)) -> (b, NamedArg c)
        fromR (Common.Arg info (Named n (Right (b, c)))) = (b, Common.Arg info (Named n c))
        fromR (Common.Arg info (Named n (Left  a     ))) = __IMPOSSIBLE__



-- | Parses a left-hand side, and makes sure that it defined the expected name.
parseLHS :: Name -> Pattern -> ScopeM LHSCore
parseLHS top p = billToParser $ do
  res <- parseLHS' IsLHS (Just top) p
  case res of
    Right (f, lhs) -> return lhs
    _ -> typeError $ NoParseForLHS IsLHS p

-- | Parses a pattern.
parsePattern :: Pattern -> ScopeM Pattern
parsePattern = parsePatternOrSyn IsLHS

parsePatternSyn :: Pattern -> ScopeM Pattern
parsePatternSyn = parsePatternOrSyn IsPatSyn

parsePatternOrSyn :: LHSOrPatSyn -> Pattern -> ScopeM Pattern
parsePatternOrSyn lhsOrPatSyn p = billToParser $ do
  res <- parseLHS' lhsOrPatSyn Nothing p
  case res of
    Left p -> return p
    _      -> typeError $ NoParseForLHS lhsOrPatSyn p

-- | Helper function for 'parseLHS' and 'parsePattern'.
validConPattern :: [QName] -> Pattern -> Bool
validConPattern cons p = case appView p of
    [_]           -> True
    IdentP x : ps -> elem x cons && all (validConPattern cons) ps
    [QuoteP _, _] -> True
    _             -> False
-- Andreas, 2012-06-04: I do not know why the following line was
-- the catch-all case.  It seems that the new catch-all works also
-- and is more logical.
--    ps            -> all (validConPattern cons) ps

-- | Helper function for 'parseLHS' and 'parsePattern'.
appView :: Pattern -> [Pattern]
appView p = case p of
    AppP p a         -> appView p ++ [namedArg a]
    OpAppP _ op _ ps -> IdentP op : map namedArg ps
    ParenP _ p       -> appView p
    RawAppP _ _      -> __IMPOSSIBLE__
    HiddenP _ _      -> __IMPOSSIBLE__
    InstanceP _ _    -> __IMPOSSIBLE__
    _                -> [p]

-- | Return all qualifiers occuring in a list of 'QName's.
--   Each qualifier is returned as a list of names, e.g.
--   for @Data.Nat._+_@ we return the list @[Data,Nat]@.
qualifierModules :: [QName] -> [[Name]]
qualifierModules qs =
  nub $ filter (not . null) $ map (init . qnameParts) qs

-- | Parse a list of expressions into an application.
parseApplication :: [Expr] -> ScopeM Expr
parseApplication [e] = return e
parseApplication es  = billToParser $ do
    -- Build the parser
    let ms = qualifierModules [ q | Ident q <- es ]
    flat <- flattenScope ms <$> getScope
    p <- buildParsers (getRange es) flat UseBoundNames

    -- Parse
    case force $ parse (pTop p) es of
        [e] -> return e
        []  -> typeError $ NoParseForApplication es
        es' -> typeError $ AmbiguousParseForApplication es $ map fullParen es'

parseModuleIdentifier :: Expr -> ScopeM QName
parseModuleIdentifier (Ident m) = return m
parseModuleIdentifier e = typeError $ NotAModuleExpr e

parseRawModuleApplication :: [Expr] -> ScopeM (QName, [NamedArg Expr])
parseRawModuleApplication es = billToParser $ do
    let e : es_args = es
    m <- parseModuleIdentifier e

    -- Build the arguments parser
    let ms = qualifierModules [ q | Ident q <- es_args ]
    flat <- flattenScope ms <$> getScope
    p <- buildParsers (getRange es_args) flat UseBoundNames

    -- Parse
    case {-force $-} parse (pArgs p) es_args of -- TODO: not sure about forcing
        [as] -> return (m, as)
        []   -> typeError $ NoParseForApplication es
        ass -> do
          let f = fullParen . foldl (App noRange) (Ident m)
          typeError $ AmbiguousParseForApplication es
                    $ map f ass

-- | Parse an expression into a module application
--   (an identifier plus a list of arguments).
parseModuleApplication :: Expr -> ScopeM (QName, [NamedArg Expr])
parseModuleApplication (RawApp _ es) = parseRawModuleApplication es
parseModuleApplication (App r e1 e2) = do -- TODO: do we need this case?
    (m, args) <- parseModuleApplication e1
    return (m, args ++ [e2])
parseModuleApplication e = do
    m <- parseModuleIdentifier e
    return (m, [])

---------------------------------------------------------------------------
-- * Inserting parenthesis
---------------------------------------------------------------------------

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
    AppV e1 (Common.Arg info e2) -> par $ unExprView $ AppV (fullParen' e1) (Common.Arg info e2')
        where
            e2' = case argInfoHiding info of
                Hidden    -> e2
                Instance  -> e2
                NotHidden -> fullParen' <$> e2
    OpAppV x ns es -> par $ unExprView $ OpAppV x ns $ (map . fmap . fmap . fmap) fullParen' es
    LamV bs e -> par $ unExprView $ LamV bs (fullParen e)
    where
        par = unExprView . ParenV
