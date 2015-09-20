{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
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

import Control.Arrow ((***), (&&&), first, second)
import Control.DeepSeq
import Control.Applicative
import Control.Monad

import Data.Either (partitionEithers)
import qualified Data.Foldable as Fold
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
import Agda.Utils.Parser.MemoisedCPS (memoise)
import Agda.Utils.Pretty
#if MIN_VERSION_base(4,8,0)
import Agda.Utils.List hiding ( uncons )
#else
import Agda.Utils.List
#endif
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie

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
  return $ second (map useDefaultFixity) $ split $ localNots ++ otherNots
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
  { pTop    :: Parser e e
  , pApp    :: Parser e e
  , pArgs   :: Parser e [NamedArg e]
  , pNonfix :: Parser e e
  , pAtom   :: Parser e e
  }

data ExprKind = IsPattern | IsExpr
  deriving (Eq, Show)

-- | Builds a parser for operator applications from all the operators
-- and function symbols in scope.
--
-- When parsing a pattern we do not use bound names. The effect is
-- that operator parts (that are not constructor parts) can be used as
-- atomic names in the pattern (so they can be rebound). See
-- @test/succeed/OpBind.agda@ for an example.
--
-- When parsing a pattern we also disallow the use of sections, mainly
-- because there is little need for sections in patterns. Note that
-- sections are parsed by splitting up names into multiple tokens
-- (@_+_@ is replaced by @_@, @+@ and @_@), and if we were to support
-- sections in patterns, then we would have to accept certain such
-- sequences of tokens as single pattern variables.
--
-- The list of names must include every name part in the
-- expression/pattern to be parsed (excluding name parts inside things
-- like parenthesised subexpressions that are treated as atoms). The
-- list is used to optimise the parser. For instance, a given notation
-- is only included in the generated grammar if all of the notation's
-- name parts are present in the list of names.
--
-- The returned list contains all operators/notations/sections that
-- were used to generate the grammar.

buildParsers ::
  forall e. IsExpr e =>
  Range -> FlatScope -> ExprKind -> [QName] ->
  ScopeM (ParseSections, [NotationSection], Parsers e)
buildParsers r flat kind exprNames = do
    (names, ops) <- localNames flat

    let -- All names.
        namesInExpr :: Set QName
        namesInExpr = Set.fromList exprNames

        partListsInExpr' = map (nameParts . unqualify) $
                           Set.toList namesInExpr

        partListTrie f =
          foldr (\ps -> Trie.union (Trie.everyPrefix ps ()))
                Trie.empty
                (f partListsInExpr')

        -- All names.
        partListsInExpr :: Trie NamePart ()
        partListsInExpr = partListTrie id

        -- All names, with the name parts in reverse order.
        reversedPartListsInExpr :: Trie NamePart ()
        reversedPartListsInExpr = partListTrie (map reverse)

        -- Every regular name part (not holes etc.).
        partsInExpr :: Set RawName
        partsInExpr =
          Set.fromList [ s | Id s <- concat partListsInExpr' ]

        -- Are all name parts present in the expression?
        partsPresent n =
          [ Set.member p partsInExpr
          | p <- stringParts (notation n)
          ]

        addHole True  p = [Hole, Id p]
        addHole False p = [Id p]

        -- Is the first identifier part present in n present in the
        -- expression, without any preceding name parts, except for a
        -- leading underscore iff withHole is True?
        firstPartPresent withHole n =
          Trie.member (addHole withHole p) partListsInExpr
          where
          p = case n of
            NormalHole{} : IdPart p : _ -> p
            IdPart p : _                -> p
            _                           -> __IMPOSSIBLE__

        -- Is the last identifier part present in n present in the
        -- expression, without any succeeding name parts, except for a
        -- trailing underscore iff withHole is True?
        lastPartPresent withHole n =
          Trie.member (addHole withHole p) reversedPartListsInExpr
          where
          p = case reverse n of
            NormalHole{} : IdPart p : _ -> p
            IdPart p : _                -> p
            _                           -> __IMPOSSIBLE__

        -- | Are the initial and final identifier parts present with
        -- the right mix of leading and trailing underscores?
        correctUnderscores :: Bool -> Bool -> Notation -> Bool
        correctUnderscores withInitialHole withFinalHole n =
          firstPartPresent withInitialHole n
            &&
          lastPartPresent  withFinalHole   n

        -- Should be used with operators (not sections) and notations
        -- coming from syntax declarations.
        filterCorrectUnderscoresOp :: [NewNotation] -> [NotationSection]
        filterCorrectUnderscoresOp ns =
          [ noSection n
          | n <- ns
          , if notaIsOperator n
            then correctUnderscores False False (notation n)
            else all (\s -> Trie.member [Id s] partListsInExpr)
                     (stringParts $ notation n)
          ]

        -- Should be used with sections.
        correctUnderscoresSect :: NotationKind -> Notation -> Bool
        correctUnderscoresSect k n = case (k, notationKind n) of
          (PrefixNotation,  InfixNotation)   -> correctUnderscores True False n
          (PostfixNotation, InfixNotation)   -> correctUnderscores False True n
          (NonfixNotation,  InfixNotation)   -> correctUnderscores True True n
          (NonfixNotation,  PrefixNotation)  -> correctUnderscores False True n
          (NonfixNotation,  PostfixNotation) -> correctUnderscores True False n
          _                                  -> __IMPOSSIBLE__

        -- If "or" is replaced by "and" in conParts/allParts below,
        -- then the misspelled operator application "if x thenn x else
        -- x" can be parsed as "if" applied to five arguments,
        -- resulting in a confusing error message claiming that "if"
        -- is not in scope.

        (non, fix) = partition nonfix (filter (and . partsPresent) ops)

        cons       = getDefinedNames [ConName, PatternSynName] flat
        conNames   = Set.fromList $
                       filter (flip Set.member namesInExpr) $
                       map (notaName . head) cons
        conParts   = Set.fromList $
                       concatMap notationNames $
                       filter (or . partsPresent) $
                       concat cons

        allNames   = Set.fromList $
                       filter (flip Set.member namesInExpr) names
        allParts   = Set.union conParts
                       (Set.fromList $
                        concatMap notationNames $
                        filter (or . partsPresent) ops)

        isAtom   x = case kind of
                       IsExpr    -> not (Set.member x allParts) || Set.member x allNames
                       IsPattern -> not (Set.member x conParts) || Set.member x conNames
        -- If string is a part of notation, it cannot be used as an identifier,
        -- unless it is also used as an identifier. See issue 307.

        parseSections = case kind of
          IsPattern -> DoNotParseSections
          IsExpr    -> ParseSections

    let nonClosedSections l ns =
          case parseSections of
            DoNotParseSections -> []
            ParseSections      ->
              [ NotationSection n k (Just l) True
              | n <- ns
              , isinfix n && notaIsOperator n
              , k <- [PrefixNotation, PostfixNotation]
              , correctUnderscoresSect k (notation n)
              ]

        unrelatedOperators :: [NotationSection]
        unrelatedOperators =
          filterCorrectUnderscoresOp unrelated
            ++
          nonClosedSections Unrelated unrelated
          where
          unrelated = filter ((== Unrelated) . level) fix

        nonWithSections :: [NotationSection]
        nonWithSections =
          map (\s -> s { sectLevel = Nothing })
              (filterCorrectUnderscoresOp non)
            ++
          case parseSections of
            DoNotParseSections -> []
            ParseSections      ->
              [ NotationSection n NonfixNotation Nothing True
              | n <- fix
              , notaIsOperator n
              , correctUnderscoresSect NonfixNotation (notation n)
              ]

        -- The triples have the form (level, operators). The lowest
        -- level comes first.
        relatedOperators :: [(Integer, [NotationSection])]
        relatedOperators =
          map (\((l, ns) : rest) -> (l, ns ++ concat (map snd rest))) .
          groupBy ((==) `on` fst) .
          sortBy (compare `on` fst) .
          mapMaybe (\n -> case level n of
                            Unrelated     -> Nothing
                            r@(Related l) ->
                              Just (l, filterCorrectUnderscoresOp [n] ++
                                       nonClosedSections r [n])) $
          fix

        everything :: [NotationSection]
        everything =
          concatMap snd relatedOperators ++
          unrelatedOperators ++
          nonWithSections

    reportSLn "scope.operators" 50 $ unlines
      [ "unrelatedOperators = " ++ show unrelatedOperators
      , "nonWithSections    = " ++ show nonWithSections
      , "relatedOperators   = " ++ show relatedOperators
      ]

    return (parseSections, everything, Data.Function.fix $ \p -> Parsers
        { pTop    = memoise TopK $
                    Fold.asum $
                      foldr ($) (pApp p)
                        (map (\(l, ns) higher ->
                                 mkP (Right l) parseSections
                                     (pTop p) ns higher True)
                             relatedOperators) :
                      map (\(k, n) ->
                              mkP (Left k) parseSections
                                  (pTop p) [n] (pApp p) False)
                          (zip [0..] unrelatedOperators)
        , pApp    = memoise AppK $ appP (pNonfix p) (pArgs p)
        , pArgs   = argsP (pNonfix p)
        , pNonfix = memoise NonfixK $
                    Fold.asum $
                      pAtom p :
                      flip map nonWithSections (\sect ->
                        let n = sectNotation sect

                            inner :: forall k. NK k ->
                                     Parser e (OperatorType k e)
                            inner = opP parseSections (pTop p) n
                        in
                        case notationKind (notation n) of
                          InfixNotation ->
                            flip ($) <$> placeholder Beginning
                                     <*> inner In
                                     <*> placeholder End
                          PrefixNotation ->
                            inner Pre <*> placeholder End
                          PostfixNotation ->
                            flip ($) <$> placeholder Beginning
                                     <*> inner Post
                          NonfixNotation -> inner Non
                          NoNotation     -> __IMPOSSIBLE__)
        , pAtom   = atomP isAtom
        })
    where
        level :: NewNotation -> PrecedenceLevel
        level = fixityLevel . notaFixity

        nonfix, isinfix, isprefix, ispostfix :: NewNotation -> Bool
        nonfix    = (== NonfixNotation)  . notationKind . notation
        isinfix   = (== InfixNotation)   . notationKind . notation
        isprefix  = (== PrefixNotation)  . notationKind . notation
        ispostfix = (== PostfixNotation) . notationKind . notation

        isPrefix, isPostfix :: NotationSection -> Bool
        isPrefix  = (== PrefixNotation)  . sectKind
        isPostfix = (== PostfixNotation) . sectKind

        isInfix :: Associativity -> NotationSection -> Bool
        isInfix ass s =
          sectKind s == InfixNotation
             &&
          fixityAssoc (notaFixity (sectNotation s)) == ass

        mkP :: Either Integer Integer
               -- ^ Memoisation key.
            -> ParseSections
            -> Parser e e
            -> [NotationSection]
            -> Parser e e
               -- ^ A parser for an expression of higher precedence.
            -> Bool
               -- ^ Include the \"expression of higher precedence\"
               -- parser as one of the choices?
            -> Parser e e
        mkP key parseSections p0 ops higher includeHigher =
            memoise (NodeK key) $
              Fold.asum $
                (if includeHigher then (higher :) else id) $
                catMaybes [nonAssoc, preRights, postLefts]
            where
            choice :: forall k.
                      NK k -> [NotationSection] ->
                      Parser e (OperatorType k e)
            choice k =
              Fold.asum .
              map (\sect ->
                let n = sectNotation sect

                    inner :: forall k.
                             NK k -> Parser e (OperatorType k e)
                    inner = opP parseSections p0 n
                in
                case k of
                  In   -> inner In

                  Pre  -> if isinfix n || ispostfix n
                          then flip ($) <$> placeholder Beginning
                                        <*> inner In
                          else inner Pre

                  Post -> if isinfix n || isprefix n
                          then flip <$> inner In
                                    <*> placeholder End
                          else inner Post

                  Non  -> __IMPOSSIBLE__)

            nonAssoc :: Maybe (Parser e e)
            nonAssoc = case filter (isInfix NonAssoc) ops of
              []  -> Nothing
              ops -> Just $ do
                x <- NoPlaceholder <$> higher
                f <- choice In ops
                y <- NoPlaceholder <$> higher
                return (f x y)

            or p1 []   p2 []   = Nothing
            or p1 []   p2 ops2 = Just (p2 ops2)
            or p1 ops1 p2 []   = Just (p1 ops1)
            or p1 ops1 p2 ops2 = Just (p1 ops1 <|> p2 ops2)

            preRight :: Maybe (Parser e (MaybePlaceholder e -> e))
            preRight =
              or (choice Pre)
                 (filter isPrefix ops)
                 (\ops -> flip ($) <$> (NoPlaceholder <$> higher)
                                   <*> choice In ops)
                 (filter (isInfix RightAssoc) ops)

            preRights :: Maybe (Parser e e)
            preRights = do
              preRight <- preRight
              return $ Data.Function.fix $ \preRights ->
                preRight <*> (NoPlaceholder <$> (preRights <|> higher))

            postLeft :: Maybe (Parser e (MaybePlaceholder e -> e))
            postLeft =
              or (choice Post)
                 (filter isPostfix ops)
                 (\ops -> flip <$> choice In ops
                               <*> (NoPlaceholder <$> higher))
                 (filter (isInfix LeftAssoc) ops)

            postLefts :: Maybe (Parser e e)
            postLefts = do
              postLeft <- postLeft
              return $ Data.Function.fix $ \postLefts ->
                memoise (PostLeftsK key) $
                  flip ($) <$> (NoPlaceholder <$> (postLefts <|> higher))
                           <*> postLeft

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
parsePat ::
  (ParseSections, Parser Pattern Pattern) -> Pattern -> [Pattern]
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
    RecP r fs        -> RecP r <$> mapM (traverse (parsePat prs)) fs


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

-- | The returned list contains all operators/notations/sections that
-- were used to generate the grammar.

parseLHS' ::
  LHSOrPatSyn -> Maybe Name -> Pattern ->
  ScopeM (ParseLHS, [NotationSection])
parseLHS' lhsOrPatSyn top p = do
    let names = patternQNames p
        ms    = qualifierModules names
    flat <- flattenScope ms <$> getScope
    (parseSections, ops, parsers) <-
      buildParsers (getRange p) flat IsPattern names
    let patP = (parseSections, pTop parsers)
    let cons = getNames [ConName, PatternSynName] flat
    let flds = getNames [FldName] flat
    case [ res | let result = parsePat patP p
               , p' <- foldr seq () result `seq` result
               , res <- validPattern (PatternCheckConfig top cons flds) p' ] of
        [(p,lhs)] -> do reportSDoc "scope.operators" 50 $ return $
                          text "Parsed lhs:" <+> pretty lhs
                        return (lhs, ops)
        []        -> typeError $ OperatorChangeMessage
                               $ OperatorInformation ops
                               $ NoParseForLHS lhsOrPatSyn p
        rs        -> typeError $ OperatorChangeMessage
                               $ OperatorInformation ops
                               $ AmbiguousParseForLHS lhsOrPatSyn p $
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
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--      Assume _ * is a constructor. Then 'true *' can be parsed as either the
--      intended _* applied to true, or as true applied to a variable *. If we
--      check arities this problem won't appear.
parseLHS :: Name -> Pattern -> ScopeM LHSCore
parseLHS top p = billToParser $ do
  (res, ops) <- parseLHS' IsLHS (Just top) p
  case res of
    Right (f, lhs) -> return lhs
    _ -> typeError $ OperatorChangeMessage
                   $ OperatorInformation ops
                   $ NoParseForLHS IsLHS p

-- | Parses a pattern.
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--      Assume _ * is a constructor. Then 'true *' can be parsed as either the
--      intended _* applied to true, or as true applied to a variable *. If we
--      check arities this problem won't appear.
parsePattern :: Pattern -> ScopeM Pattern
parsePattern = parsePatternOrSyn IsLHS

parsePatternSyn :: Pattern -> ScopeM Pattern
parsePatternSyn = parsePatternOrSyn IsPatSyn

parsePatternOrSyn :: LHSOrPatSyn -> Pattern -> ScopeM Pattern
parsePatternOrSyn lhsOrPatSyn p = billToParser $ do
  (res, ops) <- parseLHS' lhsOrPatSyn Nothing p
  case res of
    Left p -> return p
    _      -> typeError $ OperatorChangeMessage
                        $ OperatorInformation ops
                        $ NoParseForLHS lhsOrPatSyn p

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
    let names = [ q | Ident q <- es ]
        ms    = qualifierModules names
    flat <- flattenScope ms <$> getScope
    (parseSections, ops, p) <- buildParsers (getRange es) flat IsExpr names

    -- Parse
    let result = parse (parseSections, pTop p) es
    case foldr seq () result `seq` result of
        [e] -> do
          reportSDoc "scope.operators" 50 $ return $
            text "Parsed an operator application:" <+> pretty e
          return e
        []  -> typeError $ OperatorChangeMessage
                         $ OperatorInformation ops
                         $ NoParseForApplication es
        es' -> typeError $ OperatorChangeMessage
                         $ OperatorInformation ops
                         $ AmbiguousParseForApplication es
                         $ map fullParen es'

parseModuleIdentifier :: Expr -> ScopeM QName
parseModuleIdentifier (Ident m) = return m
parseModuleIdentifier e = typeError $ NotAModuleExpr e

parseRawModuleApplication :: [Expr] -> ScopeM (QName, [NamedArg Expr])
parseRawModuleApplication es = billToParser $ do
    let e : es_args = es
    m <- parseModuleIdentifier e

    -- Build the arguments parser
    let names = [ q | Ident q <- es_args ]
        ms    = qualifierModules names
    flat <- flattenScope ms <$> getScope
    (parseSections, ops, p) <-
      buildParsers (getRange es_args) flat IsExpr names

    -- Parse
    -- TODO: not sure about forcing
    case {-force $-} parse (parseSections, pArgs p) es_args of
        [as] -> return (m, as)
        []   -> typeError $ OperatorChangeMessage
                          $ OperatorInformation ops
                          $ NoParseForApplication es
        ass -> do
          let f = fullParen . foldl (App noRange) (Ident m)
          typeError $ OperatorChangeMessage
                    $ OperatorInformation ops
                    $ AmbiguousParseForApplication es
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
    OpAppV x ns es -> par $ unExprView $ OpAppV x ns $ (map . fmap . fmap . fmap . fmap) fullParen' es
    LamV bs e -> par $ unExprView $ LamV bs (fullParen e)
    where
        par = unExprView . ParenV
