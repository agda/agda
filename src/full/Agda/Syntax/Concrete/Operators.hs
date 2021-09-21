{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

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

import Control.Applicative ( Alternative((<|>)))
import Control.Arrow (second)
import Control.Monad.Except (throwError)

import Data.Either (partitionEithers)
import qualified Data.Foldable as Fold
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Concrete hiding (appView)
import Agda.Syntax.Concrete.Operators.Parser
import Agda.Syntax.Concrete.Operators.Parser.Monad hiding (parse)
import Agda.Syntax.Concrete.Pattern
import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Position
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (typeError, TypeError(..), LHSOrPatSyn(..))
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.State (getScope)

import Agda.Utils.Either
import Agda.Utils.Pretty
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.List2 (List2, pattern List2)
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe
import Agda.Utils.Monad (guardWithError)
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Billing
---------------------------------------------------------------------------

-- | Bills the operator parser.

billToParser :: ExprKind -> ScopeM a -> ScopeM a
billToParser k = Bench.billTo
  [ Bench.Parsing
  , case k of
      IsExpr    -> Bench.OperatorsExpr
      IsPattern -> Bench.OperatorsPattern
  ]

---------------------------------------------------------------------------
-- * Building the parser
---------------------------------------------------------------------------

type FlatScope = Map QName [AbstractName]

-- | Compute all defined names in scope and their fixities/notations.
-- Note that overloaded names (constructors) can have several
-- fixities/notations. Then we 'mergeNotations'. (See issue 1194.)
getDefinedNames :: KindsOfNames -> FlatScope -> [[NewNotation]]
getDefinedNames kinds names =
  [ mergeNotations $ map (namesToNotation x . A.qnameName . anameName) ds
  | (x, ds) <- Map.toList names
  , any ((`elemKindsOfNames` kinds) . anameKind) ds
  , not (null ds)
  ]
  -- Andreas, 2013-03-21 see Issue 822
  -- Names can have different kinds, i.e., 'defined' and 'constructor'.
  -- We need to consider all names that have *any* matching kind,
  -- not only those whose first appearing kind is matching.

-- | Compute all names (first component) and operators/notations
-- (second component) in scope.
localNames :: FlatScope -> ScopeM ([QName], [NewNotation])
localNames flat = do
  let defs = getDefinedNames allKindsOfNames flat
  locals <- nubOn fst . notShadowedLocals <$> getLocalVars
  -- Note: Debug printout aligned with the one in buildParsers.
  reportS "scope.operators" 50
    [ "flat  = " ++ prettyShow flat
    , "defs  = " ++ prettyShow defs
    , "locals= " ++ prettyShow locals
    ]
  let localNots  = map localOp locals
      notLocal   = not . hasElem (map notaName localNots) . notaName
      otherNots  = concatMap (filter notLocal) defs
  return $ second (map useDefaultFixity) $ split $ localNots ++ otherNots
  where
    localOp (x, y) = namesToNotation (QName x) y
    split          = partitionEithers . concatMap opOrNot
    opOrNot n      = Left (notaName n) :
                     [Right n | not (null (notation n))]

-- | A data structure used internally by 'buildParsers'.
data InternalParsers e = InternalParsers
  { pTop    :: Parser e e
  , pApp    :: Parser e e
  , pArgs   :: Parser e [NamedArg e]
  , pNonfix :: Parser e e
  , pAtom   :: Parser e e
  }

-- | Expression kinds: Expressions or patterns.
data ExprKind = IsExpr | IsPattern
  deriving (Eq, Show)

-- | The data returned by 'buildParsers'.

data Parsers e = Parsers
  { parser :: [e] -> [e]
    -- ^ A parser for expressions or patterns (depending on the
    -- 'ExprKind' argument given to 'buildParsers').
  , argsParser :: [e] -> [[NamedArg e]]
    -- ^ A parser for sequences of arguments.
  , operators :: [NotationSection]
    -- ^ All operators/notations/sections that were used to generate
    -- the grammar.
  , flattenedScope :: FlatScope
    -- ^ A flattened scope that only contains those names that are
    -- unqualified or qualified by qualifiers that occur in the list
    -- of names given to 'buildParser'.
  }

-- | Builds parsers for operator applications from all the operators
-- and function symbols in scope.
--
-- When parsing a pattern we do not use bound names. The effect is
-- that unqualified operator parts (that are not constructor parts)
-- can be used as atomic names in the pattern (so they can be
-- rebound). See @test/succeed/OpBind.agda@ for an example.
--
-- When parsing a pattern we also disallow the use of sections, mainly
-- because there is little need for sections in patterns. Note that
-- sections are parsed by splitting up names into multiple tokens
-- (@_+_@ is replaced by @_@, @+@ and @_@), and if we were to support
-- sections in patterns, then we would have to accept certain such
-- sequences of tokens as single pattern variables.

buildParsers
  :: forall e. IsExpr e
  => ExprKind
     -- ^ Should expressions or patterns be parsed?
  -> [QName]
     -- ^ This list must include every name part in the
     -- expression/pattern to be parsed (excluding name parts inside
     -- things like parenthesised subexpressions that are treated as
     -- atoms). The list is used to optimise the parser. For
     -- instance, a given notation is only included in the generated
     -- grammar if all of the notation's name parts are present in
     -- the list of names.
  -> ScopeM (Parsers e)
buildParsers kind exprNames = do
    flat         <- flattenScope (qualifierModules exprNames) <$>
                      getScope
    (names, ops) <- localNames flat

    let -- All names.
        namesInExpr :: Set QName
        namesInExpr = Set.fromList exprNames

        partListsInExpr' = map (List1.toList . nameParts . unqualify) $
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
            HolePart{} : IdPart p : _ -> rangedThing p
            IdPart p : _              -> rangedThing p
            _                         -> __IMPOSSIBLE__

        -- Is the last identifier part present in n present in the
        -- expression, without any succeeding name parts, except for a
        -- trailing underscore iff withHole is True?
        lastPartPresent withHole n =
          Trie.member (addHole withHole p) reversedPartListsInExpr
          where
          p = case reverse n of
            HolePart{} : IdPart p : _ -> rangedThing p
            IdPart p : _              -> rangedThing p
            _                         -> __IMPOSSIBLE__

        -- Are the initial and final identifier parts present with
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

        (non, fix) = List.partition nonfix (filter (and . partsPresent) ops)

        cons       = getDefinedNames
                       (someKindsOfNames [ConName, CoConName, FldName, PatternSynName]) flat
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

        isAtom x
          | kind == IsPattern && not (isQualified x) =
            not (Set.member x conParts) || Set.member x conNames
          | otherwise =
            not (Set.member x allParts) || Set.member x allNames
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
        relatedOperators :: [(PrecedenceLevel, [NotationSection])]
        relatedOperators =
          map (\((l, ns) : rest) -> (l, ns ++ concatMap snd rest)) .
          List.groupBy ((==) `on` fst) .
          List.sortBy (compare `on` fst) .
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

    reportS "scope.operators" 50
      [ "unrelatedOperators = " ++ prettyShow unrelatedOperators
      , "nonWithSections    = " ++ prettyShow nonWithSections
      , "relatedOperators   = " ++ prettyShow relatedOperators
      ]

    let g = Data.Function.fix $ \p -> InternalParsers
              { pTop    = memoise TopK $
                          Fold.asum $
                            foldr (\(l, ns) higher ->
                                       mkP (Right l) parseSections
                                           (pTop p) ns higher True) (pApp p)
                                   relatedOperators :
                            zipWith (\ k n ->
                                    mkP (Left k) parseSections
                                        (pTop p) [n] (pApp p) False) [0..] unrelatedOperators
              , pApp    = memoise AppK $ appP (pNonfix p) (pArgs p)
              , pArgs   = argsP (pNonfix p)
              , pNonfix = memoise NonfixK $
                          Fold.asum $
                            pAtom p :
                            map (\sect ->
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
                                NoNotation     -> __IMPOSSIBLE__) nonWithSections
              , pAtom   = atomP isAtom
              }

    -- Andreas, 2020-06-03 #4712
    -- Note: needs Agda to be compiled with DEBUG to print the grammar.
    reportSDoc "scope.grammar" 10 $ return $
      "Operator grammar:" $$ nest 2 (grammar (pTop g))

    return $ Parsers
      { parser         = parse (parseSections, pTop  g)
      , argsParser     = parse (parseSections, pArgs g)
      , operators      = everything
      , flattenedScope = flat
      }
    where
        level :: NewNotation -> FixityLevel
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

        mkP :: PrecedenceKey  -- Memoisation key.
            -> ParseSections
            -> Parser e e
            -> [NotationSection]
            -> Parser e e  -- A parser for an expression of higher precedence.
            -> Bool  -- Include the \"expression of higher precedence\"
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
              ops -> Just $
                (\x f y -> f (noPlaceholder x) (noPlaceholder y))
                  <$> higher
                  <*> choice In ops
                  <*> higher

            or p1 []   p2 []   = Nothing
            or p1 []   p2 ops2 = Just (p2 ops2)
            or p1 ops1 p2 []   = Just (p1 ops1)
            or p1 ops1 p2 ops2 = Just (p1 ops1 <|> p2 ops2)

            preRight :: Maybe (Parser e (MaybePlaceholder e -> e))
            preRight =
              or (choice Pre)
                 (filter isPrefix ops)
                 (\ops -> flip ($) <$> (noPlaceholder <$> higher)
                                   <*> choice In ops)
                 (filter (isInfix RightAssoc) ops)

            preRights :: Maybe (Parser e e)
            preRights = do
              preRight <- preRight
              return $ Data.Function.fix $ \preRights ->
                memoiseIfPrinting (PreRightsK key) $
                  preRight <*> (noPlaceholder <$> (preRights <|> higher))

            postLeft :: Maybe (Parser e (MaybePlaceholder e -> e))
            postLeft =
              or (choice Post)
                 (filter isPostfix ops)
                 (\ops -> flip <$> choice In ops
                               <*> (noPlaceholder <$> higher))
                 (filter (isInfix LeftAssoc) ops)

            postLefts :: Maybe (Parser e e)
            postLefts = do
              postLeft <- postLeft
              return $ Data.Function.fix $ \postLefts ->
                memoise (PostLeftsK key) $
                  flip ($) <$> (noPlaceholder <$> (postLefts <|> higher))
                           <*> postLeft


---------------------------------------------------------------------------
-- * Parse functions
---------------------------------------------------------------------------

-- | Returns the list of possible parses.
parsePat
  :: ([Pattern] -> [Pattern]) -- ^ Turns a 'RawAppP' into possible parses.
  -> Pattern                  -- ^ Pattern possibly containing 'RawAppP's.
  -> [Pattern]                -- ^ Possible parses, not containing 'RawAppP's.
parsePat prs = \case
    AppP p (Arg info q) ->
        fullParen' <$> (AppP <$> parsePat prs p <*> (Arg info <$> traverse (parsePat prs) q))
    RawAppP _ ps     -> fullParen' <$> (parsePat prs =<< prs (List2.toList ps))
    OpAppP r d ns ps -> fullParen' . OpAppP r d ns <$> (mapM . traverse . traverse) (parsePat prs) ps
    HiddenP _ _      -> fail "bad hidden argument"
    InstanceP _ _    -> fail "bad instance argument"
    AsP r x p        -> AsP r x <$> parsePat prs p
    p@DotP{}         -> return p
    ParenP r p       -> fullParen' <$> parsePat prs p
    p@WildP{}        -> return p
    p@AbsurdP{}      -> return p
    p@LitP{}         -> return p
    p@QuoteP{}       -> return p
    p@IdentP{}       -> return p
    RecP r fs        -> RecP r <$> mapM (traverse (parsePat prs)) fs
    p@EqualP{}       -> return p -- Andrea: cargo culted from DotP
    EllipsisP r mp   -> caseMaybe mp (fail "bad ellipsis") $ \p ->
                          EllipsisP r . Just <$> parsePat prs p
    WithP r p        -> WithP r <$> parsePat prs p


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

-- | The result of 'parseLHS'.
data ParseLHS
  = ParsePattern Pattern    -- ^ We parsed a pattern.
  | ParseLHS QName LHSCore  -- ^ We parsed a lhs.

instance Pretty ParseLHS where
  pretty = \case
    ParsePattern p  -> pretty p
    ParseLHS _f lhs -> pretty lhs

-- | Parses a left-hand side, workhorse for 'parseLHS'.
--
parseLHS'
  :: LHSOrPatSyn
       -- ^ Are we trying to parse a lhs or a pattern synonym?
       --   For error reporting only!
  -> Maybe QName
       -- ^ Name of the function/patSyn definition if we parse a lhs.
       --   'Nothing' if we parse a pattern.
  -> Pattern
       -- ^ Thing to parse.
  -> ScopeM (ParseLHS, [NotationSection])
       -- ^ The returned list contains all operators/notations/sections that
       -- were used to generate the grammar.

parseLHS' IsLHS (Just qn) WildP{} =
    return (ParseLHS qn $ LHSHead qn [], [])

parseLHS' lhsOrPatSyn top p = do

    -- Build parser.
    patP <- buildParsers IsPattern (patternQNames p)

    -- Run parser, forcing result.
    let ps   = let result = parsePat (parser patP) p
               in  foldr seq () result `seq` result

    -- Classify parse results.
    let cons = getNames (someKindsOfNames [ConName, CoConName, PatternSynName])
                        (flattenedScope patP)
    let flds = getNames (someKindsOfNames [FldName])
                        (flattenedScope patP)
    let conf = PatternCheckConfig top (hasElem cons) (hasElem flds)

    let (errs, results) = partitionEithers $ map (validPattern conf) ps
    reportS "scope.operators" 60 $ vcat $
      [ "Possible parses for lhs:" ] ++ map (nest 2 . pretty . snd) results
    case results of
        -- Unique result.
        [(_,lhs)] -> do reportS "scope.operators" 50 $ "Parsed lhs:" <+> pretty lhs
                        return (lhs, operators patP)
        -- No result.
        []        -> typeError $ OperatorInformation (operators patP)
                               $ NoParseForLHS lhsOrPatSyn (catMaybes errs) p
        -- Ambiguous result.
        rs        -> typeError $ OperatorInformation (operators patP)
                               $ AmbiguousParseForLHS lhsOrPatSyn p $
                       map (fullParen . fst) rs
    where
        getNames kinds flat =
          map (notaName . head) $ getDefinedNames kinds flat

        -- The pattern is retained for error reporting in case of ambiguous parses.
        validPattern :: PatternCheckConfig -> Pattern -> PM (Pattern, ParseLHS)
        validPattern conf p = do
          res <- classifyPattern conf p
          case (res, top) of
            (ParsePattern{}, Nothing) -> return (p, res)  -- expect pattern
            (ParseLHS{}    , Just{} ) -> return (p, res)  -- expect lhs
            _ -> throwError Nothing

-- | Name sets for classifying a pattern.
data PatternCheckConfig = PatternCheckConfig
  { topName :: Maybe QName    -- ^ Name of defined symbol.
  , conName :: QName -> Bool  -- ^ Valid constructor name?
  , fldName :: QName -> Bool  -- ^ Valid field name?
  }

-- | The monad for pattern checking and classification.
--
--   The error message is either empty or a subpattern that was found to be invalid.
type PM = Either (Maybe Pattern)

-- | Returns zero or one classified patterns.
--   In case of zero, return the offending subpattern.
classifyPattern :: PatternCheckConfig -> Pattern -> PM ParseLHS
classifyPattern conf p =
  case patternAppView p of

    -- case @f ps@
    Arg _ (Named _ (IdentP x)) :| ps | Just x == topName conf -> do
      mapM_ (valid . namedArg) ps
      return $ ParseLHS x $ lhsCoreAddSpine (LHSHead x []) ps

    -- case @d ps@
    Arg _ (Named _ (IdentP x)) :| ps | fldName conf x -> do

      -- Step 1: check for valid copattern lhs.
      ps0 :: [NamedArg ParseLHS] <- mapM classPat ps
      let (ps1, rest) = span (isParsePattern . namedArg) ps0
      (p2, ps3) <- maybeToEither Nothing $ uncons rest
          -- when (null rest): no field pattern or def pattern found

      -- Ensure that the @ps3@ are patterns rather than lhss.
      mapM_ (guardWithError Nothing . isParsePattern . namedArg) ps3

      -- Step 2: construct the lhs.
      let (f, lhs0)     = fromParseLHS $ namedArg p2
          lhs           = setNamedArg p2 lhs0
          (ps', _:ps'') = splitAt (length ps1) ps
      return $ ParseLHS f $ lhsCoreAddSpine (LHSProj x ps' lhs []) ps''

    -- case @...@
    Arg _ (Named _ (EllipsisP r (Just p))) :| ps -> do
      classifyPattern conf p >>= \case  -- TODO: avoid re-parsing
        ParsePattern{}    -> throwError Nothing
        (ParseLHS f core) -> do
          mapM_ (valid . namedArg) ps
          let ellcore = LHSEllipsis r core
          return $ ParseLHS f $ lhsCoreAddSpine ellcore ps

    -- case: ordinary pattern
    _ -> ParsePattern p <$ valid p

  where
  valid = validConPattern $ conName conf

  classPat :: NamedArg Pattern -> PM (NamedArg ParseLHS)
  classPat = Trav.mapM (Trav.mapM (classifyPattern conf))

  isParsePattern = \case
    ParsePattern{} -> True
    ParseLHS{}     -> False

  fromParseLHS :: ParseLHS -> (QName, LHSCore)
  fromParseLHS = \case
    ParseLHS f lhs -> (f, lhs)
    ParsePattern{} -> __IMPOSSIBLE__


-- | Parses a left-hand side, and makes sure that it defined the expected name.
parseLHS :: QName -> Pattern -> ScopeM LHSCore
parseLHS top p = billToParser IsPattern $ do
  (res, ops) <- parseLHS' IsLHS (Just top) p
  case res of
    ParseLHS f lhs -> return lhs
    _ -> typeError $ OperatorInformation ops
                   $ NoParseForLHS IsLHS [] p

-- | Parses a pattern.
parsePattern :: Pattern -> ScopeM Pattern
parsePattern = parsePatternOrSyn IsLHS

parsePatternSyn :: Pattern -> ScopeM Pattern
parsePatternSyn = parsePatternOrSyn IsPatSyn

parsePatternOrSyn :: LHSOrPatSyn -> Pattern -> ScopeM Pattern
parsePatternOrSyn lhsOrPatSyn p = billToParser IsPattern $ do
  (res, ops) <- parseLHS' lhsOrPatSyn Nothing p
  case res of
    ParsePattern p -> return p
    _ -> typeError $ OperatorInformation ops
                   $ NoParseForLHS lhsOrPatSyn [] p

-- | Helper function for 'parseLHS' and 'parsePattern'.
--
--   Returns a subpattern that is not a valid constructor pattern
--   or nothing if the whole pattern is a valid constructor pattern.
validConPattern
  :: (QName -> Bool)     -- ^ Test for constructor name.
  -> Pattern             -- ^ Supposedly a constructor pattern.
  -> PM ()   -- ^ Offending subpattern or nothing.
validConPattern cons = loop
  where
  loop p = case appView p of
      WithP _ p :| [] -> loop p
      _ :| []         -> ok
      IdentP x :| ps
        | cons x      -> mapM_ loop ps
        | otherwise   -> failure
      QuoteP _ :| [_] -> ok
      DotP _ e :| ps  -> mapM_ loop ps
      _               -> failure
    where
    ok      = return ()
    failure = throwError $ Just p


-- | Helper function for 'parseLHS' and 'parsePattern'.
appView :: Pattern -> List1 Pattern
appView = loop []
  where
  loop acc = \case
    AppP p a         -> loop (namedArg a : acc) p
    OpAppP _ op _ ps -> (IdentP op :| fmap namedArg ps)
                          `List1.append`
                        reverse acc
    ParenP _ p       -> loop acc p
    RawAppP _ _      -> __IMPOSSIBLE__
    HiddenP _ _      -> __IMPOSSIBLE__
    InstanceP _ _    -> __IMPOSSIBLE__
    p@IdentP{}       -> ret p
    p@WildP{}        -> ret p
    p@AsP{}          -> ret p
    p@AbsurdP{}      -> ret p
    p@LitP{}         -> ret p
    p@QuoteP{}       -> ret p
    p@DotP{}         -> ret p
    p@RecP{}         -> ret p
    p@EqualP{}       -> ret p
    p@EllipsisP{}    -> ret p
    p@WithP{}        -> ret p
   where
   ret p = p :| reverse acc

-- | Return all qualifiers occuring in a list of 'QName's.
--   Each qualifier is returned as a list of names, e.g.
--   for @Data.Nat._+_@ we return the list @[Data,Nat]@.
qualifierModules :: [QName] -> [[Name]]
qualifierModules qs =
  nubOn id $ filter (not . null) $ map (List1.init . qnameParts) qs

-- | Parse a list of expressions (typically from a 'RawApp') into an application.
parseApplication :: List2 Expr -> ScopeM Expr
parseApplication es  = billToParser IsExpr $ do
    let es0 = List2.toList es
    -- Build the parser
    p <- buildParsers IsExpr [ q | Ident q <- es0 ]

    -- Parse
    let result = parser p es0
    case foldr seq () result `seq` result of
      [e]   -> do
          reportSDoc "scope.operators" 50 $ return $
            "Parsed an operator application:" <+> pretty e
          return e
      []    -> typeError $ OperatorInformation (operators p)
                         $ NoParseForApplication es
      e:es' -> typeError $ OperatorInformation (operators p)
                         $ AmbiguousParseForApplication es
                         $ fmap fullParen (e :| es')

parseModuleIdentifier :: Expr -> ScopeM QName
parseModuleIdentifier (Ident m) = return m
parseModuleIdentifier e = typeError $ NotAModuleExpr e

parseRawModuleApplication :: List2 Expr -> ScopeM (QName, [NamedArg Expr])
parseRawModuleApplication es@(List2 e e2 rest) = billToParser IsExpr $ do
    let es_args = e2:rest
    m <- parseModuleIdentifier e

    -- Build the arguments parser
    p <- buildParsers IsExpr [ q | Ident q <- es_args ]

    -- Parse
    -- TODO: not sure about forcing
    case {-force $-} argsParser p es_args of
        [as] -> return (m, as)
        []   -> typeError $ OperatorInformation (operators p)
                          $ NoParseForApplication es
        as : ass -> do
          let f = fullParen . foldl (App noRange) (Ident m)
          typeError $ OperatorInformation (operators p)
                    $ AmbiguousParseForApplication es
                    $ fmap f (as :| ass)

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
    AppV e1 (Arg info e2) -> par $ unExprView $ AppV (fullParen' e1) (Arg info e2')
        where
            e2' = case argInfoHiding info of
                Hidden     -> e2
                Instance{} -> e2
                NotHidden  -> fullParen' <$> e2
    OpAppV x ns es -> par $ unExprView $ OpAppV x ns $ (fmap . fmap . fmap . fmap . fmap) fullParen' es
    LamV bs e -> par $ unExprView $ LamV bs (fullParen e)
    where
        par = unExprView . ParenV
