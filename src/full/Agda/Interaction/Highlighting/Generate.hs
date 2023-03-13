
-- | Generates data used for precise syntax highlighting.

-- {-# OPTIONS_GHC -fwarn-unused-imports #-}  -- Semigroup import obsolete in later ghcs
-- {-# OPTIONS_GHC -fwarn-unused-binds   #-}

module Agda.Interaction.Highlighting.Generate
  ( Level(..)
  , generateAndPrintSyntaxInfo
  , generateTokenInfo, generateTokenInfoFromSource
  , generateTokenInfoFromString
  , printSyntaxInfo
  , printErrorInfo, errorHighlighting
  , printUnsolvedInfo
  , printHighlightingInfo
  , highlightAsTypeChecked
  , highlightWarning, warningHighlighting
  , computeUnsolvedInfo
  , storeDisambiguatedConstructor, storeDisambiguatedProjection
  , disambiguateRecordFields
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Arrow (second)

import qualified Data.Foldable as Fold
import qualified Data.Map as Map
import Data.Maybe
import Data.List ((\\))
import qualified Data.List as List
import qualified Data.IntMap as IntMap
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.Semigroup (Semigroup(..))
import Data.Sequence (Seq)
import qualified Data.Set as Set
import qualified Data.Text.Lazy as Text

import Agda.Interaction.Response
  ( RemoveTokenBasedHighlighting( KeepHighlighting ) )
import Agda.Interaction.Highlighting.Precise as H
import Agda.Interaction.Highlighting.Range
  (rToR, rangeToRange, overlappings, Ranges)
import Agda.Interaction.Highlighting.FromAbstract

import qualified Agda.TypeChecking.Errors as TCM
import Agda.TypeChecking.MetaVars (isBlockedTerm, hasTwinMeta)
import Agda.TypeChecking.Monad
  hiding (ModuleInfo, MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad  as TCM
import qualified Agda.TypeChecking.Pretty as TCM
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Warnings ( raiseWarningsOnUsage, runPM )

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete.Definitions as W ( DeclarationWarning(..), DeclarationWarning'(..) )
import Agda.Syntax.Common (pattern Ranged)
import qualified Agda.Syntax.Common as Common
import qualified Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as L
import qualified Agda.Syntax.Parser as Pa
import qualified Agda.Syntax.Parser.Tokens as T
import qualified Agda.Syntax.Position as P
import Agda.Syntax.Position
  (RangeFile, Range, HasRange, getRange, noRange)
import Agda.Syntax.TopLevelModuleName

import Agda.Syntax.Scope.Base     ( WithKind(..) )
import Agda.Syntax.Abstract.Views ( KName, declaredNames )

import Agda.Utils.FileName
import Agda.Utils.List            ( caseList, initWithDefault, last1 )
import Agda.Utils.List2           ( List2 )
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Singleton

import Agda.Utils.Impossible

-- | Highlighting levels.

data Level
  = Full
    -- ^ Full highlighting. Should only be used after typechecking has
    --   completed successfully.
  | Partial
    -- ^ Highlighting without disambiguation of overloaded
    --   constructors.

-- | Highlight a warning.
--   We do not generate highlighting for unsolved metas and
--   constraints, as that gets handled in bulk after typechecking.
highlightWarning :: TCWarning -> TCM ()
highlightWarning tcwarn = do
  let h = convert $ warningHighlighting' False tcwarn
  -- Highlighting for warnings coming from the Happy parser is placed
  -- together with token highlighting.
  case tcWarning tcwarn of
    ParseWarning{} -> modifyTCLens stTokens     (h <>)
    _              -> modifyTCLens stSyntaxInfo (h <>)
  ifTopLevelAndHighlightingLevelIs NonInteractive $
    printHighlightingInfo KeepHighlighting h

-- | Generate syntax highlighting information for the given
-- declaration, and (if appropriate) print it. If the boolean is
-- 'True', then the state is additionally updated with the new
-- highlighting info (in case of a conflict new info takes precedence
-- over old info).
--
-- The procedure makes use of some of the highlighting info
-- corresponding to 'stTokens' (that corresponding to the interval
-- covered by the declaration). If the boolean is 'True', then this
-- highlighting info is additionally removed from the data structure
-- that 'stTokens' refers to.

generateAndPrintSyntaxInfo
  :: A.Declaration
       -- ^ Declaration to highlight.
  -> Level
       -- ^ Amount of highlighting.
  -> Bool
       -- ^ Update the state?
  -> TCM ()
generateAndPrintSyntaxInfo decl _ _ | null $ getRange decl = return ()
generateAndPrintSyntaxInfo decl hlLevel updateState = do
  top <- fromMaybe __IMPOSSIBLE__ <$> currentTopLevelModule

  reportSDoc "import.iface.create" 15 $
    TCM.fwords
      ("Generating syntax info for the following declaration " ++
       case hlLevel of
         Full   {} -> "(final):"
         Partial{} -> "(first approximation):")
      TCM.$$
    TCM.prettyA decl

  ignoreAbstractMode $ do
    kinds <- nameKinds hlLevel decl

    -- After the code has been type checked more information may be
    -- available for overloaded constructors, and
    -- @generateConstructorInfo@ takes advantage of this information.
    -- Note, however, that highlighting for overloaded constructors is
    -- included also in @nameInfo@.
    constructorInfo <- case hlLevel of
      Full{} -> generateConstructorInfo top kinds decl
      _      -> return mempty

    -- Main source of scope-checker generated highlighting:
    let nameInfo = runHighlighter top kinds decl

    reportSDoc "highlighting.warning" 60 $ TCM.hcat
      [ "current path = "
      , Strict.maybe "(nothing)" (return . pretty) =<< do
          P.rangeFile <$> viewTC eRange
      ]

    -- Highlighting from the lexer and Happy parser:
    (curTokens, otherTokens) <-
      insideAndOutside (rangeToRange (getRange decl)) <$> useTC stTokens

    -- @constructorInfo@ needs
    -- to be placed before @nameInfo@ since, when typechecking is done,
    -- constructors are included in both lists. Finally the token
    -- information is placed last since token highlighting is more
    -- crude than the others.
    let syntaxInfo = convert (constructorInfo <> nameInfo)
                       <>
                     curTokens

    when updateState $ do
      stSyntaxInfo `modifyTCLens` mappend syntaxInfo
      stTokens     `setTCLens`    otherTokens

    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo KeepHighlighting syntaxInfo

-- | Generate and return the syntax highlighting information for the
-- tokens in the given file.

generateTokenInfo :: AbsolutePath -> TCM HighlightingInfo
generateTokenInfo file =
  generateTokenInfoFromSource rf . Text.unpack =<<
    runPM (Pa.readFilePM rf)
  where
  -- Note the use of Nothing here. The file might not even parse, but
  -- it should still be possible to obtain token-based highlighting
  -- information. The top-level module names seem to be *mostly*
  -- unused, but one cannot use __IMPOSSIBLE__ instead of Nothing,
  -- because the top-level module names are used by interleaveRanges,
  -- which is used by parseLiterateWithComments, which is used by
  -- generateTokenInfoFromSource.
  rf = P.mkRangeFile file Nothing

-- | Generate and return the syntax highlighting information for the
-- tokens in the given file.

generateTokenInfoFromSource
  :: RangeFile
     -- ^ The module to highlight.
  -> String
     -- ^ The file contents. Note that the file is /not/ read from
     -- disk.
  -> TCM HighlightingInfo
generateTokenInfoFromSource file input =
  runPM $ tokenHighlighting . fst . fst <$>
          Pa.parseFile Pa.tokensParser file input

-- | Generate and return the syntax highlighting information for the
-- tokens in the given string, which is assumed to correspond to the
-- given range.

generateTokenInfoFromString :: Range -> String -> TCM HighlightingInfo
generateTokenInfoFromString r _ | r == noRange = return mempty
generateTokenInfoFromString r s = do
  runPM $ tokenHighlighting . fst <$>
          Pa.parsePosString Pa.tokensParser p s
  where
    Just p = P.rStart r

-- | Compute syntax highlighting for the given tokens.
tokenHighlighting :: [T.Token] -> HighlightingInfo
tokenHighlighting = convert . mconcat . map tokenToHI
  where
  -- Converts an aspect and a range to a file.
  aToF a r = H.singleton (rToR r) (mempty { aspect = Just a })

  tokenToHI :: T.Token -> HighlightingInfoBuilder
  tokenToHI (T.TokKeyword T.KwForall i)  = aToF Symbol (getRange i)
  tokenToHI (T.TokKeyword T.KwREWRITE _) = mempty  -- #4361, REWRITE is not always a Keyword
  tokenToHI (T.TokKeyword _ i)           = aToF Keyword (getRange i)
  tokenToHI (T.TokSymbol T.SymQuestionMark i) = aToF Hole (getRange i)
  tokenToHI (T.TokSymbol  _ i)                = aToF Symbol (getRange i)
  tokenToHI (T.TokLiteral (Ranged r (L.LitNat    _))) = aToF Number r
  tokenToHI (T.TokLiteral (Ranged r (L.LitWord64 _))) = aToF Number r
  tokenToHI (T.TokLiteral (Ranged r (L.LitFloat  _))) = aToF Number r
  tokenToHI (T.TokLiteral (Ranged r (L.LitString _))) = aToF String r
  tokenToHI (T.TokLiteral (Ranged r (L.LitChar   _))) = aToF String r
  tokenToHI (T.TokLiteral (Ranged r (L.LitQName  _))) = aToF String r
  tokenToHI (T.TokLiteral (Ranged r (L.LitMeta _ _))) = aToF String r
  tokenToHI (T.TokComment (i, _))            = aToF Comment (getRange i)
  tokenToHI (T.TokTeX (i, _))                = aToF Background (getRange i)
  tokenToHI (T.TokMarkup (i, _))             = aToF Markup (getRange i)
  tokenToHI (T.TokId {})                     = mempty
  tokenToHI (T.TokQId {})                    = mempty
  tokenToHI (T.TokString (i,s))              = aToF Pragma (getRange i)
  tokenToHI (T.TokDummy {})                  = mempty
  tokenToHI (T.TokEOF {})                    = mempty

-- | Builds a 'NameKinds' function.

nameKinds :: Level
             -- ^ This should only be @'Full'@ if
             -- type-checking completed successfully (without any
             -- errors).
          -> A.Declaration
          -> TCM NameKinds
nameKinds hlLevel decl = do
  imported <- useTC $ stImports . sigDefinitions
  local    <- case hlLevel of
    Full{} -> useTC $ stSignature . sigDefinitions
    _      -> return HMap.empty
  impPatSyns <- useTC stPatternSynImports
  locPatSyns <- case hlLevel of
    Full{} -> useTC stPatternSyns
    _      -> return empty
      -- Traverses the syntax tree and constructs a map from qualified
      -- names to name kinds. TODO: Handle open public.
  let syntax :: NameKindMap
      syntax = runBuilder (declaredNames decl :: NameKindBuilder) HMap.empty
  return $ \ n -> unionsMaybeWith mergeNameKind
    [ defnToKind . theDef <$> HMap.lookup n local
    , con <$ Map.lookup n locPatSyns
    , defnToKind . theDef <$> HMap.lookup n imported
    , con <$ Map.lookup n impPatSyns
    , HMap.lookup n syntax
    ]
  where
  defnToKind :: TCM.Defn -> NameKind
  defnToKind   TCM.Axiom{}                           = Postulate
  defnToKind   TCM.DataOrRecSig{}                    = Postulate
  defnToKind   TCM.GeneralizableVar{}                = Generalizable
  defnToKind d@TCM.Function{} | isProperProjection d = Field
                            | otherwise            = Function
  defnToKind   TCM.Datatype{}                        = Datatype
  defnToKind   TCM.Record{}                          = Record
  defnToKind   TCM.Constructor{ TCM.conInd = i }       = Constructor i
  defnToKind   TCM.Primitive{}                       = Primitive
  defnToKind   TCM.PrimitiveSort{}                   = Primitive
  defnToKind   TCM.AbstractDefn{}                    = __IMPOSSIBLE__

  con :: NameKind
  con = Constructor Common.Inductive

-- | The 'TCM.Axiom' constructor is used to represent various things
-- which are not really axioms, so when maps are merged 'Postulate's
-- are thrown away whenever possible. The 'declaredNames' function
-- below can return several explanations for one qualified name; the
-- 'Postulate's are bogus.
mergeNameKind :: NameKind -> NameKind -> NameKind
mergeNameKind Postulate k = k
mergeNameKind _     Macro = Macro  -- If the abstract syntax says macro, it's a macro.
mergeNameKind k         _ = k

-- Auxiliary types for @nameKinds@ generation

type NameKindMap     = HashMap A.QName NameKind
data NameKindBuilder = NameKindBuilder
  { runBuilder :: NameKindMap -> NameKindMap
  }

instance Semigroup (NameKindBuilder) where
  NameKindBuilder f <> NameKindBuilder g = NameKindBuilder $ f . g

instance Monoid (NameKindBuilder) where
  mempty = NameKindBuilder id
  mappend = (<>)

instance Singleton KName NameKindBuilder where
  singleton (WithKind k q) = NameKindBuilder $
    HMap.insertWith mergeNameKind q $ kindOfNameToNameKind k

instance Collection KName NameKindBuilder

-- | Generates syntax highlighting information for all constructors
-- occurring in patterns and expressions in the given declaration.
--
-- This function should only be called after type checking.
-- Constructors can be overloaded, and the overloading is resolved by
-- the type checker.

generateConstructorInfo
  :: TopLevelModuleName
     -- ^ The module to highlight.
  -> NameKinds
  -> A.Declaration
  -> TCM HighlightingInfoBuilder
generateConstructorInfo top kinds decl = do

  -- Get boundaries of current declaration.
  -- @noRange@ should be impossible, but in case of @noRange@
  -- it makes sense to return mempty.
  caseList (P.rangeIntervals $ getRange decl)
           (return mempty) $ \ i is -> do
    let start = fromIntegral $ P.posPos $ P.iStart i
        end   = fromIntegral $ P.posPos $ P.iEnd $ last1 i is

    -- Get all disambiguated names that fall within the range of decl.
    m0 <- useTC stDisambiguatedNames
    let (_, m1) = IntMap.split (pred start) m0
        (m2, _) = IntMap.split end m1
        constrs = IntMap.elems m2

    -- Return suitable syntax highlighting information.
    return $ foldMap (runHighlighter top kinds) constrs

printSyntaxInfo :: Range -> TCM ()
printSyntaxInfo r = do
  syntaxInfo <- useTC stSyntaxInfo
  ifTopLevelAndHighlightingLevelIs NonInteractive $
    printHighlightingInfo KeepHighlighting
      (restrictTo (rangeToRange r) syntaxInfo)

-- | Prints syntax highlighting info for an error.

printErrorInfo :: TCErr -> TCM ()
printErrorInfo e =
  printHighlightingInfo KeepHighlighting . convert =<<
    errorHighlighting e

-- | Generate highlighting for error.

errorHighlighting :: TCErr -> TCM HighlightingInfoBuilder
errorHighlighting e = errorHighlighting' (getRange e) <$> TCM.prettyError e

errorHighlighting'
  :: Range     -- ^ Error range.
  -> String    -- ^ Error message for tooltip.
  -> HighlightingInfoBuilder
errorHighlighting' r s = mconcat
  [ -- Erase previous highlighting.
    H.singleton (rToR $ P.continuousPerLine r) mempty
  , -- Print new highlighting.
    H.singleton (rToR r)
         $ parserBased { otherAspects = Set.singleton Error
                       , note         = s
                       }
  ]

-- | Highlighting for warnings that are considered fatal.

errorWarningHighlighting :: HasRange a => a -> HighlightingInfoBuilder
errorWarningHighlighting w =
  H.singleton (rToR $ P.continuousPerLine $ getRange w) $
    parserBased { otherAspects = Set.singleton ErrorWarning }
-- errorWarningHighlighting w = errorHighlighting' (getRange w) ""
  -- MonadPretty not available here, so, no tooltip.
  -- errorHighlighting' (getRange w) . render <$> TCM.prettyWarning (tcWarning w)

-- | Generate syntax highlighting for warnings.

warningHighlighting :: TCWarning -> HighlightingInfoBuilder
warningHighlighting = warningHighlighting' True

warningHighlighting' :: Bool -- ^ should we generate highlighting for unsolved metas and constrains?
                     -> TCWarning -> HighlightingInfoBuilder
warningHighlighting' b w = case tcWarning w of
  TerminationIssue terrs     -> terminationErrorHighlighting terrs
  NotStrictlyPositive d ocs  -> positivityErrorHighlighting d ocs
  -- #3965 highlight each unreachable clause independently: they
  -- may be interleaved with actually reachable clauses!
  UnreachableClauses _ rs    -> foldMap deadcodeHighlighting rs
  CoverageIssue{}            -> coverageErrorHighlighting $ getRange w
  CoverageNoExactSplit{}     -> catchallHighlighting $ getRange w
  UnsolvedConstraints cs     -> if b then constraintsHighlighting [] cs else mempty
  UnsolvedMetaVariables rs   -> if b then metasHighlighting rs          else mempty
  AbsurdPatternRequiresNoRHS{} -> deadcodeHighlighting w
  ModuleDoesntExport{}         -> deadcodeHighlighting w
  DuplicateUsing xs            -> foldMap deadcodeHighlighting xs
  FixityInRenamingModule rs    -> foldMap deadcodeHighlighting rs
  -- expanded catch-all case to get a warning for new constructors
  CantGeneralizeOverSorts{}  -> mempty
  UnsolvedInteractionMetas{} -> mempty
  InteractionMetaBoundaries{} -> mempty
  OldBuiltin{}               -> mempty
  EmptyRewritePragma{}       -> deadcodeHighlighting w
  EmptyWhere{}               -> deadcodeHighlighting w
  IllformedAsClause{}        -> deadcodeHighlighting w
  UselessPublic{}            -> deadcodeHighlighting w
  UselessHiding xs           -> foldMap deadcodeHighlighting xs
  UselessInline{}            -> mempty
  UselessPatternDeclarationForRecord{} -> deadcodeHighlighting w
  ClashesViaRenaming _ xs    -> foldMap deadcodeHighlighting xs
    -- #4154, TODO: clashing renamings are not dead code, but introduce problems.
    -- Should we have a different color?
  WrongInstanceDeclaration{} -> mempty
  InstanceWithExplicitArg{}  -> deadcodeHighlighting w
  InstanceNoOutputTypeName{} -> mempty
  InstanceArgWithExplicitArg{} -> mempty
  InversionDepthReached{}    -> mempty
  NoGuardednessFlag{}        -> mempty
  GenericWarning{}           -> mempty
  GenericUseless r _         -> deadcodeHighlighting r
  -- Andreas, 2020-03-21, issue #4456:
  -- Error warnings that do not have dedicated highlighting
  -- are highlighted as errors.
  GenericNonFatalError{}                -> errorWarningHighlighting w
  SafeFlagPostulate{}                   -> errorWarningHighlighting w
  SafeFlagPragma{}                      -> errorWarningHighlighting w
  SafeFlagNonTerminating                -> errorWarningHighlighting w
  SafeFlagTerminating                   -> errorWarningHighlighting w
  SafeFlagWithoutKFlagPrimEraseEquality -> errorWarningHighlighting w
  SafeFlagEta                           -> errorWarningHighlighting w
  SafeFlagInjective                     -> errorWarningHighlighting w
  SafeFlagNoCoverageCheck               -> errorWarningHighlighting w
  SafeFlagNoPositivityCheck             -> errorWarningHighlighting w
  SafeFlagPolarity                      -> errorWarningHighlighting w
  SafeFlagNoUniverseCheck               -> errorWarningHighlighting w
  InfectiveImport{}                     -> errorWarningHighlighting w
  CoInfectiveImport{}                   -> errorWarningHighlighting w
  WithoutKFlagPrimEraseEquality -> mempty
  DeprecationWarning{}       -> mempty
  UserWarning{}              -> mempty
  LibraryWarning{}           -> mempty
  RewriteNonConfluent{}      -> confluenceErrorHighlighting w
  RewriteMaybeNonConfluent{} -> confluenceErrorHighlighting w
  RewriteAmbiguousRules{}    -> confluenceErrorHighlighting w
  RewriteMissingRule{}       -> confluenceErrorHighlighting w
  PragmaCompileErased{}      -> deadcodeHighlighting w
  NotInScopeW{}              -> deadcodeHighlighting w
  UnsupportedIndexedMatch{}  -> mempty
  AsPatternShadowsConstructorOrPatternSynonym{}
                             -> deadcodeHighlighting w
  PlentyInHardCompileTimeMode o
                             -> deadcodeHighlighting o
  RecordFieldWarning w       -> recordFieldWarningHighlighting w
  OptionWarning w            -> mempty
  ParseWarning w             -> case w of
    Pa.UnsupportedAttribute{}     -> deadcodeHighlighting w
    Pa.MultipleAttributes{}       -> deadcodeHighlighting w
    Pa.OverlappingTokensWarning{} -> mempty
  NicifierIssue (DeclarationWarning _ w) -> case w of
    -- we intentionally override the binding of `w` here so that our pattern of
    -- using `getRange w` still yields the most precise range information we
    -- can get.
    NotAllowedInMutual{}             -> deadcodeHighlighting w
    EmptyAbstract{}                  -> deadcodeHighlighting w
    EmptyConstructor{}               -> deadcodeHighlighting w
    EmptyInstance{}                  -> deadcodeHighlighting w
    EmptyMacro{}                     -> deadcodeHighlighting w
    EmptyMutual{}                    -> deadcodeHighlighting w
    EmptyPostulate{}                 -> deadcodeHighlighting w
    EmptyPrimitive{}                 -> deadcodeHighlighting w
    EmptyPrivate{}                   -> deadcodeHighlighting w
    EmptyGeneralize{}                -> deadcodeHighlighting w
    EmptyField{}                     -> deadcodeHighlighting w
    HiddenGeneralize{}               -> mempty
      -- Andreas, 2022-03-25, issue #5850
      -- We would like @deadcodeHighlighting w@ for the braces in
      -- @variable {x} : A@, but these have no range, so we cannot highlight them.
      -- Highlighting the variable instead might be misleading,
      -- suggesting that it is not generalized over.
    UselessAbstract{}                -> deadcodeHighlighting w
    UselessInstance{}                -> deadcodeHighlighting w
    UselessPrivate{}                 -> deadcodeHighlighting w
    InvalidNoPositivityCheckPragma{} -> deadcodeHighlighting w
    InvalidNoUniverseCheckPragma{}   -> deadcodeHighlighting w
    InvalidTerminationCheckPragma{}  -> deadcodeHighlighting w
    InvalidCoverageCheckPragma{}     -> deadcodeHighlighting w
    InvalidConstructor{}             -> deadcodeHighlighting w
    InvalidConstructorBlock{}        -> deadcodeHighlighting w
    InvalidRecordDirective{}         -> deadcodeHighlighting w
    OpenPublicAbstract{}             -> deadcodeHighlighting w
    OpenPublicPrivate{}              -> deadcodeHighlighting w
    W.ShadowingInTelescope nrs       -> foldMap
                                          (shadowingTelHighlighting . snd)
                                          nrs
    MissingDeclarations{}            -> missingDefinitionHighlighting w
    MissingDefinitions{}             -> missingDefinitionHighlighting w
    -- TODO: explore highlighting opportunities here!
    InvalidCatchallPragma{}           -> mempty
    PolarityPragmasButNotPostulates{} -> mempty
    PragmaNoTerminationCheck{}        -> mempty
    PragmaCompiled{}                  -> errorWarningHighlighting w
    UnknownFixityInMixfixDecl{}       -> mempty
    UnknownNamesInFixityDecl{}        -> mempty
    UnknownNamesInPolarityPragmas{}   -> mempty

recordFieldWarningHighlighting ::
  RecordFieldWarning -> HighlightingInfoBuilder
recordFieldWarningHighlighting = \case
  DuplicateFieldsWarning xrs      -> dead xrs
  TooManyFieldsWarning _q _ys xrs -> dead xrs
  where
  dead :: [(C.Name, Range)] -> HighlightingInfoBuilder
  dead = mconcat . map deadcodeHighlighting
  -- Andreas, 2020-03-27 #3684: This variant seems to only highlight @x@:
  -- dead = mconcat . map f
  -- f (x, r) = deadcodeHighlighting (getRange x) `mappend` deadcodeHighlighting r

-- | Generate syntax highlighting for termination errors.

terminationErrorHighlighting ::
  [TerminationError] -> HighlightingInfoBuilder
terminationErrorHighlighting termErrs = functionDefs `mappend` callSites
  where
    m            = parserBased { otherAspects = Set.singleton TerminationProblem }
    functionDefs = foldMap (\x -> H.singleton (rToR $ bindingSite x) m) $
                   concatMap termErrFunctions termErrs
    callSites    = foldMap (\r -> H.singleton (rToR r) m) $
                   concatMap (map getRange . termErrCalls) termErrs
    bindingSite  = A.nameBindingSite . A.qnameName

-- | Generate syntax highlighting for not-strictly-positive inductive
-- definitions.

positivityErrorHighlighting ::
  I.QName -> Seq OccursWhere -> HighlightingInfoBuilder
positivityErrorHighlighting q os =
  several (rToR <$> getRange q : rs) m
  where
    rs = map (\(OccursWhere r _ _) -> r) (Fold.toList os)
    m  = parserBased { otherAspects = Set.singleton PositivityProblem }

deadcodeHighlighting :: HasRange a => a -> HighlightingInfoBuilder
deadcodeHighlighting a = H.singleton (rToR $ P.continuous $ getRange a) m
  where m = parserBased { otherAspects = Set.singleton Deadcode }

coverageErrorHighlighting :: Range -> HighlightingInfoBuilder
coverageErrorHighlighting r = H.singleton (rToR $ P.continuousPerLine r) m
  where m = parserBased { otherAspects = Set.singleton CoverageProblem }

shadowingTelHighlighting :: List2 Range -> HighlightingInfoBuilder
shadowingTelHighlighting =
  -- we do not want to highlight the one variable in scope so we take
  -- the @init@ segment of the ranges in question
  foldMap (\r -> H.singleton (rToR $ P.continuous r) m) . List2.init
  where
  m = parserBased { otherAspects =
                      Set.singleton H.ShadowingInTelescope }

catchallHighlighting :: Range -> HighlightingInfoBuilder
catchallHighlighting r = H.singleton (rToR $ P.continuousPerLine r) m
  where m = parserBased { otherAspects = Set.singleton CatchallClause }

confluenceErrorHighlighting ::
  HasRange a => a -> HighlightingInfoBuilder
confluenceErrorHighlighting a = H.singleton (rToR $ P.continuousPerLine $ getRange a) m
  where m = parserBased { otherAspects = Set.singleton ConfluenceProblem }

missingDefinitionHighlighting ::
  HasRange a => a -> HighlightingInfoBuilder
missingDefinitionHighlighting a = H.singleton (rToR $ P.continuousPerLine $ getRange a) m
  where m = parserBased { otherAspects = Set.singleton MissingDefinition }

-- | Generates and prints syntax highlighting information for unsolved
-- meta-variables and certain unsolved constraints.

printUnsolvedInfo :: TCM ()
printUnsolvedInfo = do
  info <- computeUnsolvedInfo

  printHighlightingInfo KeepHighlighting (convert info)

computeUnsolvedInfo :: TCM HighlightingInfoBuilder
computeUnsolvedInfo = do
  (rs, metaInfo) <- computeUnsolvedMetaWarnings
  constraintInfo <- computeUnsolvedConstraints rs

  return $ metaInfo `mappend` constraintInfo

-- | Generates syntax highlighting information for unsolved meta
-- variables.
--   Also returns ranges of unsolved or interaction metas.
computeUnsolvedMetaWarnings :: TCM ([Ranges], HighlightingInfoBuilder)
computeUnsolvedMetaWarnings = do
  is <- getInteractionMetas

  -- We don't want to highlight blocked terms, since
  --   * there is always at least one proper meta responsible for the blocking
  --   * in many cases the blocked term covers the highlighting for this meta
  --   * for the same reason we skip metas with a twin, since the twin will be blocked.
  let notBlocked m = not <$> isBlockedTerm m
  let notHasTwin m = not <$> hasTwinMeta m
  ms <- filterM notHasTwin =<< filterM notBlocked =<< getOpenMetas

  let extend = map (rToR . P.continuousPerLine)

  rs <- extend <$> mapM getMetaRange (ms \\ is)

  rs' <- extend <$> mapM getMetaRange is
  return $ (rs ++ rs', metasHighlighting' rs)

metasHighlighting :: [Range] -> HighlightingInfoBuilder
metasHighlighting rs = metasHighlighting' (map (rToR . P.continuousPerLine) rs)

metasHighlighting' :: [Ranges] -> HighlightingInfoBuilder
metasHighlighting' rs = several rs
                     $ parserBased { otherAspects = Set.singleton UnsolvedMeta }

-- | Generates syntax highlighting information for unsolved constraints
--   (ideally: that are not connected to a meta variable).

computeUnsolvedConstraints :: [Ranges] -- ^ does not add ranges that would overlap with these.
                           -> TCM HighlightingInfoBuilder
computeUnsolvedConstraints ms = constraintsHighlighting ms <$> getAllConstraints

constraintsHighlighting ::
  [Ranges] -> Constraints -> HighlightingInfoBuilder
constraintsHighlighting ms cs =
  several (filter noOverlap $ map (rToR . P.continuousPerLine) rs)
          (parserBased { otherAspects = Set.singleton UnsolvedConstraint })
  where
  noOverlap r = not $ any (overlappings $ r) $ ms
  -- get ranges of interesting unsolved constraints
  rs = (`mapMaybe` (map theConstraint cs)) $ \case
    Closure{ clValue = IsEmpty r t           } -> Just r
    Closure{ clEnv = e, clValue = ValueCmp{} } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = ElimCmp{}  } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = SortCmp{}  } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = LevelCmp{} } -> Just $ getRange (envRange e)
    Closure{ clEnv = e, clValue = CheckSizeLtSat{} } -> Just $ getRange (envRange e)
    _ -> Nothing


-- * Disambiguation of constructors and projections.

storeDisambiguatedField :: A.QName -> TCM ()
storeDisambiguatedField = storeDisambiguatedName Field

storeDisambiguatedProjection :: A.QName -> TCM ()
storeDisambiguatedProjection = storeDisambiguatedField

storeDisambiguatedConstructor :: Common.Induction -> A.QName -> TCM ()
storeDisambiguatedConstructor i = storeDisambiguatedName $ Constructor i

-- TODO: move the following function to a new module TypeChecking.Overloading
-- that gathers functions concerning disambiguation of overloading.

-- | Remember a name disambiguation (during type checking).
--   To be used later during syntax highlighting.
--   Also: raise user warnings associated with the name.
storeDisambiguatedName :: NameKind -> A.QName -> TCM ()
storeDisambiguatedName k q = do
  raiseWarningsOnUsage q
  whenJust (start $ getRange q) $ \ i ->
    modifyTCLens stDisambiguatedNames $ IntMap.insert i $ DisambiguatedName k q
  where
  start r = fromIntegral . P.posPos <$> P.rStart' r

-- | Store a disambiguation of record field tags for the purpose of highlighting.
disambiguateRecordFields
  :: [C.Name]   -- ^ Record field names in a record expression.
  -> [A.QName]  -- ^ Record field names in the corresponding record type definition
  -> TCM ()
disambiguateRecordFields cxs axs = forM_ cxs $ \ cx -> do
  caseMaybe (List.find ((cx ==) . A.nameConcrete . A.qnameName) axs) (return ()) $ \ ax -> do
    storeDisambiguatedField ax{ A.qnameName = (A.qnameName ax) { A.nameConcrete = cx } }
