
module Agda.TypeChecking.Pretty.Warning where

import Prelude hiding ( null )

import Data.Char ( toLower )
import Data.Function
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Text as T

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.State ( getScope )
import Agda.TypeChecking.Positivity () --instance only
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Call

import Agda.Syntax.Common ( AgdaSourceErrorLocation(..), ImportedName'(..), fromImportedName, partitionImportedNames )
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base ( concreteNamesInScope, NameOrModule(..) )
import Agda.Syntax.Internal
import Agda.Syntax.Translation.InternalToAbstract

import {-# SOURCE #-} Agda.Interaction.Imports
import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings

import Agda.Utils.Lens
import Agda.Utils.List ( editDistance )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Utils.Pretty ( Pretty, prettyShow )
import qualified Agda.Utils.Pretty as P

instance PrettyTCM TCWarning where
  prettyTCM w@(TCWarning fl _ _ _ _) = do
    reportSLn "warning" 2 $ "Warning raised at " ++ prettyShow fl
    pure $ tcWarningPrintedWarning w

prettyConstraint :: MonadPretty m => ProblemConstraint -> m Doc
prettyConstraint c = f (locallyTCState stInstantiateBlocking (const True) $ prettyTCM c)
  where
    r   = getRange c
    f :: MonadPretty m => m Doc -> m Doc
    f d = if null $ P.pretty r
          then d
          else d $$ nest 4 ("[ at" <+> prettyTCM r <+> "]")

interestingConstraint :: ProblemConstraint -> Bool
interestingConstraint pc = go $ clValue (theConstraint pc)
  where
    go UnBlock{}     = False
    go (Guarded c _) = go c
    go _             = True

prettyInterestingConstraints :: MonadPretty m => [ProblemConstraint] -> m [Doc]
prettyInterestingConstraints cs = mapM (prettyConstraint . stripPids) $ List.sortBy (compare `on` isBlocked) cs'
  where
    isBlocked = not . null . blocking . clValue . theConstraint
    cs' = filter interestingConstraint cs
    interestingPids = Set.fromList $ concatMap (blocking . clValue . theConstraint) cs'
    stripPids (PConstr pids unblock c) = PConstr (Set.intersection pids interestingPids) unblock c
    blocking (Guarded c pid) = pid : blocking c
    blocking _               = []

prettyWarning :: MonadPretty m => Warning -> m Doc
prettyWarning = \case

    UnsolvedMetaVariables ms  ->
      fsep ( pwords "Unsolved metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM ms)

    UnsolvedInteractionMetas is ->
      fsep ( pwords "Unsolved interaction metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM is)

    UnsolvedConstraints cs -> do
      pcs <- prettyInterestingConstraints cs
      if null pcs
        then fsep $ pwords "Unsolved constraints"  -- #4065: keep minimal warning text
        else vcat
          [ fsep $ pwords "Failed to solve the following constraints:"
          , nest 2 $ return $ P.vcat $ List.nub pcs
          ]

    TerminationIssue because -> do
      dropTopLevel <- topLevelModuleDropper
      fwords "Termination checking failed for the following functions:"
        $$ nest 2 (fsep $ punctuate comma $
             map (pretty . dropTopLevel) $
               concatMap termErrFunctions because)
        $$ fwords "Problematic calls:"
        $$ nest 2 (fmap (P.vcat . List.nub) $
              mapM prettyTCM $ List.sortBy (compare `on` callInfoRange) $
              concatMap termErrCalls because)

    UnreachableClauses f pss -> fsep $
      pwords "Unreachable" ++ pwords (plural (length pss) "clause")
        where
          plural 1 thing = thing
          plural n thing = thing ++ "s"

    CoverageIssue f pss -> fsep (
      pwords "Incomplete pattern matching for" ++ [prettyTCM f <> "."] ++
      pwords "Missing cases:") $$ nest 2 (vcat $ map display pss)
        where
        display (tel, ps) = prettyTCM $ NamedClause f True $
          empty { clauseTel = tel, namedClausePats = ps }

    CoverageNoExactSplit f cs -> vcat $
      fsep (pwords "Exact splitting is enabled, but the following" ++ pwords (P.singPlural cs "clause" "clauses") ++
            pwords "could not be preserved as definitional equalities in the translation to a case tree:"
           ) :
      map (nest 2 . prettyTCM . NamedClause f True) cs

    NotStrictlyPositive d ocs -> fsep $
      [prettyTCM d] ++ pwords "is not strictly positive, because it occurs"
      ++ [prettyTCM ocs]

    CantGeneralizeOverSorts ms -> vcat
            [ text "Cannot generalize over unsolved sort metas:"
            , nest 2 $ vcat [ prettyTCM x <+> text "at" <+> (pretty =<< getMetaRange x) | x <- ms ]
            , fsep $ pwords "Suggestion: add a `variable Any : Set _` and replace unsolved metas by Any"
            ]

    AbsurdPatternRequiresNoRHS ps -> fwords $
      "The right-hand side must be omitted if there " ++
      "is an absurd pattern, () or {}, in the left-hand side."

    OldBuiltin old new -> fwords $
      "Builtin " ++ old ++ " no longer exists. " ++
      "It is now bound by BUILTIN " ++ new

    EmptyRewritePragma -> fsep . pwords $ "Empty REWRITE pragma"

    EmptyWhere         -> fsep . pwords $ "Empty `where' block (ignored)"

    IllformedAsClause s -> fsep . pwords $
      "`as' must be followed by an identifier" ++ s

    ClashesViaRenaming nm xs -> fsep $ concat $
      [ [ case nm of NameNotModule -> "Name"; ModuleNotName -> "Module" ]
      , pwords "clashes introduced by `renaming':"
      , map prettyTCM xs
      ]

    UselessPatternDeclarationForRecord s -> fwords $ unwords
      [ "`pattern' attribute ignored for", s, "record" ]

    UselessPublic -> fwords $ "Keyword `public' is ignored here"

    UselessHiding xs -> fsep $ concat
      [ pwords "Ignoring names in `hiding' directive:"
      , punctuate "," $ map pretty xs
      ]

    UselessInline q -> fsep $
      pwords "It is pointless for INLINE'd function" ++ [prettyTCM q] ++
      pwords "to have a separate Haskell definition"

    WrongInstanceDeclaration -> fwords "Terms marked as eligible for instance search should end with a name, so `instance' is ignored here."

    InstanceWithExplicitArg q -> fsep $
      pwords "Instance declarations with explicit arguments are never considered by instance search," ++
      pwords "so making" ++ [prettyTCM q] ++ pwords "into an instance has no effect."

    InstanceNoOutputTypeName b -> fsep $
      pwords "Instance arguments whose type does not end in a named or variable type are never considered by instance search," ++
      pwords "so having an instance argument" ++ [return b] ++ pwords "has no effect."

    InstanceArgWithExplicitArg b -> fsep $
      pwords "Instance arguments with explicit arguments are never considered by instance search," ++
      pwords "so having an instance argument" ++ [return b] ++ pwords "has no effect."

    InversionDepthReached f -> do
      maxDepth <- maxInversionDepth
      fsep $ pwords "Refusing to invert pattern matching of" ++ [prettyTCM f] ++
             pwords ("because the maximum depth (" ++ show maxDepth ++ ") has been reached.") ++
             pwords "Most likely this means you have an unsatisfiable constraint, but it could" ++
             pwords "also mean that you need to increase the maximum depth using the flag" ++
             pwords "--inversion-max-depth=N"

    GenericWarning d -> return d

    GenericNonFatalError d -> return d

    GenericUseless _r d -> return d

    SafeFlagPostulate e -> fsep $
      pwords "Cannot postulate" ++ [pretty e] ++ pwords "with safe flag"

    SafeFlagPragma xs ->
      let plural | length xs == 1 = ""
                 | otherwise      = "s"
      in fsep $ [fwords ("Cannot set OPTIONS pragma" ++ plural)]
                ++ map text xs ++ [fwords "with safe flag."]

    SafeFlagNonTerminating -> fsep $
      pwords "Cannot use NON_TERMINATING pragma with safe flag."

    SafeFlagTerminating -> fsep $
      pwords "Cannot use TERMINATING pragma with safe flag."

    SafeFlagWithoutKFlagPrimEraseEquality -> fsep (pwords "Cannot use primEraseEquality with safe and without-K flags.")

    WithoutKFlagPrimEraseEquality -> fsep (pwords "Using primEraseEquality with the without-K flag is inconsistent.")

    SafeFlagNoPositivityCheck -> fsep $
      pwords "Cannot use NO_POSITIVITY_CHECK pragma with safe flag."

    SafeFlagPolarity -> fsep $
      pwords "Cannot use POLARITY pragma with safe flag."

    SafeFlagNoUniverseCheck -> fsep $
      pwords "Cannot use NO_UNIVERSE_CHECK pragma with safe flag."

    SafeFlagEta -> fsep $
      pwords "Cannot use ETA pragma with safe flag."

    SafeFlagInjective -> fsep $
      pwords "Cannot use INJECTIVE pragma with safe flag."

    SafeFlagNoCoverageCheck -> fsep $
      pwords "Cannot use NON_COVERING pragma with safe flag."

    ParseWarning pw -> pretty pw

    DeprecationWarning old new version -> fsep $
      [text old] ++ pwords "has been deprecated. Use" ++ [text new] ++ pwords
      "instead. This will be an error in Agda" ++ [text version <> "."]

    NicifierIssue w -> sayWhere (getRange w) $ pretty w

    UserWarning str -> text (T.unpack str)

    ModuleDoesntExport m names modules xs -> vcat
      [ fsep $ pwords "The module" ++ [pretty m] ++ pwords "doesn't export the following:"
      , prettyNotInScopeNames False (suggestion names)   ys
      , prettyNotInScopeNames False (suggestion modules) ms
      ]
      where
      ys, ms :: [C.ImportedName]
      ys            = map ImportedName   ys0
      ms            = map ImportedModule ms0
      (ys0, ms0)    = partitionImportedNames xs
      suggestion zs = maybe empty parens . didYouMean (map C.QName zs) fromImportedName

    DuplicateUsing xs -> fsep $ pwords "Duplicates in `using` directive:" ++ map pretty (List1.toList xs)

    FixityInRenamingModule _rs -> fsep $ pwords "Modules do not have fixity"

    LibraryWarning lw -> pretty lw

    InfectiveImport o m -> fsep $
      pwords "Importing module" ++ [pretty m] ++ pwords "using the" ++
      [pretty o] ++ pwords "flag from a module which does not."

    CoInfectiveImport o m -> fsep $
      pwords "Importing module" ++ [pretty m] ++ pwords "not using the" ++
      [pretty o] ++ pwords "flag from a module which does."

    RewriteNonConfluent lhs rhs1 rhs2 err -> fsep
      [ "Local confluence check failed:"
      , prettyTCM lhs , "reduces to both"
      , prettyTCM rhs1 , "and" , prettyTCM rhs2
      , "which are not equal because"
      , return err
      ]

    RewriteMaybeNonConfluent lhs1 lhs2 cs -> vcat $ concat
      [ [ fsep $ concat
          [ pwords "Couldn't determine overlap between left-hand sides"
          , [ prettyTCM lhs1 , text "and" , prettyTCM lhs2 ]
          , pwords "because of unsolved constraints:"
          ]
        ]
      , map (nest 2 . return) cs
      ]

    RewriteAmbiguousRules lhs rhs1 rhs2 -> vcat
      [ ( fsep $ concat
          [ pwords "Global confluence check failed:" , [prettyTCM lhs]
          , pwords "can be rewritten to either" , [prettyTCM rhs1]
          , pwords "or" , [prettyTCM rhs2 <> "."]
          ])
      , fsep $ concat
        [ pwords "Possible fix: add a rewrite rule with left-hand side"
        , [prettyTCM lhs] , pwords "to resolve the ambiguity."
        ]
      ]

    RewriteMissingRule u v rhou -> vcat
      [ fsep $ concat
        [ pwords "Global confluence check failed:" , [prettyTCM u]
        , pwords "unfolds to" , [prettyTCM v] , pwords "which should further unfold to"
        , [prettyTCM rhou] , pwords "but it does not."
        ]
      , fsep $ concat
        [ pwords "Possible fix: add a rule to rewrite"
        , [ prettyTCM v , "to" , prettyTCM rhou <> "," ]
        , pwords "or change the order of the rules so more specialized rules come later."
        ]
      ]

    PragmaCompileErased bn qn -> fsep $ concat
      [ pwords "The backend"
      , [ text bn
        , "erases"
        , prettyTCM qn
        ]
      , pwords "so the COMPILE pragma will be ignored."
      ]

    NotInScopeW xs -> vcat
      [ fsep $ pwords "Not in scope:"
      , do
        inscope <- Set.toList . concreteNamesInScope <$> getScope
        prettyNotInScopeNames True (suggestion inscope) xs
      ]
      where
      suggestion inscope x = nest 2 $ par $ concat
        [ [ "did you forget space around the ':'?"  | ':' `elem` s ]
        , [ "did you forget space around the '->'?" | "->" `List.isInfixOf` s ]
        , maybeToList $ didYouMean inscope C.unqualify x
        ]
        where
        par []  = empty
        par [d] = parens d
        par ds  = parens $ vcat ds
        s = P.prettyShow x

    AsPatternShadowsConstructorOrPatternSynonym patsyn -> fsep $ concat
      [ pwords "Name bound in @-pattern ignored because it shadows"
      , if patsyn then pwords "pattern synonym" else [ "constructor" ]
      ]

    RecordFieldWarning w -> prettyRecordFieldWarning w

prettyRecordFieldWarning :: MonadPretty m => RecordFieldWarning -> m Doc
prettyRecordFieldWarning = \case
  DuplicateFieldsWarning xrs    -> prettyDuplicateFields $ map fst xrs
  TooManyFieldsWarning q ys xrs -> prettyTooManyFields q ys $ map fst xrs

prettyDuplicateFields :: MonadPretty m => [C.Name] -> m Doc
prettyDuplicateFields xs = fsep $ concat
    [ pwords "Duplicate"
    , fields xs
    , punctuate comma (map pretty xs)
    , pwords "in record"
    ]
  where
  fields ys = P.singPlural ys [text "field"] [text "fields"]

prettyTooManyFields :: MonadPretty m => QName -> [C.Name] -> [C.Name] -> m Doc
prettyTooManyFields r missing xs = fsep $ concat
    [ pwords "The record type"
    , [prettyTCM r]
    , pwords "does not have the"
    , fields xs
    , punctuate comma (map pretty xs)
    , if null missing then [] else concat
      [ pwords "but it would have the"
      , fields missing
      , punctuate comma (map pretty missing)
      ]
    ]
  where
  fields ys = P.singPlural ys [text "field"] [text "fields"]

-- | Report a number of names that are not in scope.
prettyNotInScopeNames
  :: (MonadPretty m, Pretty a, HasRange a)
  => Bool          -- ^ Print range?
  -> (a -> m Doc)  -- ^ Correction suggestion generator.
  -> [a]           -- ^ Names that are not in scope.
  -> m Doc
prettyNotInScopeNames printRange suggestion xs = nest 2 $ vcat $ map name xs
  where
  name x = fsep
    [ pretty x
    , if printRange then "at" <+> prettyTCM (getRange x) else empty
    , suggestion x
    ]

-- | Suggest some corrections to a misspelled name.
didYouMean
  :: (MonadPretty m, Pretty a, Pretty b)
  => [C.QName]     -- ^ Names in scope.
  -> (a -> b)      -- ^ Canonization function for similarity search.
  -> a             -- ^ A name which is not in scope.
  -> Maybe (m Doc) -- ^ "did you mean" hint.
didYouMean inscope canon x
  | null ys   = Nothing
  | otherwise = Just $ sep
      [ "did you mean"
      , nest 2 (vcat $ punctuate " or" $
                 map (\ y -> text $ "'" ++ y ++ "'") ys)
        <> "?"
      ]
  where
  strip :: Pretty b => b -> String
  strip        = map toLower . filter (/= '_') . prettyShow
  -- dropModule x = fromMaybe x $ List.stripPrefix "module " x
  maxDist n    = div n 3
  close a b    = editDistance a b <= maxDist (length a)
  ys           = map prettyShow $ filter (close (strip $ canon x) . strip . C.unqualify) inscope


prettyTCWarnings :: [TCWarning] -> TCM String
prettyTCWarnings = fmap (unlines . List.intersperse "") . prettyTCWarnings'

prettyTCWarnings' :: [TCWarning] -> TCM [String]
prettyTCWarnings' = mapM (fmap P.render . prettyTCM) . filterTCWarnings

-- | If there are several warnings, remove the unsolved-constraints warning
-- in case there are no interesting constraints to list.
filterTCWarnings :: [TCWarning] -> [TCWarning]
filterTCWarnings = \case
  -- #4065: Always keep the only warning
  [w] -> [w]
  -- Andreas, 2019-09-10, issue #4065:
  -- If there are several warnings, remove the unsolved-constraints warning
  -- in case there are no interesting constraints to list.
  ws  -> (`filter` ws) $ \ w -> case tcWarning w of
    UnsolvedConstraints cs -> any interestingConstraint cs
    _ -> True


-- | Turns all warnings into errors.
tcWarningsToError :: [TCWarning] -> TCM a
tcWarningsToError ws = typeError $ case ws of
  [] -> SolvedButOpenHoles
  _  -> NonFatalErrors ws


-- | Depending which flags are set, one may happily ignore some
-- warnings.

applyFlagsToTCWarnings' :: MainInterface -> [TCWarning] -> TCM [TCWarning]
applyFlagsToTCWarnings' isMain ws = do

  -- For some reason some SafeFlagPragma seem to be created multiple times.
  -- This is a way to collect all of them and remove duplicates.
  let pragmas w = case tcWarning w of { SafeFlagPragma ps -> ([w], ps); _ -> ([], []) }
  let sfp = case fmap List.nub (foldMap pragmas ws) of
              (TCWarning fl r w p b:_, sfp) ->
                 [TCWarning fl r (SafeFlagPragma sfp) p b]
              _                        -> []

  warnSet <- do
    opts <- pragmaOptions
    let warnSet = optWarningMode opts ^. warningSet
    pure $ if isMain /= NotMainInterface
           then Set.union warnSet unsolvedWarnings
           else warnSet

  -- filter out the warnings the flags told us to ignore
  let cleanUp w = let wName = warningName w in
        wName /= SafeFlagPragma_
        && wName `Set.member` warnSet
        && case w of
          UnsolvedMetaVariables ums    -> not $ null ums
          UnsolvedInteractionMetas uis -> not $ null uis
          UnsolvedConstraints ucs      -> not $ null ucs
          _                            -> True

  return $ sfp ++ filter (cleanUp . tcWarning) ws

applyFlagsToTCWarnings :: [TCWarning] -> TCM [TCWarning]
applyFlagsToTCWarnings = applyFlagsToTCWarnings' NotMainInterface
