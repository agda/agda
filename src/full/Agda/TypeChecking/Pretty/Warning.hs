
module Agda.TypeChecking.Pretty.Warning where

import Prelude hiding ( null )

import Data.Char ( toLower )
import Data.Function
import qualified Data.Set as Set
import qualified Data.List as List

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.State ( getScope )
import Agda.TypeChecking.Positivity () --instance only
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Call

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
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P

instance PrettyTCM TCWarning where
  prettyTCM = return . tcWarningPrintedWarning

instance PrettyTCM Warning where
  prettyTCM = prettyWarning

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

{-# SPECIALIZE prettyWarning :: Warning -> TCM Doc #-}
prettyWarning :: MonadPretty m => Warning -> m Doc
prettyWarning wng = case wng of

    UnsolvedMetaVariables ms  ->
      fsep ( pwords "Unsolved metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM ms)

    UnsolvedInteractionMetas is ->
      fsep ( pwords "Unsolved interaction metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM is)

    UnsolvedConstraints cs -> ifNull (filter interestingConstraint cs)
      {-then-} (fsep $ pwords "Unsolved constraints")  -- #4065: keep minimal warning text
      {-else-} $ \ cs' -> vcat
        [ fsep $ pwords "Failed to solve the following constraints:"
        , nest 2 $ P.vcat . List.nub <$> mapM prettyConstraint cs'
        ]

    TerminationIssue because -> do
      dropTopLevel <- topLevelModuleDropper
      fwords "Termination checking failed for the following functions:"
        $$ (nest 2 $ fsep $ punctuate comma $
             map (pretty . dropTopLevel) $
               concatMap termErrFunctions because)
        $$ fwords "Problematic calls:"
        $$ (nest 2 $ fmap (P.vcat . List.nub) $
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
      [ fsep $ pwords "Exact splitting is enabled, but the following" ++ pwords (P.singPlural cs "clause" "clauses") ++
               pwords "could not be preserved as definitional equalities in the translation to a case tree:"
      ] ++
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

    IllformedAsClause s -> fsep . pwords $
      "`as' must be followed by an identifier" ++ s

    ClashesViaRenaming nm xs -> fsep $ concat $
      [ [ case nm of NameNotModule -> "Name"; ModuleNotName -> "Module" ]
      , pwords "clashes introduced by `renaming':"
      , map prettyTCM xs
      ]

    UselessPublic -> fwords $ "Keyword `public' is ignored here"

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

    SafeFlagInjective -> fsep $
      pwords "Cannot use INJECTIVE pragma with safe flag."

    SafeFlagNoCoverageCheck -> fsep $
      pwords "Cannot use NON_COVERING pragma with safe flag."

    ParseWarning pw -> pretty pw

    DeprecationWarning old new version -> fsep $
      [text old] ++ pwords "has been deprecated. Use" ++ [text new] ++ pwords
      "instead. This will be an error in Agda" ++ [text version <> "."]

    NicifierIssue w -> sayWhere (getRange w) $ pretty w

    UserWarning str -> text str

    ModuleDoesntExport m xs -> fsep $
      pwords "The module" ++ [pretty m] ++ pwords "doesn't export the following:" ++
      punctuate comma (map pretty xs)

    FixityInRenamingModule _rs -> fsep $ pwords "Modules do not have fixity"

    LibraryWarning lw -> pretty lw

    InfectiveImport o m -> fsep $
      pwords "Importing module" ++ [pretty m] ++ pwords "using the" ++
      [pretty o] ++ pwords "flag from a module which does not."

    CoInfectiveImport o m -> fsep $
      pwords "Importing module" ++ [pretty m] ++ pwords "not using the" ++
      [pretty o] ++ pwords "flag from a module which does."

    RewriteNonConfluent lhs rhs1 rhs2 err -> fsep
      [ "Confluence check failed:"
      , prettyTCM lhs , "reduces to both"
      , prettyTCM rhs1 , "and" , prettyTCM rhs2
      , "which are not equal because"
      , return err
      ]

    RewriteMaybeNonConfluent lhs1 lhs2 cs -> do
      vcat $
        [ fsep
           [ "Couldn't determine overlap between left-hand sides"
           , prettyTCM lhs1 , "and" , prettyTCM lhs2
           , "because of unsolved constraints:"
           ]
        ] ++ map (nest 2 . return) cs

    PragmaCompileErased bn qn -> fsep $
      pwords "The backend" ++ [text bn] ++ pwords "erases" ++ [prettyTCM qn]
      ++ pwords "so the COMPILE pragma will be ignored."

    NotInScopeW xs -> do
      inscope <- Set.toList . concreteNamesInScope <$> getScope
      fsep (pwords "Not in scope:") $$ nest 2 (vcat $ map (name inscope) xs)
      where
      name inscope x =
        fsep [ pretty x
             , "at" <+> prettyTCM (getRange x)
             , suggestion inscope x
             ]
      suggestion inscope x = nest 2 $ par $
        [ "did you forget space around the ':'?"  | ':' `elem` s ] ++
        [ "did you forget space around the '->'?" | List.isInfixOf "->" s ] ++
        [ sep [ "did you mean"
              , nest 2 $ vcat (punctuate " or"
                       $ map (\ y -> text $ "'" ++ y ++ "'") ys)
              <> "?" ]
          | not $ null ys ]
        where
          s = P.prettyShow x
          par []  = empty
          par [d] = parens d
          par ds  = parens $ vcat ds

          strip x = map toLower $ filter (/= '_') $ P.prettyShow $ C.unqualify x
          maxDist n = div n 3
          close a b = editDistance a b <= maxDist (length a)
          ys = map P.prettyShow $ filter (close (strip x) . strip) inscope


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
    UnsolvedConstraints cs -> not $ null $ filter interestingConstraint cs
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
              (TCWarning r w p b:_, sfp) ->
                 [TCWarning r (SafeFlagPragma sfp) p b]
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
