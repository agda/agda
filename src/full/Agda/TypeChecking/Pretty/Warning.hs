
module Agda.TypeChecking.Pretty.Warning where

import Prelude hiding ( null )

import Control.Monad ( guard, filterM, (<=<) )

import Data.Char ( toLower )
import Data.Function (on)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.List as List
import qualified Data.Text as T

import Agda.TypeChecking.Monad.Base
import qualified Agda.TypeChecking.Monad.Base.Warning as W
import Agda.TypeChecking.Monad.Builtin
import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.State ( getScope )
import Agda.TypeChecking.Monad ( localTCState, enterClosure )
import Agda.TypeChecking.Positivity () --instance only
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Call () -- instance PrettyTCM CallInfo
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Constraint (prettyInterestingConstraints, interestingConstraint)
import Agda.TypeChecking.Warnings (MonadWarning, isUnsolvedWarning, onlyShowIfUnsolved, classifyWarning, WhichWarnings(..), warning_)
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.Syntax.Common
  ( ImportedName'(..), fromImportedName, partitionImportedNames
  , IsOpaque(OpaqueDef, TransparentDef)
  , ProjOrigin(..)
  , getHiding
  )
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base ( concreteNamesInScope, NameOrModule(..) )
import Agda.Syntax.Internal
import Agda.Syntax.Translation.InternalToAbstract

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings

import Agda.Utils.FileName ( filePath )
import Agda.Utils.Functor  ( (<.>) )
import Agda.Utils.Lens
import Agda.Utils.List ( editDistance )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty ( Pretty, prettyShow, singPlural )
import qualified Agda.Syntax.Common.Pretty as P

import Agda.Utils.Impossible

instance PrettyTCM TCWarning where
  prettyTCM w@(TCWarning loc _ _ _ _) = do
    reportSLn "warning" 2 $ "Warning raised at " ++ prettyShow loc
    pure $ tcWarningPrintedWarning w

{-# SPECIALIZE prettyWarning :: Warning -> TCM Doc #-}
prettyWarning :: MonadPretty m => Warning -> m Doc
prettyWarning = \case

    UnsolvedMetaVariables ms  ->
      fsep ( pwords "Unsolved metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM ms)

    UnsolvedInteractionMetas is ->
      fsep ( pwords "Unsolved interaction metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM is)

    InteractionMetaBoundaries is ->
      fsep ( pwords "Interaction meta(s) at the following location(s) have unsolved boundary constraints:" )
      $$ nest 2 (vcat $ map prettyTCM (Set.toList (Set.fromList is)))

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
              mapM prettyTCM $ List.sortOn getRange $
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

    InlineNoExactSplit f c -> vcat $
      [ fsep $
          pwords "Exact splitting is enabled, but the following clause" ++
          pwords "is no longer a definitional equality because it was translated to a copattern match:"
      , nest 2 . prettyTCM . NamedClause f True $ c
      ]

    NotStrictlyPositive d ocs -> fsep $
      [prettyTCM d] ++ pwords "is not strictly positive, because it occurs"
      ++ [prettyTCM ocs]

    ConstructorDoesNotFitInData c s1 s2 err -> msg $$
      case err of
        TypeError _loc s e -> withTCState (const s) $ enterClosure e \ e ->
          parens ("Reason:" <+> prettyTCM e)
        _ ->
          prettyTCM err
      where
        msg = sep
          [ "Constructor" <+> prettyTCM c
          , "of sort" <+> prettyTCM s1
          , ("does not fit into data type of sort" <+> prettyTCM s2) <> "."
          ]

    CoinductiveEtaRecord name -> vcat
      [ fsep $ pwords "Not switching on eta-equality for coinductive records."
      , fsep $ pwords "If you must, use pragma" ++ [ "{-# ETA", prettyTCM name, "#-}" ]
      ]

    UnsupportedIndexedMatch doc -> vcat
      [ fsep (pwords "This clause uses pattern-matching features that are not yet supported by Cubical Agda,"
           ++ pwords "the function to which it belongs will not compute when applied to transports."
             )
      , ""
      , "Reason:" <+> pure doc
      , ""
      ]

    CantGeneralizeOverSorts ms -> vcat
            [ text "Cannot generalize over unsolved sort metas:"
            , nest 2 $ vcat [ prettyTCM x <+> text "at" <+> (pretty =<< getMetaRange x) | x <- ms ]
            , fsep $ pwords "Suggestion: add a `variable Any : Set _` and replace unsolved metas by Any"
            ]

    AbsurdPatternRequiresAbsentRHS ps -> fwords $
      "The right-hand side must be omitted if there " ++
      "is an absurd pattern, () or {}, in the left-hand side."

    OldBuiltin old new -> fwords $
      "Builtin " ++ getBuiltinId old ++ " no longer exists. " ++
      "It is now bound by BUILTIN " ++ getBuiltinId new

    BuiltinDeclaresIdentifier b -> fwords $
      "BUILTIN " ++ getBuiltinId b ++ " declares an identifier " ++
      "(no longer expects an already defined identifier)"

    EmptyRewritePragma -> fsep . pwords $ "Empty REWRITE pragma"

    EmptyWhere         -> fsep . pwords $ "Empty `where' block (ignored)"

    -- TODO: linearity
    -- FixingQuantity s q q' -> fsep $ concat
    --   [ pwords "Replacing illegal quantity", [ pretty q ], pwords s, [ "by", pretty q' ] ]

    FixingRelevance s r r' ->  fsep $ concat
      [ pwords "Replacing illegal relevance", [ p r ]
      , pwords s, [ "by", p r' ]
      ]
      where p r = text $ "`" ++ verbalize r ++ "'"

    IllformedAsClause s -> fsep . pwords $
      "`as' must be followed by an identifier" ++ s

    ClashesViaRenaming nm xs -> fsep $ concat $
      [ [ case nm of NameNotModule -> "Name"; ModuleNotName -> "Module" ]
      , pwords "clashes introduced by `renaming':"
      , map prettyTCM xs
      ]

    UselessPatternDeclarationForRecord s -> fwords $ unwords
      [ "`pattern' attribute ignored for", s, "record" ]
      -- the @s@ is a qualifier like "eta" or "coinductive"

    UselessPublic -> fwords $ "Keyword `public' is ignored here"

    UselessHiding xs -> fsep $ concat
      [ pwords "Ignoring names in `hiding' directive:"
      , punctuate "," $ map pretty xs
      ]

    UselessInline q -> fsep $
      pwords "It is pointless for INLINE'd function" ++ [prettyTCM q] ++
      pwords "to have a separate Haskell definition"

    WrongInstanceDeclaration -> fwords $
      "Instances should be of type {Γ} → C, where C evaluates to a postulated name or the name of " ++
      "a data or record type, so `instance' is ignored here."

    InstanceWithExplicitArg q -> fsep $
      pwords "Instance declarations with explicit arguments are never considered by instance search," ++
      pwords "so making" ++ [prettyTCM q] ++ pwords "into an instance has no effect."

    InstanceNoOutputTypeName b -> fsep $
      pwords "Instance arguments whose type is not {Γ} → C, where C evaluates to a postulated type, " ++
      pwords "a parameter type or the name of a data or record type, are never considered by instance search," ++
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

    NoGuardednessFlag q ->
      fsep $ [ prettyTCM q ] ++ pwords "is declared coinductive, but option" ++
             pwords "--guardedness is not enabled. Coinductive functions on" ++
             pwords "this type will likely be rejected by the termination" ++
             pwords "checker unless this flag is enabled."

    InvalidCharacterLiteral c -> fsep $
      pwords "Invalid character literal" ++ [text $ show c] ++
      pwords "(surrogate code points are not supported)"

    UselessPragma _r d -> return d

    SafeFlagPostulate e -> fsep $
      pwords "Cannot postulate" ++ [pretty e] ++ pwords "with safe flag"

    SafeFlagPragma xs -> fsep $ concat
      [ [ fwords $ singPlural (words =<< xs) id (++ "s") "Cannot set OPTIONS pragma" ]
      , map text xs
      , [ fwords "with safe flag." ]
      ]

    SafeFlagWithoutKFlagPrimEraseEquality -> fsep (pwords "Cannot use primEraseEquality with safe and without-K flags.")

    WithoutKFlagPrimEraseEquality -> fsep (pwords "Using primEraseEquality with the without-K flag is inconsistent.")

    ConflictingPragmaOptions a b -> fsep $ pwords $ unwords
      [ "Conflicting options", yes a, "and", no b, "(" ++ yes a, "implies", yes b ++ ")."
      , "Ignoring", no b ++ "." ]
      where
        yes s = "--" ++ s
        no ('n' : 'o' : '-' : s) = "--" ++ s
        no s                     = "--no-" ++ s

    OptionWarning ow -> pretty ow

    ParseWarning pw -> pretty pw

    DuplicateInterfaceFiles selected ignored -> vcat
      [ fwords "There are two interface files:"
      , nest 4 $ text $ filePath selected
      , nest 4 $ text $ filePath ignored
      , nest 2 $ fsep $ pwords "Using" ++ [text $ filePath selected] ++ pwords "for now but please remove at least one of them."
      ]

    DeprecationWarning old new version -> fsep $
      [text old] ++ pwords "has been deprecated. Use" ++ [text new] ++ pwords
      "instead. This will be an error in Agda" ++ [text version <> "."]

    NicifierIssue w -> pretty w

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

    InfectiveImport msg -> return msg

    CoInfectiveImport msg -> return msg

    NotARewriteRule x amb -> hsep $ concat
        [ [ pretty x ]
        , pwords "is not a legal rewrite rule, since the left-hand side is"
        , case amb of
            YesAmbiguous xs -> [ "ambiguous:", pretty xs ]
            NotAmbiguous -> pwords "neither a defined symbol nor a constructor"
        ]

    IllegalRewriteRule q reason -> case reason of
      LHSNotDefinitionOrConstructor -> hsep
        [ prettyTCM q , " is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor" ]
      VariablesNotBoundByLHS xs -> hsep
        [ prettyTCM q
        , " is not a legal rewrite rule, since the following variables are not bound by the left hand side: "
        , prettyList_ (map (prettyTCM . var) $ IntSet.toList xs)
        ]
      VariablesBoundMoreThanOnce xs -> do
        (prettyTCM q
          <+> " is not a legal rewrite rule, since the following parameters are bound more than once on the left hand side: "
          <+> hsep (List.intersperse "," $ map (prettyTCM . var) $ IntSet.toList xs))
          <> ". Perhaps you can use a postulate instead of a constructor as the head symbol?"
      LHSReduces v v' -> fsep
        [ prettyTCM q <+> " is not a legal rewrite rule, since the left-hand side "
        , prettyTCM v <+> " reduces to " <+> prettyTCM v' ]
      HeadSymbolIsProjectionLikeFunction f -> hsep
        [ prettyTCM q , " is not a legal rewrite rule, since the head symbol"
        , hd , "is a projection-like function."
        , "You can turn off the projection-like optimization for", hd
        , "with the pragma {-# NOT_PROJECTION_LIKE", hd, "#-}"
        , "or globally with the flag --no-projection-like"
        ]
        where hd = prettyTCM f
      HeadSymbolIsTypeConstructor f -> hsep
        [ prettyTCM q , " is not a legal rewrite rule, since the head symbol"
        , prettyTCM f , "is a type constructor."
        ]
      HeadSymbolContainsMetas f -> hsep
        [ prettyTCM q , "is not a legal rewrite rule, since the definition of the head symbol"
        , prettyTCM f , "contains unsolved metavariables and confluence checking is enabled."
        ]
      ConstructorParametersNotGeneral c vs -> vcat
        [ prettyTCM q <+> text " is not a legal rewrite rule, since the constructor parameters are not fully general:"
        , nest 2 $ text "Constructor: " <+> prettyTCM c
        , nest 2 $ text "Parameters: " <+> prettyList (map prettyTCM vs)
        ]
      ContainsUnsolvedMetaVariables ms -> hsep
        [ prettyTCM q , " is not a legal rewrite rule, since"
        , "it contains the unsolved meta variable(s)", prettyList_ (map prettyTCM $ Set.toList ms)
        ]
      BlockedOnProblems ps -> hsep
        [ prettyTCM q , " is not a legal rewrite rule, since"
        , "it is blocked on problem(s)", prettyList_ (map prettyTCM $ Set.toList ps)
        ]
      RequiresDefinitions qs -> hsep
        [ prettyTCM q , " is not a legal rewrite rule, since"
        , "it requires the definition(s) of", prettyList_ (map prettyTCM $ Set.toList qs)
        ]
      DoesNotTargetRewriteRelation -> hsep
        [ prettyTCM q , " does not target rewrite relation" ]
      BeforeFunctionDefinition -> hsep
        [ "Rewrite rule from function "
        , prettyTCM q
        , " cannot be added before the function definition"
        ]
      BeforeMutualFunctionDefinition r -> hsep
        [ "Rewrite rule from function "
        , prettyTCM q
        , " cannot be added before the definition of mutually defined"
        , prettyTCM r
        ]
      DuplicateRewriteRule ->
        "Rewrite rule " <+> prettyTCM q <+> " has already been added"

    ConfluenceCheckingIncompleteBecauseOfMeta f -> fsep
      [ "Confluence checking incomplete because the definition of"
      , prettyTCM f
      , text "contains unsolved metavariables."
      ]

    ConfluenceForCubicalNotSupported -> fsep $ pwords $
      "Confluence checking for --cubical is not yet supported, confluence checking might be incomplete"

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
        , [ prettyTCM v , "to" , prettyTCM rhou ]
        ]
      ]

    DuplicateRecordDirective dir ->
      "Ignoring duplicate record directive: " <+> pretty dir

    PragmaCompileErased bn qn -> fsep $ concat
      [ pwords "The backend"
      , [ text bn
        , "erases"
        , prettyTCM qn
        ]
      , pwords "so the COMPILE pragma will be ignored."
      ]

    PragmaCompileList -> fsep $ pwords
      "Ignoring GHC pragma for builtin lists; they always compile to Haskell lists."

    PragmaCompileMaybe -> fsep $ pwords
      "Ignoring GHC pragma for builtin MAYBE; it always compiles to Haskell Maybe."

    PragmaCompileUnparsable s -> fwords $ "Ignoring unparsable GHC pragma '" ++ s ++ "'"

    PragmaCompileWrong _x s -> fwords s

    PragmaCompileWrongName x amb -> hsep $ concat
      [ pwords "Cannot COMPILE"
      , [ pretty x ]
      , pwords "since it is"
      , case amb of
          YesAmbiguous xs -> [ "ambiguous:", pretty xs ]
          NotAmbiguous -> pwords "neither a defined symbol nor a constructor"
      ]

    PragmaExpectsDefinedSymbol pragma _x -> hsep $ concat
      [ pwords "Target of"
      , [ text pragma ]
      , pwords "pragma should be a defined symbol"
      ]

    PragmaExpectsUnambiguousConstructorOrFunction pragma _x amb -> hsep $ concat
      [ pwords "Target of"
      , [ text pragma ]
      , pwords "pragma should be"
      , case amb of
          YesAmbiguous xs -> pwords "unambiguous, but it resolves to:" ++ [ pretty xs ]
          NotAmbiguous -> pwords "a function, constructor, or projection"
      ]

    PragmaExpectsUnambiguousProjectionOrFunction pragma _x amb -> hsep $ concat
      [ pwords "Target of"
      , [ text pragma ]
      , pwords "pragma should be"
      , case amb of
          YesAmbiguous xs -> pwords "unambiguous, but it resolves to:" ++ [ pretty xs ]
          NotAmbiguous -> pwords "a function or projection"
      ]

    NoMain topLevelModule -> vcat
      [ fsep $ pwords "No main function defined in" ++ [prettyTCM topLevelModule <> "."]
      , fsep $ pwords "Use option --no-main to suppress this warning."
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
      , case patsyn of
          IsPatSyn -> pwords "pattern synonym"
          IsLHS    -> [ "constructor" ]
      ]

    PatternShadowsConstructor x c -> fsep $
      pwords "The pattern variable" ++ [prettyTCM x] ++
      pwords "has the same name as the constructor" ++ [prettyTCM c]

    PlentyInHardCompileTimeMode o -> fsep $
      pwords "Ignored use of" ++ [pretty o] ++
      pwords "in hard compile-time mode"

    RecordFieldWarning w -> prettyRecordFieldWarning w

    MissingTypeSignatureForOpaque name isOpaque -> vcat
        [ "Missing type signature for" <+> text what <+> "definition" <+> (prettyTCM name <> ".")
        , fsep $ pwords $
            "Types of " ++ what ++ " definitions are never inferred since this would leak " ++
            "information that should be " ++ what ++ "."
        ]
      where
        what = case isOpaque of
          TransparentDef -> "abstract"
          OpaqueDef _    -> "opaque"


    NotAffectedByOpaque -> fwords "Only function definitions can be marked opaque. This definition will be treated as transparent."

    UnfoldingWrongName x -> fsep $
      pwords "Name in unfolding clause should be unambiguous defined name:" ++ [prettyTCM x]

    UnfoldTransparentName qn -> fsep $
      pwords "The name" ++ [prettyTCM qn <> ","] ++ pwords "mentioned by an unfolding clause, does not belong to an opaque block. This has no effect."

    UselessOpaque -> "This `opaque` block has no effect."

    InvalidDisplayForm x reason -> fsep $ concat
        [ pwords "Ignoring invalid display form for"
        , [ prettyTCM x ]
        , if null reason then [] else "because" : pwords reason
        ]

    TooManyArgumentsToSort q args -> fsep $ concat
      [ pwords "Too many arguments given to sort"
      , [ prettyTCM q ]
      ]

    WithClauseProjectionFixityMismatch p0 o' q o -> fsep $ concat
        [ pwords "With clause pattern"
        , [ prettyA p0 ]
        , pwords "is not an instance of its parent pattern"
        , [ P.fsep <$> prettyTCMPatterns [q] ]
        , pwords "since the parent pattern is"
        , pwords $ prettyProjOrigin o
        , pwords "and the with clause pattern is"
        , pwords $ prettyProjOrigin o'
        ]
      where
        prettyProjOrigin ProjPrefix  = "a prefix projection"
        prettyProjOrigin ProjPostfix = "a postfix projection"
        prettyProjOrigin ProjSystem  = __IMPOSSIBLE__

    FaceConstraintCannotBeHidden ai -> fsep $
      pwords "Face constraint patterns cannot be" ++ [ pretty (getHiding ai), "arguments"]

    FaceConstraintCannotBeNamed x -> fsep $
      pwords "Ignoring name" ++ ["`" <> pretty x <> "`"] ++ pwords "given to face constraint pattern"

    CustomBackendWarning backend warn -> (text backend <> ":") <?> pure warn

{-# SPECIALIZE prettyRecordFieldWarning :: RecordFieldWarning -> TCM Doc #-}
prettyRecordFieldWarning :: MonadPretty m => RecordFieldWarning -> m Doc
prettyRecordFieldWarning = \case
  W.DuplicateFields xrs    -> prettyDuplicateFields $ map fst xrs
  W.TooManyFields q ys xrs -> prettyTooManyFields q ys $ map fst xrs

prettyDuplicateFields :: MonadPretty m => [C.Name] -> m Doc
prettyDuplicateFields xs = fsep $ concat
    [ pwords "Duplicate"
    , fields xs
    , punctuate comma (map pretty xs)
    , pwords "in record"
    ]
  where
  fields ys = P.singPlural ys [text "field"] [text "fields"]

{-# SPECIALIZE prettyTooManyFields :: QName -> [C.Name] -> [C.Name] -> TCM Doc  #-}
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

{-# SPECIALIZE prettyNotInScopeNames :: (Pretty a, HasRange a) => Bool -> (a -> TCM Doc) -> [a] -> TCM Doc #-}
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

{-# SPECIALIZE didYouMean :: (Pretty a, Pretty b) => [C.QName] -> (a -> b) -> a -> Maybe (TCM Doc) #-}
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
prettyTCWarnings = List.intercalate "\n" <.> map P.render <.> prettyTCWarnings'

prettyTCWarnings' :: [TCWarning] -> TCM [Doc]
prettyTCWarnings' = traverse prettyTCM . filterTCWarnings

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


-- | Turns warnings, if any, into errors.
tcWarningsToError :: [TCWarning] -> TCM ()
tcWarningsToError mws = case (unsolvedHoles, otherWarnings) of
   ([], [])                   -> return ()
   (_unsolvedHoles@(_:_), []) -> typeError SolvedButOpenHoles
   (_, ws@(_:_))              -> typeError $ NonFatalErrors ws
   where
   -- filter out unsolved interaction points for imported module so
   -- that we get the right error message (see test case Fail/Issue1296)
   (unsolvedHoles, otherWarnings) = List.partition (isUnsolvedIM . tcWarning) mws
   isUnsolvedIM UnsolvedInteractionMetas{} = True
   isUnsolvedIM _                          = False


-- | Depending which flags are set, one may happily ignore some
-- warnings.

applyFlagsToTCWarningsPreserving :: HasOptions m => Set WarningName -> [TCWarning] -> m [TCWarning]
applyFlagsToTCWarningsPreserving additionalKeptWarnings ws = do
  -- For some reason some SafeFlagPragma seem to be created multiple times.
  -- This is a way to collect all of them and remove duplicates.
  let pragmas w = case tcWarning w of { SafeFlagPragma ps -> ([w], ps); _ -> ([], []) }
  let sfp = case fmap List.nub (foldMap pragmas ws) of
              (TCWarning loc r w p b:_, sfp) ->
                 [TCWarning loc r (SafeFlagPragma sfp) p b]
              _                        -> []

  pragmaWarnings <- (^. warningSet) . optWarningMode <$> pragmaOptions
  let warnSet = Set.union pragmaWarnings additionalKeptWarnings

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

applyFlagsToTCWarnings :: HasOptions m => [TCWarning] -> m [TCWarning]
applyFlagsToTCWarnings = applyFlagsToTCWarningsPreserving Set.empty

{-# SPECIALIZE isBoundaryConstraint :: ProblemConstraint -> TCM (Maybe Range) #-}
isBoundaryConstraint :: (ReadTCState m, MonadTCM m) => ProblemConstraint -> m (Maybe Range)
isBoundaryConstraint c =
  enterClosure (theConstraint c) $ \case
    ValueCmp _ _ (MetaV mid xs) y | Just xs <- allApplyElims xs ->
      fmap g <$> liftTCM (isFaceConstraint mid xs)
    ValueCmp _ _ y (MetaV mid xs) | Just xs <- allApplyElims xs ->
      fmap g <$> liftTCM (isFaceConstraint mid xs)
    _ -> pure Nothing
  where
    g (a, _, _, _) = getRange a

{-# SPECIALIZE getAllUnsolvedWarnings :: TCM [TCWarning] #-}
getAllUnsolvedWarnings :: (ReadTCState m, MonadWarning m, MonadTCM m) => m [TCWarning]
getAllUnsolvedWarnings = do
  unsolvedInteractions <- getUnsolvedInteractionMetas

  allCons <- getAllConstraints
  unsolvedConstraints  <- filterM (fmap isNothing . isBoundaryConstraint) allCons
  interactionBoundary  <- catMaybes <$> traverse isBoundaryConstraint allCons

  unsolvedMetas        <- getUnsolvedMetas

  let checkNonEmpty c rs = c rs <$ guard (not $ null rs)

  mapM warning_ $ catMaybes
                [ checkNonEmpty UnsolvedInteractionMetas  unsolvedInteractions
                , checkNonEmpty UnsolvedMetaVariables     unsolvedMetas
                , checkNonEmpty UnsolvedConstraints       unsolvedConstraints
                , checkNonEmpty InteractionMetaBoundaries interactionBoundary
                ]

-- | Collect all warnings that have accumulated in the state.

{-# SPECIALIZE getAllWarnings :: WhichWarnings -> TCM [TCWarning] #-}
getAllWarnings :: (ReadTCState m, MonadWarning m, MonadTCM m) => WhichWarnings -> m [TCWarning]
getAllWarnings = getAllWarningsPreserving Set.empty

{-# SPECIALIZE getAllWarningsPreserving :: Set WarningName -> WhichWarnings -> TCM [TCWarning] #-}
getAllWarningsPreserving ::
  (ReadTCState m, MonadWarning m, MonadTCM m) => Set WarningName -> WhichWarnings -> m [TCWarning]
getAllWarningsPreserving keptWarnings ww = do
  unsolved            <- getAllUnsolvedWarnings
  collectedTCWarnings <- useTC stTCWarnings

  let showWarn w = classifyWarning w <= ww &&
                    not (null unsolved && onlyShowIfUnsolved w)

  fmap (filter (showWarn . tcWarning))
    $ applyFlagsToTCWarningsPreserving keptWarnings
    $ reverse $ unsolved ++ collectedTCWarnings

getAllWarningsOfTCErr :: TCErr -> TCM [TCWarning]
getAllWarningsOfTCErr err = case err of
  TypeError _ tcst cls -> case clValue cls of
    NonFatalErrors{} -> return []
    _ -> localTCState $ do
      putTC tcst
      ws <- getAllWarnings AllWarnings
      -- We filter out the unsolved(Metas/Constraints) to stay
      -- true to the previous error messages.
      return $ filter (not . isUnsolvedWarning . tcWarning) ws
  _ -> return []
