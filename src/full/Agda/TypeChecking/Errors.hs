{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Errors
    ( prettyError
    , PrettyTCM(..)
    , tcErrString
    , Warnings(..)
    , warningsToError
    ) where

import Control.Applicative ( (<$>) )
import Control.Monad.State
import Control.Monad.Error

import Data.List (nub)
import qualified Data.Map as Map (empty)

import System.FilePath

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Fixity
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as D
import Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract.Pretty as P
import qualified Agda.Syntax.Concrete.Pretty as P
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Scope.Base (ScopeInfo(..))
import Agda.Syntax.Scope.Monad (isDatatypeModule)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Pretty

import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Top level function
---------------------------------------------------------------------------

prettyError :: TCErr -> TCM String
prettyError err = liftTCM $ liftM show $
    prettyTCM err
    `catchError` \err' -> text "panic: error when printing error!" $$ prettyTCM err'
    `catchError` \err'' -> text "much panic: error when printing error from printing error!" $$ prettyTCM err''
    `catchError` \err''' -> fsep (
	pwords "total panic: error when printing error from printing error from printing error." ++
	pwords "I give up! Approximations of errors:" )
	$$ vcat (map (text . tcErrString) [err,err',err'',err'''])

---------------------------------------------------------------------------
-- * Warnings
---------------------------------------------------------------------------

-- | Warnings.
--
-- Invariant: The fields are never empty at the same time.

data Warnings = Warnings
  { terminationProblems   :: [TerminationError]
    -- ^ Termination checking problems are not reported if
    -- 'optTerminationCheck' is 'False'.
  , unsolvedMetaVariables :: [Range]
    -- ^ Meta-variable problems are reported as type errors unless
    -- 'optAllowUnsolved' is 'True'.
  , unsolvedConstraints   :: Constraints
    -- ^ Same as 'unsolvedMetaVariables'.
  }

-- | Turns warnings into an error. Even if several errors are possible
-- only one is raised.

warningsToError :: Warnings -> TypeError
warningsToError (Warnings [] [] [])    = __IMPOSSIBLE__
warningsToError (Warnings _ w@(_:_) _) = UnsolvedMetas w
warningsToError (Warnings _ _ w@(_:_)) = UnsolvedConstraints w
warningsToError (Warnings w@(_:_) _ _) = TerminationCheckFailed w

---------------------------------------------------------------------------
-- * Helpers
---------------------------------------------------------------------------

sayWhere :: HasRange a => a -> TCM Doc -> TCM Doc
sayWhere x d = text (show $ getRange x) $$ d

sayWhen :: Range -> Maybe (Closure Call) -> TCM Doc -> TCM Doc
sayWhen r Nothing   m = sayWhere r m
sayWhen r (Just cl) m = sayWhere r (m $$ prettyTCM cl)

panic :: String -> TCM Doc
panic s = fwords $ "Panic: " ++ s

nameWithBinding :: QName -> TCM Doc
nameWithBinding q =
  sep [ prettyTCM q, text "bound at", text (show r) ]
  where
    r = nameBindingSite $ qnameName q

tcErrString :: TCErr -> String
tcErrString err = show (getRange err) ++ " " ++ case err of
    TypeError _ cl  -> errorString $ clValue cl
    Exception r s   -> show r ++ " " ++ s
    IOException r e -> show r ++ " " ++ show e
    PatternErr _    -> "PatternErr"
    {- AbortAssign _   -> "AbortAssign" -- UNUSED -}

errorString :: TypeError -> String
errorString err = case err of
    AmbiguousModule{}                        -> "AmbiguousModule"
    AmbiguousName{}                          -> "AmbiguousName"
    AmbiguousParseForApplication{}           -> "AmbiguousParseForApplication"
    AmbiguousParseForLHS{}                   -> "AmbiguousParseForLHS"
--    AmbiguousParseForPatternSynonym{}        -> "AmbiguousParseForPatternSynonym"
    AmbiguousTopLevelModuleName {}           -> "AmbiguousTopLevelModuleName"
    BothWithAndRHS                           -> "BothWithAndRHS"
    BuiltinInParameterisedModule{}           -> "BuiltinInParameterisedModule"
    BuiltinMustBeConstructor{}               -> "BuiltinMustBeConstructor"
    ClashingDefinition{}                     -> "ClashingDefinition"
    ClashingFileNamesFor{}                   -> "ClashingFileNamesFor"
    ClashingImport{}                         -> "ClashingImport"
    ClashingModule{}                         -> "ClashingModule"
    ClashingModuleImport{}                   -> "ClashingModuleImport"
    CompilationError{}                       -> "CompilationError"
    ConstructorPatternInWrongDatatype{}      -> "ConstructorPatternInWrongDatatype"
    CoverageFailure{}                        -> "CoverageFailure"
    CoverageCantSplitOn{}                    -> "CoverageCantSplitOn"
    CoverageCantSplitIrrelevantType{}        -> "CoverageCantSplitIrrelevantType"
    CoverageCantSplitType{}                  -> "CoverageCantSplitType"
    CyclicModuleDependency{}                 -> "CyclicModuleDependency"
    DataMustEndInSort{}                      -> "DataMustEndInSort"
-- UNUSED:    DataTooManyParameters{}                  -> "DataTooManyParameters"
    DifferentArities                         -> "DifferentArities"
    DoesNotConstructAnElementOf{}            -> "DoesNotConstructAnElementOf"
    DuplicateBuiltinBinding{}                -> "DuplicateBuiltinBinding"
    DuplicateConstructors{}                  -> "DuplicateConstructors"
    DuplicateFields{}                        -> "DuplicateFields"
    DuplicateImports{}                       -> "DuplicateImports"
    FieldOutsideRecord                       -> "FieldOutsideRecord"
    FileNotFound{}                           -> "FileNotFound"
    GenericError{}                           -> "GenericError"
    GenericDocError{}                        -> "GenericDocError"
    IFSNoCandidateInScope{}                  -> "IFSNoCandidateInScope"
    IlltypedPattern{}                        -> "IlltypedPattern"
    IncompletePatternMatching{}              -> "IncompletePatternMatching"
    IndexVariablesNotDistinct{}              -> "IndexVariablesNotDistinct"
    IndicesFreeInParameters{}                -> "IndicesFreeInParameters"
    IndicesNotConstructorApplications{}      -> "IndicesNotConstructorApplications"
    InternalError{}                          -> "InternalError"
    InvalidPattern{}                         -> "InvalidPattern"
    LocalVsImportedModuleClash{}             -> "LocalVsImportedModuleClash"
    MetaCannotDependOn{}                     -> "MetaCannotDependOn"
    MetaOccursInItself{}                     -> "MetaOccursInItself"
    ModuleArityMismatch{}                    -> "ModuleArityMismatch"
    ModuleDefinedInOtherFile {}              -> "ModuleDefinedInOtherFile"
    ModuleDoesntExport{}                     -> "ModuleDoesntExport"
    ModuleNameDoesntMatchFileName {}         -> "ModuleNameDoesntMatchFileName"
    NeedOptionCopatterns{}                   -> "NeedOptionCopatterns"
    NoBindingForBuiltin{}                    -> "NoBindingForBuiltin"
    NoParseForApplication{}                  -> "NoParseForApplication"
    NoParseForLHS{}                          -> "NoParseForLHS"
--    NoParseForPatternSynonym{}               -> "NoParseForPatternSynonym"
    NoRHSRequiresAbsurdPattern{}             -> "NoRHSRequiresAbsurdPattern"
    NotInductive {}                          -> "NotInductive"
    AbsurdPatternRequiresNoRHS{}             -> "AbsurdPatternRequiresNoRHS"
    NoSuchBuiltinName{}                      -> "NoSuchBuiltinName"
    NoSuchModule{}                           -> "NoSuchModule"
    NoSuchPrimitiveFunction{}                -> "NoSuchPrimitiveFunction"
    NotAModuleExpr{}                         -> "NotAModuleExpr"
    NotAProperTerm                           -> "NotAProperTerm"
    SetOmegaNotValidType                     -> "SetOmegaNotValidType"
    NotAValidLetBinding{}                    -> "NotAValidLetBinding"
    NotAnExpression{}                        -> "NotAnExpression"
    NotImplemented{}                         -> "NotImplemented"
    NotSupported{}                           -> "NotSupported"
    NotInScope{}                             -> "NotInScope"
    NotLeqSort{}                             -> "NotLeqSort"
    NotStrictlyPositive{}                    -> "NotStrictlyPositive"
    NothingAppliedToHiddenArg{}              -> "NothingAppliedToHiddenArg"
    NothingAppliedToInstanceArg{}            -> "NothingAppliedToInstanceArg"
    OverlappingProjects {}                   -> "OverlappingProjects"
    PatternShadowsConstructor {}             -> "PatternShadowsConstructor"
    PatternSynonymArityMismatch {}           -> "PatternSynonymArityMismatch"
    PropMustBeSingleton                      -> "PropMustBeSingleton"
    RepeatedVariablesInPattern{}             -> "RepeatedVariablesInPattern"
    SafeFlagPostulate{}                      -> "SafeFlagPostulate"
    SafeFlagPragma{}                         -> "SafeFlagPragma"
    SafeFlagNoTerminationCheck{}             -> "SafeFlagNoTerminationCheck"
    SafeFlagPrimTrustMe{}                    -> "SafeFlagPrimTrustMe"
    ShadowedModule{}                         -> "ShadowedModule"
    ShouldBeASort{}                          -> "ShouldBeASort"
    ShouldBeApplicationOf{}                  -> "ShouldBeApplicationOf"
    ShouldBeAppliedToTheDatatypeParameters{} -> "ShouldBeAppliedToTheDatatypeParameters"
    ShouldBeEmpty{}                          -> "ShouldBeEmpty"
    ShouldBePi{}                             -> "ShouldBePi"
    ShouldBeRecordType{}                     -> "ShouldBeRecordType"
    ShouldBeRecordPattern{}                  -> "ShouldBeRecordPattern"
    ShouldEndInApplicationOfTheDatatype{}    -> "ShouldEndInApplicationOfTheDatatype"
    TerminationCheckFailed{}                 -> "TerminationCheckFailed"
    TooFewFields{}                           -> "TooFewFields"
    TooManyArgumentsInLHS{}                  -> "TooManyArgumentsInLHS"
    TooManyFields{}                          -> "TooManyFields"
    SplitOnIrrelevant{}                      -> "SplitOnIrrelevant"
    DefinitionIsIrrelevant{}                 -> "DefinitionIsIrrelevant"
    VariableIsIrrelevant{}                   -> "VariableIsIrrelevant"
    UnequalBecauseOfUniverseConflict{}       -> "UnequalBecauseOfUniverseConflict"
    UnequalRelevance{}                       -> "UnequalRelevance"
    UnequalHiding{}                          -> "UnequalHiding"
    UnequalLevel{}                           -> "UnequalLevel"
    UnequalSorts{}                           -> "UnequalSorts"
    UnequalTerms{}                           -> "UnequalTerms"
    UnequalTypes{}                           -> "UnequalTypes"
    UnequalTelescopes{}                      -> "UnequalTelescopes"
    UnequalColors{}                          -> "UnequalTelescopes"
    HeterogeneousEquality{}                  -> "HeterogeneousEquality"
    UnexpectedWithPatterns{}                 -> "UnexpectedWithPatterns"
    UninstantiatedDotPattern{}               -> "UninstantiatedDotPattern"
    UninstantiatedModule{}                   -> "UninstantiatedModule"
    UnreachableClauses{}                     -> "UnreachableClauses"
    UnsolvedConstraints{}                    -> "UnsolvedConstraints"
    UnsolvedMetas{}                          -> "UnsolvedMetas"
    UnusedVariableInPatternSynonym           -> "UnusedVariableInPatternSynonym"
    WithClausePatternMismatch{}              -> "WithClausePatternMismatch"
    WrongHidingInApplication{}               -> "WrongHidingInApplication"
    WrongHidingInLHS{}                       -> "WrongHidingInLHS"
    WrongHidingInLambda{}                    -> "WrongHidingInLambda"
    WrongIrrelevanceInLambda{}               -> "WrongIrrelevanceInLambda"
    WrongNumberOfConstructorArguments{}      -> "WrongNumberOfConstructorArguments"

instance PrettyTCM TCErr where
    prettyTCM err = case err of
	TypeError s e -> localState $ do
	    put s
	    sayWhen (envRange $ clEnv e) (envCall $ clEnv e) $ prettyTCM e
	Exception r s   -> sayWhere r $ fwords s
	IOException r e -> sayWhere r $ fwords $ show e
	PatternErr _    -> sayWhere err $ panic "uncaught pattern violation"
	{- AbortAssign _   -> sayWhere err $ panic "uncaught aborted assignment" -- UNUSED -}

instance PrettyTCM TypeError where
    prettyTCM err = do
	case err of
	    InternalError s  -> panic s
	    NotImplemented s -> fwords $ "Not implemented: " ++ s
	    NotSupported s -> fwords $ "Not supported: " ++ s
	    CompilationError s -> sep [fwords "Compilation error:", text s]
	    GenericError s   -> fwords s
	    GenericDocError d   -> return d
	    TerminationCheckFailed because ->
              fwords "Termination checking failed for the following functions:"
              $$ (nest 2 $
                    fsep (punctuate comma (map (text . show . qnameName)
                                               (concatMap termErrFunctions because))))
              $$ fwords "Problematic calls:"
              $$ (nest 2 $ vcat $
                    map (\c -> let call = text (callInfoCall c) in
                               case show (callInfoRange c) of
                                 "" -> call
                                 r  -> call $$ nest 2 (text "(at" <+> text r <> text ")"))
                        (nub $ concatMap termErrCalls because))
	    PropMustBeSingleton -> fwords
		"Datatypes in Prop must have at most one constructor when proof irrelevance is enabled"
	    DataMustEndInSort t -> fsep $
		pwords "The type of a datatype must end in a sort."
		++ [prettyTCM t] ++ pwords "isn't a sort."
{- UNUSED:
	    DataTooManyParameters -> fsep $ pwords "Too many parameters given to data type."
-}
	    ShouldEndInApplicationOfTheDatatype t -> fsep $
		pwords "The target of a constructor must be the datatype applied to its parameters,"
		++ [prettyTCM t] ++ pwords "isn't"
	    ShouldBeAppliedToTheDatatypeParameters s t -> fsep $
		pwords "The target of the constructor should be" ++ [prettyTCM s] ++
		pwords "instead of" ++ [prettyTCM t]
	    ShouldBeApplicationOf t q -> fsep $
		pwords "The pattern constructs an element of" ++ [prettyTCM q] ++
		pwords "which is not the right datatype"
	    ShouldBeRecordType t -> fsep $
		pwords "Expected non-abstract record type, found " ++ [prettyTCM t]
	    ShouldBeRecordPattern p -> fsep $
		pwords "Expected record pattern" -- ", found " ++ [prettyTCM p]
	    DifferentArities ->
		fwords "The number of arguments in the defining equations differ"
	    WrongHidingInLHS t -> do
		fwords "Found an implicit argument where an explicit argument was expected"
	    WrongHidingInLambda t -> do
		fwords "Found an implicit lambda where an explicit lambda was expected"
	    WrongIrrelevanceInLambda t -> do
		fwords "Found an irrelevant lambda where a relevant lambda was expected"
	    WrongHidingInApplication t -> do
		fwords "Found an implicit application where an explicit application was expected"
            NotInductive t -> fsep $
              [prettyTCM t] ++ pwords "is not an inductive data type"
            UninstantiatedDotPattern e -> fsep $
              pwords "Failed to infer the value of dotted pattern"
            IlltypedPattern p a -> fsep $
              pwords "Type mismatch"
            TooManyArgumentsInLHS a -> fsep $
              pwords "Left hand side gives too many arguments to a function of type" ++ [prettyTCM a]
            WrongNumberOfConstructorArguments c expect given -> fsep $
              pwords "The constructor" ++ [prettyTCM c] ++ pwords "expects" ++
              [text (show expect)] ++ pwords "arguments, but has been given" ++ [text (show given)]
            DoesNotConstructAnElementOf c t -> fsep $
              pwords "the constructor" ++ [prettyTCM c] ++
              pwords "does not construct an element of" ++ [prettyTCM t]
            ConstructorPatternInWrongDatatype c d -> fsep $
              [prettyTCM c] ++ pwords "is not a constructor of the datatype" ++ [prettyTCM d]
            IndicesNotConstructorApplications is ->
              fwords "The indices"
              $$ nest 2 (vcat $ map prettyTCM is)
              $$ fsep (pwords "are not constructors (or literals) applied to variables" ++
                       pwords "(note that parameters count as constructor arguments)")
            IndexVariablesNotDistinct vs is ->
              fwords "The variables"
              $$ nest 2 (vcat $ map (\v -> prettyTCM (I.Var v [])) vs)
              $$ fwords "in the indices"
              $$ nest 2 (vcat $ map prettyTCM is)
              $$ fwords "are not distinct (note that parameters count as constructor arguments)"
            IndicesFreeInParameters vs indices pars ->
              fwords "The variables"
              $$ nest 2 (vcat $ map (\v -> prettyTCM (I.Var v [])) vs)
              $$ fwords "which are used (perhaps as constructor parameters) in the index expressions"
              $$ nest 2 (vcat $ map prettyTCM indices)
              $$ fwords "are free in the parameters"
              $$ nest 2 (vcat $ map prettyTCM pars)
            ShadowedModule x [] -> __IMPOSSIBLE__
            ShadowedModule x ms@(m : _) -> fsep $
              pwords "Duplicate definition of module" ++ [prettyTCM x <> text "."] ++
              pwords "Previous definition of" ++ [help m] ++ pwords "module" ++ [prettyTCM x] ++
              pwords "at" ++ [text $ show r]
              where
                help m = do
                  b <- isDatatypeModule m
                  if b then text "datatype" else empty

                r = case [ r | r <- map (defSiteOfLast . mnameToList) ms
                             , r /= noRange ] of
                      []    -> noRange
                      r : _ -> r

                defSiteOfLast [] = noRange
                defSiteOfLast ns = nameBindingSite (last ns)
            ModuleArityMismatch m EmptyTel args -> fsep $
              pwords "The module" ++ [prettyTCM m] ++
              pwords "is not parameterized, but is being applied to arguments"
            ModuleArityMismatch m tel@(ExtendTel _ _) args -> fsep $
              pwords "The arguments to " ++ [prettyTCM m] ++ pwords "does not fit the telescope" ++
	      [prettyTCM tel]
            ShouldBeEmpty t [] -> fsep $
		[prettyTCM t] ++ pwords "should be empty, but that's not obvious to me"
	    ShouldBeEmpty t ps -> fsep (
		[prettyTCM t] ++
                pwords "should be empty, but the following constructor patterns are valid:"
              ) $$ nest 2 (vcat $ map (showPat 0) ps)

	    ShouldBeASort t -> fsep $
		[prettyTCM t] ++ pwords "should be a sort, but it isn't"
	    ShouldBePi t -> fsep $
		[prettyTCM t] ++ pwords "should be a function type, but it isn't"
	    NotAProperTerm ->
		fwords "Found a malformed term"
	    SetOmegaNotValidType ->
		fwords "Setω is not a valid type"
            SplitOnIrrelevant p t -> fsep $
                pwords "Cannot pattern match" ++ [prettyA p] ++
                pwords "against irrelevant type" ++ [prettyTCM t]
            DefinitionIsIrrelevant x -> fsep $
                text "Identifier" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"
            VariableIsIrrelevant x -> fsep $
                text "Variable" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"
	    UnequalBecauseOfUniverseConflict cmp s t -> fsep $
		[prettyTCM s, notCmp cmp, prettyTCM t, text "because this would result in an invalid use of Setω" ]
 	    UnequalTerms cmp s t a -> fsep $
		[prettyTCM s, notCmp cmp, prettyTCM t] ++ pwords "of type" ++ [prettyTCM a]
	    UnequalLevel cmp s t -> fsep $
		[prettyTCM s, notCmp cmp, prettyTCM t]
	    UnequalTelescopes cmp a b -> fsep $
		[prettyTCM a, notCmp cmp, prettyTCM b]
	    UnequalTypes cmp a b -> fsep $
		[prettyTCM a, notCmp cmp, prettyTCM b]
            UnequalColors a b -> error "TODO guilhem 4"
	    HeterogeneousEquality u a v b -> fsep $
                pwords "Refuse to solve heterogeneous constraint" ++
                [prettyTCM u] ++ pwords ":" ++ [prettyTCM a] ++ pwords "=?=" ++
                [prettyTCM v] ++ pwords ":" ++ [prettyTCM b]
	    UnequalRelevance cmp a b -> fsep $
		[prettyTCM a, notCmp cmp, prettyTCM b] ++
-- Andreas 2010-09-21 to reveal Forced annotations, print also uglily
--		[text $ show a, notCmp cmp, text $ show b] ++
		pwords "because one is a relevant function type and the other is an irrelevant function type"
	    UnequalHiding a b -> fsep $
		[prettyTCM a, text "!=", prettyTCM b] ++
		pwords "because one is an implicit function type and the other is an explicit function type"
	    UnequalSorts s1 s2 -> fsep $
		[prettyTCM s1, text "!=", prettyTCM s2]
	    NotLeqSort s1 s2 -> fsep $
		pwords "The type of the constructor does not fit in the sort of the datatype, since"
		++ [prettyTCM s1] ++ pwords "is not less or equal than" ++ [prettyTCM s2]
	    TooFewFields r xs -> fsep $
		pwords "Missing fields" ++ punctuate comma (map pretty xs) ++
		pwords "in an element of the record" ++ [prettyTCM r]
	    TooManyFields r xs -> fsep $
		pwords "The record type" ++ [prettyTCM r] ++
		pwords "does not have the fields" ++ punctuate comma (map pretty xs)
	    DuplicateConstructors xs -> fsep $
		pwords "Duplicate constructors" ++ punctuate comma (map pretty xs) ++
		pwords "in datatype"
	    DuplicateFields xs -> fsep $
		pwords "Duplicate fields" ++ punctuate comma (map pretty xs) ++
		pwords "in record"
            UnexpectedWithPatterns ps -> fsep $
              pwords "Unexpected with patterns" ++ (punctuate (text " |") $ map prettyA ps)
            WithClausePatternMismatch p q -> fsep $
              pwords "With clause pattern" ++ [prettyA p] ++
              pwords "is not an instance of its parent pattern" -- TODO: pretty for internal patterns
	    MetaCannotDependOn m ps i -> fsep $
		    pwords "The metavariable" ++ [prettyTCM $ MetaV m []] ++ pwords "cannot depend on" ++ [pvar i] ++
		    pwords "because it" ++ deps
		where
		    pvar i = prettyTCM $ I.Var i []
		    deps = case map pvar ps of
			[]  -> pwords "does not depend on any variables"
			[x] -> pwords "only depends on the variable" ++ [x]
			xs  -> pwords "only depends on the variables" ++ punctuate comma xs

	    MetaOccursInItself m -> fsep $
		pwords "Cannot construct infinite solution of metavariable" ++ [prettyTCM $ MetaV m []]
            BuiltinMustBeConstructor s e -> fsep $
                [prettyA e] ++ pwords "must be a constructor in the binding to builtin" ++ [text s]
	    NoSuchBuiltinName s -> fsep $
		pwords "There is no built-in thing called" ++ [text s]
	    DuplicateBuiltinBinding b x y -> fsep $
		pwords "Duplicate binding for built-in thing" ++ [text b <> comma] ++
		pwords "previous binding to" ++ [prettyTCM x]
	    NoBindingForBuiltin x -> fsep $
		pwords "No binding for builtin thing" ++ [text x <> comma] ++
		pwords ("use {-# BUILTIN " ++ x ++ " name #-} to bind it to 'name'")
	    NoSuchPrimitiveFunction x -> fsep $
		pwords "There is no primitive function called" ++ [text x]
	    BuiltinInParameterisedModule x -> fwords $
		"The BUILTIN pragma cannot appear inside a bound context " ++
		"(for instance, in a parameterised module or as a local declaration)"
	    NoRHSRequiresAbsurdPattern ps -> fwords $
		"The right-hand side can only be omitted if there " ++
		"is an absurd pattern, () or {}, in the left-hand side."
	    AbsurdPatternRequiresNoRHS ps -> fwords $
		"The right-hand side must be omitted if there " ++
		"is an absurd pattern, () or {}, in the left-hand side."
	    LocalVsImportedModuleClash m -> fsep $
		pwords "The module" ++ [text $ show m] ++
		pwords "can refer to either a local module or an imported module"
	    UnsolvedMetas rs ->
		fsep ( pwords "Unsolved metas at the following locations:" )
		$$ nest 2 (vcat $ map (text . show) rs)
	    UnsolvedConstraints cs ->
		fsep ( pwords "Failed to solve the following constraints:" )
		$$ nest 2 (vcat $ map prettyConstraint cs)
              where prettyConstraint :: ProblemConstraint -> TCM Doc
                    prettyConstraint c = f (prettyTCM c)
                      where s   = show (getRange c)
                            f d = if null s then d else d $$ nest 4 (text ("[ at " ++ s ++ " ]"))
	    CyclicModuleDependency ms ->
		fsep (pwords "cyclic module dependency:")
		$$ nest 2 (vcat $ map pretty ms)
	    FileNotFound x files ->
		fsep ( pwords "Failed to find source of module" ++ [pretty x] ++
		       pwords "in any of the following locations:"
		     ) $$ nest 2 (vcat $ map (text . filePath) files)
            OverlappingProjects f m1 m2 ->
	        fsep ( pwords "The file" ++ [text (filePath f)] ++
                       pwords "can be accessed via several project roots. Both" ++
                       [pretty m1] ++ pwords "and" ++ [pretty m2] ++
                       pwords "point to this file."
                     )
	    AmbiguousTopLevelModuleName x files ->
		fsep ( pwords "Ambiguous module name. The module name" ++
                       [pretty x] ++
		       pwords "could refer to any of the following files:"
		     ) $$ nest 2 (vcat $ map (text . filePath) files)
	    ClashingFileNamesFor x files ->
		fsep ( pwords "Multiple possible sources for module" ++ [text $ show x] ++
		       pwords "found:"
		     ) $$ nest 2 (vcat $ map (text . filePath) files)
            ModuleDefinedInOtherFile mod file file' -> fsep $
              pwords "You tried to load" ++ [text (filePath file)] ++
              pwords "which defines the module" ++ [pretty mod <> text "."] ++
              pwords "However, according to the include path this module should" ++
              pwords "be defined in" ++ [text (filePath file') <> text "."]
	    ModuleNameDoesntMatchFileName given files ->
              fsep (pwords "The name of the top level module does not match the file name. The module" ++
                   [ pretty given ] ++ pwords "should be defined in one of the following files:")
	      $$ nest 2 (vcat $ map (text . filePath) files)
            BothWithAndRHS -> fsep $
              pwords "Unexpected right hand side"
	    NotInScope xs ->
		fsep (pwords "Not in scope:") $$ nest 2 (vcat $ map name xs)
		where
                  name x = fsep [ pretty x, text "at" <+> text (show $ getRange x), suggestion (show x) ]
                  suggestion s
                    | elem ':' s    = parens $ text "did you forget space around the ':'?"
                    | elem "->" two = parens $ text "did you forget space around the '->'?"
                    | otherwise     = empty
                    where
                      two = zipWith (\a b -> [a,b]) s (tail s)
	    NoSuchModule x -> fsep $
		pwords "No such module" ++ [pretty x]
	    AmbiguousName x ys -> vcat
	      [ fsep $ pwords "Ambiguous name" ++ [pretty x <> text "."] ++
		       pwords "It could refer to any one of"
	      , nest 2 $ vcat $ map nameWithBinding ys
	      ]
	    AmbiguousModule x ys -> vcat
	      [ fsep $ pwords "Ambiguous module name" ++ [pretty x <> text "."] ++
		       pwords "It could refer to any one of"
	      , nest 2 $ vcat $ map help ys
	      ]
              where
                help :: ModuleName -> TCM Doc
                help m = do
                  b <- isDatatypeModule m
                  sep [prettyTCM m, if b then text "(datatype module)" else empty]
	    UninstantiatedModule x -> fsep (
		    pwords "Cannot access the contents of the parameterised module" ++ [pretty x <> text "."] ++
		    pwords "To do this the module first has to be instantiated. For instance:"
		) $$ nest 2 (hsep [ text "module", pretty x <> text "'", text "=", pretty x, text "e1 .. en" ])
	    ClashingDefinition x y -> fsep $
		pwords "Multiple definitions of" ++ [pretty x <> text "."] ++
		pwords "Previous definition at" ++ [text $ show $ nameBindingSite $ qnameName y]
	    ClashingModule m1 m2 -> fsep $
		pwords "The modules" ++ [prettyTCM m1, text "and", prettyTCM m2] ++ pwords "clash."
	    ClashingImport x y -> fsep $
		pwords "Import clash between" ++ [pretty x, text "and", prettyTCM y]
	    ClashingModuleImport x y -> fsep $
		pwords "Module import clash between" ++ [pretty x, text "and", prettyTCM y]
	    PatternShadowsConstructor x c -> fsep $
                pwords "The pattern variable" ++ [prettyTCM x] ++
                pwords "has the same name as the constructor" ++ [prettyTCM c]
            DuplicateImports m xs -> fsep $
                pwords "Ambiguous imports from module" ++ [pretty m] ++ pwords "for" ++
                punctuate comma (map pretty xs)
	    ModuleDoesntExport m xs -> fsep $
		pwords "The module" ++ [pretty m] ++ pwords "doesn't export the following:" ++
		punctuate comma (map pretty xs)
	    NotAModuleExpr e -> fsep $
		pwords "The right-hand side of a module definition must have the form 'M e1 .. en'" ++
		pwords "where M is a module name. The expression" ++ [pretty e, text "doesn't."]
            FieldOutsideRecord -> fsep $
              pwords "Field appearing outside record declaration."
            InvalidPattern p -> fsep $
              pretty p : pwords "is not a valid pattern"
	    RepeatedVariablesInPattern xs -> fsep $
	      pwords "Repeated variables in left hand side:" ++ map pretty xs
	    NotAnExpression e -> fsep $
		[pretty e] ++ pwords "is not a valid expression."
	    NotAValidLetBinding nd -> fwords $
		"Not a valid let-declaration"
	    NothingAppliedToHiddenArg e	-> fsep $
		[pretty e] ++ pwords "cannot appear by itself. It needs to be the argument to" ++
		pwords "a function expecting an implicit argument."
	    NothingAppliedToInstanceArg e -> fsep $
		[pretty e] ++ pwords "cannot appear by itself. It needs to be the argument to" ++
		pwords "a function expecting an instance argument."
	    NoParseForApplication es -> fsep $
		pwords "Could not parse the application" ++ [pretty $ C.RawApp noRange es]
	    AmbiguousParseForApplication es es' -> fsep (
		    pwords "Don't know how to parse" ++ [pretty (C.RawApp noRange es) <> text "."] ++
		    pwords "Could mean any one of:"
		) $$ nest 2 (vcat $ map pretty es')
            UnusedVariableInPatternSynonym -> fsep $
                pwords "Unused variable in pattern synonym."
            PatternSynonymArityMismatch x -> fsep $
                pwords "Arity mismatch when using pattern synonym" ++ [prettyTCM x]
	    NoParseForLHS IsLHS p -> fsep $
		pwords "Could not parse the left-hand side" ++ [pretty p]
	    NoParseForLHS IsPatSyn p -> fsep $
		pwords "Could not parse the pattern synonym" ++ [pretty p]
{- UNUSED
	    NoParseForPatternSynonym p -> fsep $
		pwords "Could not parse the pattern synonym" ++ [pretty p]
-}
	    AmbiguousParseForLHS lhsOrPatSyn p ps -> fsep (
		    pwords "Don't know how to parse" ++ [pretty p <> text "."] ++
		    pwords "Could mean any one of:"
		) $$ nest 2 (vcat $ map pretty ps)
{- UNUSED
	    AmbiguousParseForPatternSynonym p ps -> fsep (
		    pwords "Don't know how to parse" ++ [pretty p <> text "."] ++
		    pwords "Could mean any one of:"
		) $$ nest 2 (vcat $ map pretty ps)
-}
	    IncompletePatternMatching v args -> fsep $
		pwords "Incomplete pattern matching for" ++ [prettyTCM v <> text "."] ++
		pwords "No match for" ++ map prettyTCM args
            UnreachableClauses f pss -> fsep $
                pwords "Unreachable" ++ pwords (plural (length pss) "clause")
                where
                  plural 1 thing = thing
                  plural n thing = thing ++ "s"
            CoverageFailure f pss -> fsep (
                pwords "Incomplete pattern matching for" ++ [prettyTCM f <> text "."] ++
                pwords "Missing cases:") $$ nest 2 (vcat $ map display pss)
                where
                  display ps = do
                    ps <- nicify f ps
                    prettyTCM f <+> fsep (map showArg ps)

                  nicify f ps = do
                    showImp <- showImplicitArguments
                    if showImp
                      then return ps
                      else return ps  -- TODO: remove implicit arguments which aren't constructors

            CoverageCantSplitOn c tel cIxs gIxs -> inContext [] $ addCtxTel tel $ vcat
              [ fsep $ pwords "Cannot decide whether there should be a case for the constructor" ++ [prettyTCM c <> text ","] ++
                       pwords "since the unification gets stuck on unifying the inferred indices"
              , nest 2 $ prettyTCM cIxs
              , fsep $ pwords "with the expected indices"
              , nest 2 $ prettyTCM gIxs ]

            CoverageCantSplitIrrelevantType a -> fsep $
              pwords "Cannot split on argument of irrelevant datatype" ++ [prettyTCM a]

            CoverageCantSplitType a -> fsep $
              pwords "Cannot split on argument of non-datatype" ++ [prettyTCM a]

	    NotStrictlyPositive d ocs -> fsep $
		pwords "The datatype" ++ [prettyTCM d] ++ pwords "is not strictly positive, because"
		++ prettyOcc "it" ocs
		where
		    prettyOcc _ [] = []
		    prettyOcc it (OccCon d c r : ocs) = concat
			[ pwords it, pwords "occurs", prettyR r
			, pwords "in the constructor", [prettyTCM c], pwords "of"
			, [prettyTCM d <> com ocs], prettyOcc "which" ocs
			]
		    prettyOcc it (OccClause f n r : ocs) = concat
			[ pwords it, pwords "occurs", prettyR r
			, pwords "in the", [th n], pwords "clause of"
			, [prettyTCM f <> com ocs], prettyOcc "which" ocs
			]
		    prettyR NonPositively = pwords "negatively"
		    prettyR (ArgumentTo i q) =
			pwords "as the" ++ [th i] ++
			pwords "argument to" ++ [prettyTCM q]
		    th 0 = text "first"
		    th 1 = text "second"
		    th 2 = text "third"
		    th n = text (show $ n - 1) <> text "th"

		    com []    = empty
		    com (_:_) = comma
            IFSNoCandidateInScope t -> fsep $
                pwords "No variable of type" ++ [prettyTCM t] ++ pwords "was found in scope."
            SafeFlagPostulate e -> fsep $
                pwords "Cannot postulate" ++ [pretty e] ++ pwords "with safe flag"
            SafeFlagPragma xs ->
                let plural | length xs == 1 = ""
                           | otherwise      = "s"
                in fsep $ [fwords ("Cannot set OPTION pragma" ++ plural)]
                          ++ map text xs ++ [fwords "with safe flag."]
            SafeFlagNoTerminationCheck -> fsep (pwords "Cannot use NO_TERMINATION_CHECK pragma with safe flag.")
            SafeFlagPrimTrustMe -> fsep (pwords "Cannot use primTrustMe with safe flag")
            NeedOptionCopatterns -> fsep (pwords "Option --copatterns needed to enable destructor patterns")
          where
            mpar n args
              | n > 0 && not (null args) = parens
              | otherwise                = id

            showArg :: I.Arg I.Pattern -> TCM Doc
            showArg (Common.Arg info x) = case argInfoHiding info of
                    Hidden -> braces $ showPat 0 x
                    Instance -> dbraces $ showPat 0 x
                    NotHidden -> showPat 1 x

            showPat :: Integer -> I.Pattern -> TCM Doc
            showPat _ (I.VarP _)        = text "_"
            showPat _ (I.DotP _)        = text "._"
            showPat n (I.ConP c _ args) = mpar n args $ prettyTCM c <+> fsep (map showArg args)
            showPat _ (I.LitP l)        = text (show l)

notCmp :: Comparison -> TCM Doc
notCmp cmp = text $ "!" ++ show cmp


instance PrettyTCM Call where
    prettyTCM c = case c of
	CheckClause t cl _  -> fsep $
	    pwords "when checking that the clause"
	    ++ [P.prettyA cl] ++ pwords "has type" ++ [prettyTCM t]
	CheckPattern p tel t _ -> addCtxTel tel $ fsep $
	    pwords "when checking that the pattern"
	    ++ [prettyA p] ++ pwords "has type" ++ [prettyTCM t]
	CheckLetBinding b _ -> fsep $
	    pwords "when checking the let binding" ++ [P.prettyA b]
	InferExpr e _ -> fsep $
	    pwords "when inferring the type of" ++ [prettyA e]
	CheckExpr e t _ -> fsep $
	    pwords "when checking that the expression"
	    ++ [prettyA e] ++ pwords "has type" ++ [prettyTCM t]
	IsTypeCall e s _ -> fsep $
	    pwords "when checking that the expression"
	    ++ [prettyA e] ++ pwords "is a type of sort" ++ [prettyTCM s]
	IsType_ e _ -> fsep $
	    pwords "when checking that the expression"
	    ++ [prettyA e] ++ pwords "is a type"
	CheckArguments r es t0 t1 _ -> fsep $
	    pwords "when checking that" ++
	    map hPretty es ++ pwords "are valid arguments to a function of type" ++ [prettyTCM t0]
	CheckRecDef _ x ps cs _ ->
	    fsep $ pwords "when checking the definition of" ++ [prettyTCM x]
	CheckDataDef _ x ps cs _ ->
	    fsep $ pwords "when checking the definition of" ++ [prettyTCM x]
	CheckConstructor d _ _ (A.Axiom _ _ c _) _ -> fsep $
	    pwords "when checking the constructor" ++ [prettyTCM c] ++
	    pwords "in the declaration of" ++ [prettyTCM d]
	CheckConstructor _ _ _ _ _ -> __IMPOSSIBLE__
	CheckFunDef _ f _ _ ->
	    fsep $ pwords "when checking the definition of" ++ [prettyTCM f]
	CheckPragma _ p _ ->
	    fsep $ pwords "when checking the pragma" ++ [prettyA $ RangeAndPragma noRange p]
	CheckPrimitive _ x e _ -> fsep $
	    pwords "when checking that the type of the primitive function" ++
	    [prettyTCM x] ++ pwords "is" ++ [prettyA e]
        CheckWithFunctionType e _ -> fsep $
            pwords "when checking that the type" ++
            [prettyA e] ++ pwords "of the generated with function is well-formed"
        CheckDotPattern e v _ -> fsep $
            pwords "when checking that the given dot pattern" ++ [prettyA e] ++
            pwords "matches the inferred value" ++ [prettyTCM v]
        CheckPatternShadowing c _ -> fsep $
            pwords "when checking the clause" ++ [P.prettyA c]
	InferVar x _ ->
	    fsep $ pwords "when inferring the type of" ++ [prettyTCM x]
	InferDef _ x _ ->
	    fsep $ pwords "when inferring the type of" ++ [prettyTCM x]
        CheckIsEmpty r t _ ->
            fsep $ pwords "when checking that" ++ [prettyTCM t] ++ pwords "has no constructors"
	ScopeCheckExpr e _ ->
	    fsep $ pwords "when scope checking" ++ [pretty e]
	ScopeCheckDeclaration d _ ->
	    fwords "when scope checking the declaration" $$
	    nest 2 (pretty $ simpleDecl d)
	ScopeCheckLHS x p _ ->
	    fsep $ pwords "when scope checking the left-hand side" ++ [pretty p] ++
		   pwords "in the definition of" ++ [pretty x]
        NoHighlighting _ -> empty
	SetRange r _ ->
	    fsep $ pwords "when doing something at" ++ [text $ show r]
        CheckSectionApplication _ m1 modapp _ -> fsep $
          pwords "when checking the module application" ++
          [prettyA $ A.Apply info m1 modapp Map.empty Map.empty]
          where
            info = A.ModuleInfo noRange noRange Nothing Nothing Nothing

	where
            hPretty :: I.Arg (Named String Expr) -> TCM Doc
            hPretty a = do
                info <- reify $ argInfo a
                pretty =<< (abstractToConcreteCtx (hiddenArgumentCtx (argHiding a))
                         $ Common.Arg info $ unArg a)

	    simpleDecl = D.notSoNiceDeclaration
