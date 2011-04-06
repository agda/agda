{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Errors
    ( prettyError
    , PrettyTCM(..)
    , tcErrString
    ) where

import Control.Applicative ( (<$>) )
import Control.Monad.State
import Control.Monad.Error
import qualified Data.Map as Map (empty)
import System.FilePath

import Agda.Syntax.Common
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

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.Size

#include "../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Top level function
---------------------------------------------------------------------------

prettyError :: MonadTCM tcm => TCErr -> tcm String
prettyError err = liftTCM $ liftM show $
    prettyTCM err
    `catchError` \err' -> text "panic: error when printing error!" $$ prettyTCM err'
    `catchError` \err'' -> text "much panic: error when printing error from printing error!" $$ prettyTCM err''
    `catchError` \err''' -> fsep (
	pwords "total panic: error when printing error from printing error from printing error." ++
	pwords "I give up! Approximations of errors:" )
	$$ vcat (map (text . tcErrString) [err,err',err'',err'''])

---------------------------------------------------------------------------
-- * Helpers
---------------------------------------------------------------------------

sayWhere :: (MonadTCM tcm, HasRange a) => a -> tcm Doc -> tcm Doc
sayWhere x d = text (show $ getRange x) $$ d

sayWhen :: MonadTCM tcm => Range -> Maybe (Closure Call) -> tcm Doc -> tcm Doc
sayWhen r Nothing   m = sayWhere r m
sayWhen r (Just cl) m = sayWhere r (m $$ prettyTCM cl)

panic :: MonadTCM tcm => String -> tcm Doc
panic s = fwords $ "Panic: " ++ s

nameWithBinding :: MonadTCM tcm => QName -> tcm Doc
nameWithBinding q =
  sep [ prettyTCM q, text "bound at", text (show r) ]
  where
    r = nameBindingSite $ qnameName q

tcErrString :: TCErr -> String
tcErrString err = show (getRange err) ++ " " ++ case errError err of
    TypeError _ cl  -> errorString $ clValue cl
    Exception r s   -> show r ++ " " ++ s
    IOException r e -> show r ++ " " ++ show e
    PatternErr _    -> "PatternErr"
    AbortAssign _   -> "AbortAssign"

errorString :: TypeError -> String
errorString err = case err of
    AmbiguousModule{}                        -> "AmbiguousModule"
    AmbiguousName{}                          -> "AmbiguousName"
    AmbiguousParseForApplication{}           -> "AmbiguousParseForApplication"
    AmbiguousParseForLHS{}                   -> "AmbiguousParseForLHS"
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
    CoverageCantSplitType{}                  -> "CoverageCantSplitType"
    CyclicModuleDependency{}                 -> "CyclicModuleDependency"
    DataMustEndInSort{}                      -> "DataMustEndInSort"
    DifferentArities                         -> "DifferentArities"
    DoesNotConstructAnElementOf{}            -> "DoesNotConstructAnElementOf"
    DuplicateBuiltinBinding{}                -> "DuplicateBuiltinBinding"
    DuplicateConstructors{}                  -> "DuplicateConstructors"
    DuplicateFields{}                        -> "DuplicateFields"
    DuplicateImports{}                       -> "DuplicateImports"
    FieldOutsideRecord                       -> "FieldOutsideRecord"
    FileNotFound{}                           -> "FileNotFound"
    GenericError{}                           -> "GenericError"
    IlltypedPattern{}                        -> "IlltypedPattern"
    IncompletePatternMatching{}              -> "IncompletePatternMatching"
    IndexFreeInParameter{}                   -> "IndexFreeInParameter"
    IndexVariablesNotDistinct{}              -> "IndexVariablesNotDistinct"
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
    NoBindingForBuiltin{}                    -> "NoBindingForBuiltin"
    NoParseForApplication{}                  -> "NoParseForApplication"
    NoParseForLHS{}                          -> "NoParseForLHS"
    NoRHSRequiresAbsurdPattern{}             -> "NoRHSRequiresAbsurdPattern"
    NotInductive {}                          -> "NotInductive"
    AbsurdPatternRequiresNoRHS{}             -> "AbsurdPatternRequiresNoRHS"
    NoSuchBuiltinName{}                      -> "NoSuchBuiltinName"
    NoSuchModule{}                           -> "NoSuchModule"
    NoSuchPrimitiveFunction{}                -> "NoSuchPrimitiveFunction"
    NotAModuleExpr{}                         -> "NotAModuleExpr"
    NotAProperTerm                           -> "NotAProperTerm"
    NotAValidLetBinding{}                    -> "NotAValidLetBinding"
    NotAnExpression{}                        -> "NotAnExpression"
    NotImplemented{}                         -> "NotImplemented"
    NotSupported{}                           -> "NotSupported"
    NotInScope{}                             -> "NotInScope"
    NotLeqSort{}                             -> "NotLeqSort"
    NotStrictlyPositive{}                    -> "NotStrictlyPositive"
    NothingAppliedToHiddenArg{}              -> "NothingAppliedToHiddenArg"
    OverlappingProjects {}                   -> "OverlappingProjects"
    PatternShadowsConstructor {}             -> "PatternShadowsConstructor"
    PropMustBeSingleton                      -> "PropMustBeSingleton"
    RepeatedVariablesInPattern{}             -> "RepeatedVariablesInPattern"
    ShadowedModule{}                         -> "ShadowedModule"
    ShouldBeASort{}                          -> "ShouldBeASort"
    ShouldBeApplicationOf{}                  -> "ShouldBeApplicationOf"
    ShouldBeAppliedToTheDatatypeParameters{} -> "ShouldBeAppliedToTheDatatypeParameters"
    ShouldBeEmpty{}                          -> "ShouldBeEmpty"
    ShouldBePi{}                             -> "ShouldBePi"
    ShouldBeRecordType{}                     -> "ShouldBeRecordType"
    ShouldEndInApplicationOfTheDatatype{}    -> "ShouldEndInApplicationOfTheDatatype"
    TerminationCheckFailed{}                 -> "TerminationCheckFailed"
    TooFewFields{}                           -> "TooFewFields"
    TooManyArgumentsInLHS{}                  -> "TooManyArgumentsInLHS"
    TooManyFields{}                          -> "TooManyFields"
    SplitOnIrrelevant{}                      -> "SplitOnIrrelevant"
    DefinitionIsIrrelevant{}                 -> "DefinitionIsIrrelevant"
    VariableIsIrrelevant{}                   -> "VariableIsIrrelevant"
    UnequalRelevance{}                       -> "UnequalRelevance"
    UnequalHiding{}                          -> "UnequalHiding"
    UnequalLevel{}                           -> "UnequalLevel"
    UnequalSorts{}                           -> "UnequalSorts"
    UnequalTerms{}                           -> "UnequalTerms"
    UnequalTypes{}                           -> "UnequalTypes"
    UnequalTelescopes{}                      -> "UnequalTelescopes"
    UnexpectedWithPatterns{}                 -> "UnexpectedWithPatterns"
    UninstantiatedDotPattern{}               -> "UninstantiatedDotPattern"
    UninstantiatedModule{}                   -> "UninstantiatedModule"
    UnreachableClauses{}                     -> "UnreachableClauses"
    UnsolvedConstraints{}                    -> "UnsolvedConstraints"
    UnsolvedMetas{}                          -> "UnsolvedMetas"
    WithClausePatternMismatch{}              -> "WithClausePatternMismatch"
    WrongHidingInApplication{}               -> "WrongHidingInApplication"
    WrongHidingInLHS{}                       -> "WrongHidingInLHS"
    WrongHidingInLambda{}                    -> "WrongHidingInLambda"
    WrongNumberOfConstructorArguments{}      -> "WrongNumberOfConstructorArguments"

instance PrettyTCM TCErr where
    prettyTCM err = case errError err of
	TypeError s e -> do
	    s0 <- get
	    put s
	    d <- sayWhen (envRange $ clEnv e) (envCall $ clEnv e) $ prettyTCM e
	    put s0
	    return d
	Exception r s   -> sayWhere r $ fwords s
	IOException r e -> sayWhere r $ fwords $ show e
	PatternErr _    -> sayWhere err $ panic "uncaught pattern violation"
	AbortAssign _   -> sayWhere err $ panic "uncaught aborted assignment"

instance PrettyTCM TypeError where
    prettyTCM err = do
	case err of
	    InternalError s  -> panic s
	    NotImplemented s -> fwords $ "Not implemented: " ++ s
	    NotSupported s -> fwords $ "Not supported: " ++ s
	    CompilationError s -> sep [fwords "Compilation error:", text s]
	    GenericError s   -> fwords s
	    TerminationCheckFailed because -> fsep $
	      pwords "Termination checking failed for the following functions:" ++
              [ fsep (punctuate comma (map (text . show . qnameName)
                                           (concatMap fst because))) <> text "." ]
	    PropMustBeSingleton -> fwords
		"Datatypes in Prop must have at most one constructor when proof irrelevance is enabled"
	    DataMustEndInSort t -> fsep $
		pwords "The type of a datatype must end in a sort."
		++ [prettyTCM t] ++ pwords "isn't a sort."
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
		pwords "Expected record type, found " ++ [prettyTCM t]
	    DifferentArities ->
		fwords "The number of arguments in the defining equations differ"
	    WrongHidingInLHS t -> do
		fwords "Found an implicit argument where an explicit argument was expected"
	    WrongHidingInLambda t -> do
		fwords "Found an implicit lambda where an explicit lambda was expected"
	    WrongHidingInApplication t -> do
		fwords "Found an implicit application where an explicit application was expected"
            NotInductive t -> fsep $
              [prettyTCM t] ++ pwords "is not an inductive data type"
            UninstantiatedDotPattern e -> fsep $
              pwords "Failed to infer the value of dotted pattern"
            IlltypedPattern p a -> fsep $
              pwords "Type mismatch"
            TooManyArgumentsInLHS n a -> fsep $
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
              fsep (pwords "The following indices are not constructors" ++
                    pwords "(or literals) applied to variables:")
              $$ nest 2 (vcat $ map prettyTCM is)
            IndexVariablesNotDistinct is ->
              fsep (pwords "The variables in the following indices are not distinct:")
              $$ nest 2 (vcat $ map prettyTCM is)
            IndexFreeInParameter i pars ->
              fsep (pwords "The index" ++ [prettyTCM (I.Var i [])] ++
                    pwords "is free in the following parameters:")
              $$ nest 2 (vcat $ map prettyTCM pars)
            ShadowedModule [] -> __IMPOSSIBLE__
            ShadowedModule ms@(m : _) -> fsep $
              pwords "Duplicate definition of module" ++ [prettyTCM m <> text "."] ++
              pwords "Previous definition at" ++ [text $ show r]
              where
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
		[prettyTCM t] ++ pwords "should be empty, but it isn't obvious that it is."
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
            SplitOnIrrelevant p t -> fsep $
                pwords "cannot pattern match" ++ [prettyA p] ++
                pwords "against irrelevant type" ++ [prettyTCM t]
            DefinitionIsIrrelevant x -> fsep $
                text "identifier" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"
            VariableIsIrrelevant x -> fsep $
                text "variable" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"
 	    UnequalTerms cmp s t a -> fsep $
		[prettyTCM s, f cmp, prettyTCM t] ++ pwords "of type" ++ [prettyTCM a]
                where
                  f CmpEq  = text "!="
                  f CmpLeq = text "!=<"
	    UnequalLevel cmp s t -> fsep $
		[prettyTCM s, f cmp, prettyTCM t]
                where
                  f CmpEq  = text "!="
                  f CmpLeq = text "!=<"
	    UnequalTelescopes cmp a b -> fsep $
		[prettyTCM a, f cmp, prettyTCM b]
                where
                  f CmpEq  = text "!="
                  f CmpLeq = text "!=<"
	    UnequalTypes cmp a b -> fsep $
		[prettyTCM a, f cmp, prettyTCM b]
                where
                  f CmpEq  = text "!="
                  f CmpLeq = text "!=<"
	    UnequalRelevance a b -> fsep $
		[prettyTCM a] ++ pwords "!=" ++ [prettyTCM b] ++
-- Andreas 2010-09-21 to reveal Forced annotations, print also uglily
--		[text $ show a] ++ pwords "!=" ++ [text $ show b] ++
		pwords "because one is a relevant function type and the other is an irrelevant function type"
	    UnequalHiding a b -> fsep $
		[prettyTCM a] ++ pwords "!=" ++ [prettyTCM b] ++
		pwords "because one is an implicit function type and the other is an explicit function type"
	    UnequalSorts s1 s2 -> fsep $
		[prettyTCM s1] ++ pwords "!=" ++ [prettyTCM s2]
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
		$$ nest 2 (vcat $ map prettyTCM cs)
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
	      , nest 2 $ vcat $ map prettyTCM ys
	      ]
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
	    NoParseForApplication es -> fsep $
		pwords "Could not parse the application" ++ [pretty $ C.RawApp noRange es]
	    AmbiguousParseForApplication es es' -> fsep (
		    pwords "Don't know how to parse" ++ [pretty (C.RawApp noRange es) <> text "."] ++
		    pwords "Could mean any one of:"
		) $$ nest 2 (vcat $ map pretty es')
	    NoParseForLHS p -> fsep $
		pwords "Could not parse the left-hand side" ++ [pretty p]
	    AmbiguousParseForLHS p ps -> fsep (
		    pwords "Don't know how to parse" ++ [pretty p <> text "."] ++
		    pwords "Could mean any one of:"
		) $$ nest 2 (vcat $ map pretty ps)
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

            CoverageCantSplitOn c -> fsep $
              pwords "Cannot split on the constructor" ++ [prettyTCM c]

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

          where
            mpar n args
              | n > 0 && not (null args) = parens
              | otherwise                = id

            showArg (Arg Hidden r x)    = braces $ showPat 0 x
            showArg (Arg NotHidden r x) = showPat 1 x

            showPat _ (I.VarP _)        = text "_"
            showPat _ (I.DotP _)        = text "._"
            showPat n (I.ConP c _ args) = mpar n args $ prettyTCM c <+> fsep (map showArg args)
            showPat _ (I.LitP l)        = text (show l)



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
        CheckDotPattern e v _ -> fsep $
            pwords "when checking that the given dot pattern" ++ [prettyA e] ++
            pwords "matches the inferred value" ++ [prettyTCM v]
        CheckPatternShadowing c _ -> fsep $
            pwords "when checking the clause" ++ [P.prettyA c]
	InferVar x _ ->
	    fsep $ pwords "when inferring the type of" ++ [prettyTCM x]
	InferDef _ x _ ->
	    fsep $ pwords "when inferring the type of" ++ [prettyTCM x]
	ScopeCheckExpr e _ ->
	    fsep $ pwords "when scope checking" ++ [pretty e]
	ScopeCheckDeclaration d _ ->
	    fwords "when scope checking the declaration" $$
	    nest 2 (pretty $ simpleDecl d)
	ScopeCheckDefinition d _ ->
	    fwords "when scope checking the definition" $$
	    nest 2 (vcat $ map pretty $ simpleDef d)
	ScopeCheckLHS x p _ ->
	    fsep $ pwords "when scope checking the left-hand side" ++ [pretty p] ++
		   pwords "in the definition of" ++ [pretty x]
	TermFunDef _ f _ _ ->
	    fsep $ pwords "when termination checking the definition of" ++ [prettyTCM f]
	SetRange r _ ->
	    fsep $ pwords "when doing something at" ++ [text $ show r]
        CheckSectionApplication _ m1 ptel m2 args _ -> fsep $
          pwords "when checking the module application" ++
          [prettyA $ A.Apply info m1 ptel m2 args Map.empty Map.empty]
          where
            info = A.ModuleInfo noRange noRange Nothing Nothing Nothing

	where
	    hPretty a = pretty =<< abstractToConcreteCtx (hiddenArgumentCtx (argHiding a)) a

	    simpleDef d = case d of
	      D.FunDef _ ds _ _ _ _ _	 -> ds
	      D.DataDef r fx p a d bs cs ->
		[ C.Data r Inductive d (map bind bs) (C.Underscore noRange Nothing)
		    $ map simpleDecl cs
		]
	      D.RecDef r fx p a d c bs cs ->
		[ C.Record r d (name <$> c) (map bind bs) (C.Underscore noRange Nothing)
		    $ map simpleDecl cs
		]
	      where
		bind :: C.LamBinding -> C.TypedBindings
		bind (C.DomainFull b) = b
		bind (C.DomainFree h x) = C.TypedBindings r $ Arg h Relevant (C.TBind r [x] (C.Underscore r Nothing))
		  where r = getRange x

                name (D.Axiom _ _ _ _ _ n _) = n
                name _                     = __IMPOSSIBLE__

	    simpleDecl d = case d of
		D.Axiom _ _ _ _ rel x e		       -> C.TypeSig rel x e
		D.NiceField _ _ _ _ x e	               -> C.Field x e
		D.PrimitiveFunction r _ _ _ x e	       -> C.Primitive r [C.TypeSig Relevant x e]
		D.NiceDef r ds _ _		       -> C.Mutual r ds
		D.NiceModule r _ _ x tel _	       -> C.Module r x tel []
		D.NiceModuleMacro r _ _ x tel e op dir -> C.ModuleMacro r x tel e op dir
		D.NiceOpen r x dir		       -> C.Open r x dir
		D.NiceImport r x as op dir	       -> C.Import r x as op dir
		D.NicePragma _ p		       -> C.Pragma p
