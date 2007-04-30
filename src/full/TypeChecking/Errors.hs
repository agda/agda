{-# OPTIONS -cpp -fglasgow-exts -fallow-undecidable-instances #-}
module TypeChecking.Errors
    ( prettyError
    , PrettyTCM(..)
    ) where

import Control.Applicative ( (<$>) )
import Control.Monad.State
import Control.Monad.Error

import Syntax.Common
import Syntax.Fixity
import Syntax.Position
import qualified Syntax.Concrete as C
import qualified Syntax.Concrete.Definitions as D
import Syntax.Abstract as A
import Syntax.Internal as I
import qualified Syntax.Abstract.Pretty as P
import qualified Syntax.Concrete.Pretty as P
import Syntax.Translation.InternalToAbstract
import Syntax.Translation.AbstractToConcrete

import TypeChecking.Monad
import TypeChecking.Pretty

import Utils.Monad
import Utils.Trace
import Utils.Pretty (Doc)

#include "../undefined.h"

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

sayWhen :: MonadTCM tcm => CallTrace -> tcm Doc -> tcm Doc
sayWhen tr m = case matchCall interestingCall tr of
    Nothing -> m
    Just c  -> sayWhere c (m $$ prettyTCM c)

panic :: MonadTCM tcm => String -> tcm Doc
panic s = fwords $ "Panic: " ++ s

tcErrString :: TCErr -> String
tcErrString err = show (getRange err) ++ " " ++ case err of
    TypeError _ cl -> errorString $ clValue cl
    Exception r s  -> show r ++ " " ++ s
    PatternErr _   -> "PatternErr"
    AbortAssign _  -> "AbortAssign"

errorString :: TypeError -> String
errorString err = case err of
    InternalError _			       -> "InternalError"
    NotImplemented _			       -> "NotImplemented"
    PropMustBeSingleton			       -> "PropMustBeSingleton"
    DataMustEndInSort _			       -> "DataMustEndInSort"
    ShouldEndInApplicationOfTheDatatype _      -> "ShouldEndInApplicationOfTheDatatype"
    ShouldBeAppliedToTheDatatypeParameters _ _ -> "ShouldBeAppliedToTheDatatypeParameters"
    ShouldBeApplicationOf _ _		       -> "ShouldBeApplicationOf"
    DifferentArities			       -> "DifferentArities"
    WrongHidingInLHS _			       -> "WrongHidingInLHS"
    WrongHidingInLambda _		       -> "WrongHidingInLambda"
    WrongHidingInApplication _		       -> "WrongHidingInApplication"
    ShouldBeEmpty _			       -> "ShouldBeEmpty"
    ShouldBeASort _			       -> "ShouldBeASort"
    ShouldBePi _			       -> "ShouldBePi"
    NotAProperTerm			       -> "NotAProperTerm"
    UnequalTerms _ _ _			       -> "UnequalTerms"
    UnequalTypes _ _			       -> "UnequalTypes"
    UnequalHiding _ _			       -> "UnequalHiding"
    UnequalSorts _ _			       -> "UnequalSorts"
    NotLeqSort _ _			       -> "NotLeqSort"
    MetaCannotDependOn _ _ _		       -> "MetaCannotDependOn"
    MetaOccursInItself _		       -> "MetaOccursInItself"
    GenericError _			       -> "GenericError"
    NoSuchBuiltinName _			       -> "NoSuchBuiltinName"
    DuplicateBuiltinBinding _ _ _	       -> "DuplicateBuiltinBinding"
    NoBindingForBuiltin _		       -> "NoBindingForBuiltin"
    NoSuchPrimitiveFunction _		       -> "NoSuchPrimitiveFunction"
    BuiltinInParameterisedModule _	       -> "BuiltinInParameterisedModule"
    NoRHSRequiresAbsurdPattern _	       -> "NoRHSRequiresAbsurdPattern"
    LocalVsImportedModuleClash _	       -> "LocalVsImportedModuleClash"
    UnsolvedMetasInImport _		       -> "UnsolvedMetasInImport"
    UnsolvedMetas _			       -> "UnsolvedMetas"
    UnsolvedConstraints _		       -> "UnsolvedConstraints"
    CyclicModuleDependency _		       -> "CyclicModuleDependency"
    FileNotFound _ _			       -> "FileNotFound"
    ClashingFileNamesFor _ _		       -> "ClashingFileNamesFor"
    NotInScope _			       -> "NotInScope"
    NoSuchModule _			       -> "NoSuchModule"
    UninstantiatedModule _		       -> "UninstantiatedModule"
    ClashingDefinition _ _		       -> "ClashingDefinition"
    ClashingModule _ _			       -> "ClashingModule"
    ClashingImport _ _			       -> "ClashingImport"
    ClashingModuleImport _ _		       -> "ClashingModuleImport"
    ModuleDoesntExport _ _		       -> "ModuleDoesntExport"
    NotAModuleExpr _			       -> "NotAModuleExpr"
    NotAnExpression _			       -> "NotAnExpression"
    NotAValidLetBinding _		       -> "NotAValidLetBinding"
    NothingAppliedToHiddenArg _		       -> "NothingAppliedToHiddenArg"
    NoParseForApplication _		       -> "NoParseForApplication"
    AmbiguousParseForApplication _ _	       -> "AmbiguousParseForApplication"
    NoParseForLHS _			       -> "NoParseForLHS"
    AmbiguousParseForLHS _ _		       -> "AmbiguousParseForLHS"
    IncompletePatternMatching _ _	       -> "IncompletePatternMatching"
    NotStrictlyPositive _ _		       -> "NotStrictlyPositive"

instance PrettyTCM TCErr where
    prettyTCM err = case err of
	TypeError s e -> do
	    s0 <- get
	    put s
	    d <- sayWhen (clTrace e) $ prettyTCM e
	    put s0
	    return d
	Exception r s -> sayWhere r $ fwords s
	PatternErr _  -> sayWhere err $ panic "uncaught pattern violation"
	AbortAssign _ -> sayWhere err $ panic "uncaught aborted assignment"

instance PrettyTCM TypeError where
    prettyTCM err = do
	trace <- getTrace
	case err of
	    InternalError s  -> panic s
	    NotImplemented s -> fwords $ "Not implemented: " ++ s
	    GenericError s   -> fwords s
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
	    DifferentArities ->
		fwords "The number of arguments in the defining equations differ"
	    WrongHidingInLHS t -> do
		fwords "Found an implicit argument where an explicit argument was expected"
	    WrongHidingInLambda t -> do
		fwords "Found an implicit lambda where an explicit lambda was expected"
	    WrongHidingInApplication t -> do
		fwords "Found an implicit application where an explicit application was expected"
	    ShouldBeEmpty t -> fsep $
		[prettyTCM t] ++ pwords "should be empty, but it isn't (as far as I can see)"
	    ShouldBeASort t -> fsep $
		[prettyTCM t] ++ pwords "should be a sort, but it isn't"
	    ShouldBePi t -> fsep $
		[prettyTCM t] ++ pwords "should be a function type, but it isn't"
	    NotAProperTerm ->
		fwords "Found a malformed term"
	    UnequalTerms s t a -> fsep $
		[prettyTCM s] ++ pwords "!=" ++ [prettyTCM t] ++ pwords "of type" ++ [prettyTCM a]
	    UnequalTypes a b -> fsep $
		[prettyTCM a] ++ pwords "!=" ++ [prettyTCM b]
	    UnequalHiding a b -> fsep $
		[prettyTCM a] ++ pwords "!=" ++ [prettyTCM b] ++
		pwords "because one is an implicit function type and the other is an explicit function type"
	    UnequalSorts s1 s2 -> fsep $
		[prettyTCM s1] ++ pwords "!=" ++ [prettyTCM s2]
	    NotLeqSort s1 s2 -> fsep $
		pwords "The type of the constructor does not fit in the sort of the datatype, since"
		++ [prettyTCM s1] ++ pwords "is not less or equal than" ++ [prettyTCM s2]
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
	    LocalVsImportedModuleClash m -> fsep $
		pwords "The module" ++ [text $ show m] ++
		pwords "can refer to either a local module or an imported module"
	    UnsolvedMetas rs ->
		fsep ( pwords "Unsolved metas at the following locations:" )
		$$ nest 2 (vcat $ map (text . show) rs)
	    UnsolvedMetasInImport rs ->
		fsep ( pwords "There were unsolved metas in an imported module at the following locations:" )
		$$ nest 2 (vcat $ map (text . show) rs)
	    UnsolvedConstraints cs ->
		fsep ( pwords "Failed to solve the following constraints:" )
		$$ nest 2 (vcat $ map prettyTCM cs)
	    CyclicModuleDependency ms ->
		fsep (pwords "cyclic module dependency:")
		$$ nest 2 (vcat $ map (text . show) ms)
	    FileNotFound x files ->
		fsep ( pwords "Failed to find source of module" ++ [text $ show x] ++
		       pwords "in any of the following locations:"
		     ) $$ nest 2 (vcat $ map text files)
	    ClashingFileNamesFor x files ->
		fsep ( pwords "Multiple possible sources for module" ++ [text $ show x] ++
		       pwords "found:"
		     ) $$ nest 2 (vcat $ map text files)
	    NotInScope xs ->
		fsep (pwords "Not in scope:") $$ nest 2 (vcat $ map name xs)
		where name x = hsep [ pretty x, text "at", text $ show $ getRange x ]

	    NoSuchModule x -> fsep $
		pwords "No such module" ++ [pretty x]
	    UninstantiatedModule x -> fsep (
		    pwords "Cannot access the contents of the parameterised module" ++ [pretty x <> text "."] ++
		    pwords "To do this the module first has to be instantiated. For instance:"
		) $$ nest 2 (hsep [ text "module", pretty x <> text "'", text "=", pretty x, text "e1 .. en" ])
	    ClashingDefinition x y -> fsep $
		pwords "Multiple definitions of" ++ [pretty x]
	    ClashingModule m1 m2 -> fsep $
		pwords "The modules" ++ [prettyTCM m1, text "and", prettyTCM m2] ++ pwords "clash."
	    ClashingImport x y -> fsep $
		pwords "Import clash between" ++ [pretty x, text "and", prettyTCM y]
	    ClashingModuleImport x y -> fsep $
		pwords "Module import clash between" ++ [pretty x, text "and", prettyTCM y]
	    ModuleDoesntExport m xs -> fsep $
		pwords "The module" ++ [pretty m] ++ pwords "doesn't export the following:" ++
		punctuate comma (map pretty xs)
	    NotAModuleExpr e -> fsep $
		pwords "The right-hand side of a module definition must have the form 'M e1 .. en'" ++
		pwords "where M is a module name. The expression" ++ [pretty e, text "doesn't."]
	    NotAnExpression e -> fsep $
		[pretty e] ++ pwords "is not a valid expression."
	    NotAValidLetBinding nd -> fwords $
		"Let-definitions cannot do pattern matching or be recursive."
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
		pwords "Incomplete pattern matching for" ++ [prettyTCM v <> text"."] ++
		pwords "No match for" ++ map prettyTCM args
	    NotStrictlyPositive d ocs -> fsep $
		pwords "Datatype" ++ [prettyTCM d] ++ pwords "is not strictly positive, because"
		++ prettyOcc "it" ocs
		where
		    prettyOcc _ [] = []
		    prettyOcc it (Occ d c r : ocs) = concat
			[ pwords it, pwords "occurs", prettyR r
			, pwords "in constructor", [prettyTCM c], pwords "of datatype"
			, [prettyTCM d <> com ocs], prettyOcc "which" ocs
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


instance PrettyTCM Call where
    prettyTCM c = case c of
	CheckClause t cl _  -> fsep $
	    pwords "when checking that the clause"
	    ++ [prettyA cl] ++ pwords "has type" ++ [prettyTCM t]
	CheckPatterns ps t _ -> fsep $
	    pwords "when checking that the patterns" ++
	    map hPretty ps ++ pwords "fit the type" ++ [prettyTCM t]
	CheckPattern _ p t _ -> fsep $
	    pwords "when checking that the pattern"
	    ++ [prettyA p] ++ pwords "has type" ++ [prettyTCM t]
	CheckLetBinding b _ -> fsep $
	    pwords "when checking the let binding" ++ [vcat . map pretty =<< abstractToConcrete_ b]
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
	CheckDataDef _ x ps cs _ ->
	    fsep $ pwords "when checking the definition of" ++ [prettyTCM x]
	CheckConstructor d _ _ (A.Axiom _ c _) _ -> fsep $
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
	InferVar x _ ->
	    fsep $ pwords "when inferring the type of" ++ [prettyTCM x]
	InferDef _ x _ ->
	    fsep $ pwords "when inferring the type of" ++ [prettyTCM x]
	ScopeCheckExpr e _ ->
	    fsep $ pwords "when scope checking" ++ [pretty e]
	ScopeCheckDeclaration d _ ->
	    fwords "when scope checking the declaration" $$
	    nest 2 (pretty $ simpleDecl d)
	ScopeCheckLHS x p _ ->
	    fsep $ pwords "when scope checking the left-hand side" ++ [pretty p] ++
		   pwords "in the definition of" ++ [pretty x]
	where
	    hPretty a@(Arg h _) = pretty =<< abstractToConcreteCtx (hiddenArgumentCtx h) a

	    simpleDecl d = case d of
		D.Axiom _ _ _ _ x e		       -> C.TypeSig x e
		D.PrimitiveFunction r _ _ _ x e	       -> C.Primitive r [C.TypeSig x e]
		D.NiceDef r ds _ _		       -> C.Mutual r ds
		D.NiceModule r _ _ x tel _	       -> C.Module r x tel []
		D.NiceModuleMacro r _ _ x tel e op dir -> C.ModuleMacro r x tel e op dir
		D.NiceOpen r x dir		       -> C.Open r x dir
		D.NiceImport r x as op dir	       -> C.Import r x as op dir
		D.NicePragma _ p		       -> C.Pragma p

interestingCall :: Closure Call -> Maybe (Closure Call)
interestingCall cl = case clValue cl of
    InferVar _ _	      -> Nothing
    InferDef _ _ _	      -> Nothing
    CheckArguments _ [] _ _ _ -> Nothing
    _			      -> Just cl

