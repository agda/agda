{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Errors
  ( prettyError
  , tcErrString
  , Warnings(..)
  , warningsToError
  ) where

import Prelude hiding (null)

import Control.Monad.State

import Data.Function
import Data.List (nub, sortBy)
import Data.Maybe
import qualified Data.Set as Set
import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as D
import Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract.Pretty as AP
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Scope.Monad (isDatatypeModule)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (instantiate)

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.FileName
import Agda.Utils.Function
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size
import qualified Agda.Utils.Pretty as P

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Top level function
---------------------------------------------------------------------------

{-# SPECIALIZE prettyError :: TCErr -> TCM String #-}
prettyError :: MonadTCM tcm => TCErr -> tcm String
prettyError err = liftTCM $ show <$> prettyError' err []
  where
  prettyError' :: TCErr -> [TCErr] -> TCM Doc
  prettyError' err errs
    | length errs > 3 = fsep (
        pwords "total panic: error when printing error from printing error from printing error." ++
        pwords "I give up! Approximations of errors (original error last):" )
        $$ vcat (map (text . tcErrString) errs)
    | otherwise = applyUnless (null errs) (text "panic: error when printing error!" $$) $ do
        (prettyTCM err $$ vcat (map (text . ("when printing error " ++) . tcErrString) errs))
        `catchError` \ err' -> prettyError' err' (err:errs)

---------------------------------------------------------------------------
-- * Warnings
---------------------------------------------------------------------------

-- | Warnings.
--
-- Invariant: The fields are never empty at the same time.

data Warnings = Warnings
  { unsolvedMetaVariables :: [Range]
    -- ^ Meta-variable problems are reported as type errors unless
    -- 'optAllowUnsolved' is 'True'.
  , unsolvedConstraints   :: Constraints
    -- ^ Same as 'unsolvedMetaVariables'.
  }

-- | Turns warnings into an error. Even if several errors are possible
--   only one is raised.
warningsToError :: Warnings -> TCM a
warningsToError (Warnings [] [])     = typeError $ SolvedButOpenHoles
warningsToError (Warnings w@(_:_) _) = typeError $ UnsolvedMetas w
warningsToError (Warnings _ w@(_:_)) = typeError $ UnsolvedConstraints w

---------------------------------------------------------------------------
-- * Helpers
---------------------------------------------------------------------------

sayWhere :: HasRange a => a -> TCM Doc -> TCM Doc
sayWhere x d = applyUnless (null r) (prettyTCM r $$) d
  where r = getRange x

sayWhen :: Range -> Maybe (Closure Call) -> TCM Doc -> TCM Doc
sayWhen r Nothing   m = sayWhere r m
sayWhen r (Just cl) m = sayWhere r (m $$ prettyTCM cl)

panic :: String -> TCM Doc
panic s = fwords $ "Panic: " ++ s

nameWithBinding :: QName -> TCM Doc
nameWithBinding q =
  sep [ prettyTCM q, text "bound at", prettyTCM r ]
  where
    r = nameBindingSite $ qnameName q

tcErrString :: TCErr -> String
tcErrString err = show (getRange err) ++ " " ++ case err of
  TypeError _ cl  -> errorString $ clValue cl
  Exception r s   -> show r ++ " " ++ show s
  IOException r e -> show r ++ " " ++ show e
  PatternErr{}    -> "PatternErr"
  {- AbortAssign _   -> "AbortAssign" -- UNUSED -}

errorString :: TypeError -> String
errorString err = case err of
  AmbiguousModule{}                        -> "AmbiguousModule"
  AmbiguousName{}                          -> "AmbiguousName"
  AmbiguousParseForApplication{}           -> "AmbiguousParseForApplication"
  AmbiguousParseForLHS{}                   -> "AmbiguousParseForLHS"
--  AmbiguousParseForPatternSynonym{}        -> "AmbiguousParseForPatternSynonym"
  AmbiguousTopLevelModuleName {}           -> "AmbiguousTopLevelModuleName"
  BadArgumentsToPatternSynonym{}           -> "BadArgumentsToPatternSynonym"
  TooFewArgumentsToPatternSynonym{}        -> "TooFewArgumentsToPatternSynonym"
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
  CoverageNoExactSplit{}                   -> "CoverageNoExactSplit"
  CyclicModuleDependency{}                 -> "CyclicModuleDependency"
  DataMustEndInSort{}                      -> "DataMustEndInSort"
-- UNUSED:    DataTooManyParameters{}                  -> "DataTooManyParameters"
  CantResolveOverloadedConstructorsTargetingSameDatatype{} -> "CantResolveOverloadedConstructorsTargetingSameDatatype"
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
  IllformedProjectionPattern{}             -> "IllformedProjectionPattern"
  CannotEliminateWithPattern{}             -> "CannotEliminateWithPattern"
  IllegalLetInTelescope{}                  -> "IllegalLetInTelescope"
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
  NeedOptionRewriting{}                    -> "NeedOptionRewriting"
  NoBindingForBuiltin{}                    -> "NoBindingForBuiltin"
  NoParseForApplication{}                  -> "NoParseForApplication"
  NoParseForLHS{}                          -> "NoParseForLHS"
--  NoParseForPatternSynonym{}               -> "NoParseForPatternSynonym"
  NoRHSRequiresAbsurdPattern{}             -> "NoRHSRequiresAbsurdPattern"
  NotInductive {}                          -> "NotInductive"
  AbsurdPatternRequiresNoRHS{}             -> "AbsurdPatternRequiresNoRHS"
  NoSuchBuiltinName{}                      -> "NoSuchBuiltinName"
  NoSuchModule{}                           -> "NoSuchModule"
  NoSuchPrimitiveFunction{}                -> "NoSuchPrimitiveFunction"
  NotAModuleExpr{}                         -> "NotAModuleExpr"
  NotAProperTerm                           -> "NotAProperTerm"
  SetOmegaNotValidType{}                   -> "SetOmegaNotValidType"
  InvalidType{}                            -> "InvalidType"
  InvalidTypeSort{}                        -> "InvalidTypeSort"
  FunctionTypeInSizeUniv{}                 -> "FunctionTypeInSizeUniv"
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
  OperatorChangeMessage {}                 -> "OperatorChangeMessage"
  OperatorInformation {}                   -> "OperatorInformation"
  PatternShadowsConstructor {}             -> "PatternShadowsConstructor"
  PropMustBeSingleton                      -> "PropMustBeSingleton"
  RepeatedVariablesInPattern{}             -> "RepeatedVariablesInPattern"
  SafeFlagPostulate{}                      -> "SafeFlagPostulate"
  SafeFlagPragma{}                         -> "SafeFlagPragma"
  SafeFlagNoTerminationCheck{}             -> "SafeFlagNoTerminationCheck"
  SafeFlagNonTerminating{}                 -> "SafeFlagNonTerminating"
  SafeFlagTerminating{}                    -> "SafeFlagTerminating"
  SafeFlagPrimTrustMe{}                    -> "SafeFlagPrimTrustMe"
  ShadowedModule{}                         -> "ShadowedModule"
  ShouldBeASort{}                          -> "ShouldBeASort"
  ShouldBeApplicationOf{}                  -> "ShouldBeApplicationOf"
  ShouldBeAppliedToTheDatatypeParameters{} -> "ShouldBeAppliedToTheDatatypeParameters"
  ShouldBeEmpty{}                          -> "ShouldBeEmpty"
  ShouldBePi{}                             -> "ShouldBePi"
  ShouldBeRecordType{}                     -> "ShouldBeRecordType"
  ShouldBeRecordPattern{}                  -> "ShouldBeRecordPattern"
  NotAProjectionPattern{}                  -> "NotAProjectionPattern"
  ShouldEndInApplicationOfTheDatatype{}    -> "ShouldEndInApplicationOfTheDatatype"
  SplitError{}                             -> "SplitError"
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
--  UnequalLevel{}                           -> "UnequalLevel" -- UNUSED
  UnequalSorts{}                           -> "UnequalSorts"
  UnequalTerms{}                           -> "UnequalTerms"
  UnequalTypes{}                           -> "UnequalTypes"
--  UnequalTelescopes{}                      -> "UnequalTelescopes" -- UNUSED
  HeterogeneousEquality{}                  -> "HeterogeneousEquality"
  WithOnFreeVariable{}                     -> "WithOnFreeVariable"
  UnexpectedWithPatterns{}                 -> "UnexpectedWithPatterns"
  UninstantiatedDotPattern{}               -> "UninstantiatedDotPattern"
  UninstantiatedModule{}                   -> "UninstantiatedModule"
  UnreachableClauses{}                     -> "UnreachableClauses"
  UnsolvedConstraints{}                    -> "UnsolvedConstraints"
  UnsolvedMetas{}                          -> "UnsolvedMetas"
  SolvedButOpenHoles{}                     -> "SolvedButOpenHoles"
  UnusedVariableInPatternSynonym           -> "UnusedVariableInPatternSynonym"
  UnquoteFailed{}                          -> "UnquoteFailed"
  WithClausePatternMismatch{}              -> "WithClausePatternMismatch"
  WithoutKError{}                          -> "WithoutKError"
  WrongHidingInApplication{}               -> "WrongHidingInApplication"
  WrongHidingInLHS{}                       -> "WrongHidingInLHS"
  WrongHidingInLambda{}                    -> "WrongHidingInLambda"
  WrongInstanceDeclaration{}               -> "WrongInstanceDeclaration"
  WrongIrrelevanceInLambda{}               -> "WrongIrrelevanceInLambda"
  WrongNamedArgument{}                     -> "WrongNamedArgument"
  WrongNumberOfConstructorArguments{}      -> "WrongNumberOfConstructorArguments"
  HidingMismatch{}                         -> "HidingMismatch"
  RelevanceMismatch{}                      -> "RelevanceMismatch"

instance PrettyTCM TCErr where
  prettyTCM err = case err of
    -- Andreas, 2014-03-23
    -- This use of localState seems ok since we do not collect
    -- Benchmark info during printing errors.
    TypeError s e -> localState $ do
      put s
      sayWhen (envRange $ clEnv e) (envCall $ clEnv e) $ prettyTCM e
    Exception r s   -> sayWhere r $ return s
    IOException r e -> sayWhere r $ fwords $ show e
    PatternErr{}    -> sayWhere err $ panic "uncaught pattern violation"
    {- AbortAssign _   -> sayWhere err $ panic "uncaught aborted assignment" -- UNUSED -}

instance PrettyTCM CallInfo where
  prettyTCM c = do
    let call = prettyTCM $ callInfoCall c
        r    = callInfoRange c
    if null $ P.pretty r
      then call
      else call $$ nest 2 (text "(at" <+> prettyTCM r <> text ")")

-- | Drops the filename component of the qualified name.
dropTopLevelModule :: QName -> QName
dropTopLevelModule (QName (MName ns) n) = QName (MName (drop 1 ns)) n

instance PrettyTCM TypeError where
  prettyTCM err = case err of
    InternalError s -> panic s

    NotImplemented s -> fwords $ "Not implemented: " ++ s

    NotSupported s -> fwords $ "Not supported: " ++ s

    CompilationError s -> sep [fwords "Compilation error:", text s]

    GenericError s -> fwords s

    GenericDocError d -> return d

    TerminationCheckFailed because ->
      fwords "Termination checking failed for the following functions:"
      $$ (nest 2 $ fsep $ punctuate comma $
           map (pretty . dropTopLevelModule) $
             concatMap termErrFunctions because)
      $$ fwords "Problematic calls:"
      $$ (nest 2 $ fmap (P.vcat . nub) $
            mapM prettyTCM $ sortBy (compare `on` callInfoRange) $
            concatMap termErrCalls because)

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

    NotAProjectionPattern p -> fsep $
      pwords "Not a valid projection for a copattern: " ++ [ prettyA p ]

    DifferentArities ->
      fwords "The number of arguments in the defining equations differ"

    WrongHidingInLHS -> fwords "Unexpected implicit argument"

    WrongHidingInLambda t ->
      fwords "Found an implicit lambda where an explicit lambda was expected"

    WrongIrrelevanceInLambda t ->
      fwords "Found an irrelevant lambda where a relevant lambda was expected"

    WrongNamedArgument a -> fsep $
      pwords "Function does not accept argument "
      ++ [prettyTCM a] -- ++ pwords " (wrong argument name)"

    WrongHidingInApplication t ->
      fwords "Found an implicit application where an explicit application was expected"

    WrongInstanceDeclaration -> fwords "Terms marked as eligible for instance search should end with a name"

    HidingMismatch h h' -> fwords $
      "Expected " ++ verbalize (Indefinite h') ++ " argument, but found " ++
      verbalize (Indefinite h) ++ " argument"

    RelevanceMismatch r r' -> fwords $
      "Expected " ++ verbalize (Indefinite r') ++ " argument, but found " ++
      verbalize (Indefinite r) ++ " argument"

    NotInductive t -> fsep $
      [prettyTCM t] ++ pwords "is not an inductive data type"

    UninstantiatedDotPattern e -> fsep $
      pwords "Failed to infer the value of dotted pattern"

    IlltypedPattern p a -> fsep $
      pwords "Type mismatch"

    IllformedProjectionPattern p -> fsep $
      pwords "Ill-formed projection pattern " ++ [prettyA p]

    CannotEliminateWithPattern p a -> do
      let isProj = isJust (isProjP p)
      fsep $
        pwords "Cannot eliminate type" ++ prettyTCM a :
        if isProj then
           pwords "with projection pattern" ++ [prettyA p]
         else
           pwords "with pattern" ++ prettyA p :
           pwords "(did you supply too many arguments?)"

    TooManyArgumentsInLHS a -> fsep $
      pwords "Left hand side gives too many arguments to a function of type"
      ++ [prettyTCM a]

    WrongNumberOfConstructorArguments c expect given -> fsep $
      pwords "The constructor" ++ [prettyTCM c] ++
      pwords "expects" ++ [prettyTCM expect] ++
      pwords "arguments (including hidden ones), but has been given"
      ++ [prettyTCM given] ++ pwords "(including hidden ones)"

    CantResolveOverloadedConstructorsTargetingSameDatatype d cs -> fsep $
      pwords "Can't resolve overloaded constructors targeting the same datatype"
      ++ [(parens $ prettyTCM (qnameToConcrete d)) <> colon]
      ++ map pretty cs

    DoesNotConstructAnElementOf c t -> fsep $
      pwords "The constructor" ++ [prettyTCM c] ++
      pwords "does not construct an element of" ++ [prettyTCM t]

    ConstructorPatternInWrongDatatype c d -> fsep $
      [prettyTCM c] ++ pwords "is not a constructor of the datatype"
      ++ [prettyTCM d]

    IndicesNotConstructorApplications [i] ->
      fwords "The index"
      $$ nest 2 (prettyTCM i)
      $$ fsep (pwords "is not a constructor (or literal) applied to variables" ++
               pwords "(note that parameters count as constructor arguments)")

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
      pwords "at" ++ [prettyTCM r]
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
      pwords "The arguments to " ++ [prettyTCM m] ++ pwords "do not fit the telescope" ++
      [prettyTCM tel]

    ShouldBeEmpty t [] -> fsep $
       [prettyTCM t] ++ pwords "should be empty, but that's not obvious to me"

    ShouldBeEmpty t ps -> fsep (
      [prettyTCM t] ++
      pwords "should be empty, but the following constructor patterns are valid:"
      ) $$ nest 2 (vcat $ map (prettyPat 0) ps)

    ShouldBeASort t -> fsep $
      [prettyTCM t] ++ pwords "should be a sort, but it isn't"

    ShouldBePi t -> fsep $
      [prettyTCM t] ++ pwords "should be a function type, but it isn't"

    NotAProperTerm -> fwords "Found a malformed term"

    SetOmegaNotValidType -> fwords "Setω is not a valid type"

    InvalidTypeSort s -> fsep $ [prettyTCM s] ++ pwords "is not a valid type"
    InvalidType v -> fsep $ [prettyTCM v] ++ pwords "is not a valid type"

    FunctionTypeInSizeUniv v -> fsep $
      pwords "Functions may not return sizes, thus, function type " ++
      [ prettyTCM v ] ++ pwords " is illegal"

    SplitOnIrrelevant p t -> fsep $
      pwords "Cannot pattern match" ++ [prettyA p] ++
      pwords "against irrelevant type" ++ [prettyTCM t]

    DefinitionIsIrrelevant x -> fsep $
      text "Identifier" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"
    VariableIsIrrelevant x -> fsep $
      text "Variable" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"
    UnequalBecauseOfUniverseConflict cmp s t -> fsep $
      [prettyTCM s, notCmp cmp, prettyTCM t, text "because this would result in an invalid use of Setω" ]

    UnequalTerms cmp s t a -> do
      (d1, d2, d) <- prettyInEqual s t
      fsep $ [return d1, notCmp cmp, return d2] ++ pwords "of type" ++ [prettyTCM a] ++ [return d]

-- UnequalLevel is UNUSED
--   UnequalLevel cmp s t -> fsep $
--     [prettyTCM s, notCmp cmp, prettyTCM t]

-- UnequalTelescopes is UNUSED
--   UnequalTelescopes cmp a b -> fsep $
--     [prettyTCM a, notCmp cmp, prettyTCM b]

    UnequalTypes cmp a b -> prettyUnequal a (notCmp cmp) b
--              fsep $ [prettyTCM a, notCmp cmp, prettyTCM b]

    HeterogeneousEquality u a v b -> fsep $
      pwords "Refuse to solve heterogeneous constraint" ++
      [prettyTCM u] ++ pwords ":" ++ [prettyTCM a] ++ pwords "=?=" ++
      [prettyTCM v] ++ pwords ":" ++ [prettyTCM b]

    UnequalRelevance cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
-- Andreas 2010-09-21 to reveal Forced annotations, print also uglily
--            [text $ show a, notCmp cmp, text $ show b] ++
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

    WithOnFreeVariable e -> fsep $
      pwords "Cannot `with` on variable " ++ [prettyA e] ++
      pwords " bound in a module telescope (or patterns of a parent clause)"

    UnexpectedWithPatterns ps -> fsep $
      pwords "Unexpected with patterns" ++ (punctuate (text " |") $ map prettyA ps)

    WithClausePatternMismatch p q -> fsep $
      pwords "With clause pattern " ++ [prettyA p] ++
      pwords " is not an instance of its parent pattern " ++ [prettyTCM q]
         -- TODO: prettier printing for internal patterns

    MetaCannotDependOn m ps i -> fsep $
      pwords "The metavariable" ++ [prettyTCM $ MetaV m []] ++
      pwords "cannot depend on" ++ [pvar i] ++
      pwords "because it" ++ deps
        where
          pvar = prettyTCM . I.var
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

    NoBindingForBuiltin x
      | elem x [builtinZero, builtinSuc] -> fsep $
        pwords "No binding for builtin " ++ [text x <> comma] ++
        pwords ("use {-# BUILTIN " ++ builtinNat ++ " name #-} to bind builtin natural " ++
                "numbers to the type 'name'")
      | otherwise -> fsep $
        pwords "No binding for builtin thing" ++ [text x <> comma] ++
        pwords ("use {-# BUILTIN " ++ x ++ " name #-} to bind it to 'name'")

    NoSuchPrimitiveFunction x -> fsep $
      pwords "There is no primitive function called" ++ [text x]

    BuiltinInParameterisedModule x -> fwords $
      "The BUILTIN pragma cannot appear inside a bound context " ++
      "(for instance, in a parameterised module or as a local declaration)"

    IllegalLetInTelescope tb -> fsep $
      -- pwords "The binding" ++
      [pretty tb] ++
      pwords " is not allowed in a telescope here."

    NoRHSRequiresAbsurdPattern ps -> fwords $
      "The right-hand side can only be omitted if there " ++
      "is an absurd pattern, () or {}, in the left-hand side."

    AbsurdPatternRequiresNoRHS ps -> fwords $
      "The right-hand side must be omitted if there " ++
      "is an absurd pattern, () or {}, in the left-hand side."

    LocalVsImportedModuleClash m -> fsep $
      pwords "The module" ++ [prettyTCM m] ++
      pwords "can refer to either a local module or an imported module"

    SolvedButOpenHoles ->
      text "Module cannot be imported since it has open interaction points"

    UnsolvedMetas rs ->
      fsep ( pwords "Unsolved metas at the following locations:" )
      $$ nest 2 (vcat $ map prettyTCM rs)

    UnsolvedConstraints cs ->
      fsep ( pwords "Failed to solve the following constraints:" )
      $$ nest 2 (vcat $ map prettyConstraint cs)

      where prettyConstraint :: ProblemConstraint -> TCM Doc
            prettyConstraint c = f (prettyTCM c)
              where
              r   = getRange c
              f d = if null $ P.pretty r
                    then d
                    else d $$ nest 4 (text "[ at" <+> prettyTCM r <+> text "]")

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
      fsep ( pwords "Multiple possible sources for module"
             ++ [prettyTCM x] ++ pwords "found:"
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

    BothWithAndRHS -> fsep $ pwords "Unexpected right hand side"

    NotInScope xs ->
      fsep (pwords "Not in scope:") $$ nest 2 (vcat $ map name xs)
      where
      name x = fsep [ pretty x
                    , text "at" <+> prettyTCM (getRange x)
                    , suggestion (P.prettyShow x)
                    ]
      suggestion s
        | elem ':' s    = parens $ text "did you forget space around the ':'?"
        | elem "->" two = parens $ text "did you forget space around the '->'?"
        | otherwise     = empty
        where
          two = zipWith (\a b -> [a,b]) s (tail s)

    NoSuchModule x -> fsep $ pwords "No such module" ++ [pretty x]

    AmbiguousName x ys -> vcat
      [ fsep $ pwords "Ambiguous name" ++ [pretty x <> text "."] ++
               pwords "It could refer to any one of"
      , nest 2 $ vcat $ map nameWithBinding ys
      , fwords "(hint: Use C-c C-w (in Emacs) if you want to know why)"
      ]

    AmbiguousModule x ys -> vcat
      [ fsep $ pwords "Ambiguous module name" ++ [pretty x <> text "."] ++
               pwords "It could refer to any one of"
      , nest 2 $ vcat $ map help ys
      , fwords "(hint: Use C-c C-w (in Emacs) if you want to know why)"
      ]
      where
        help :: ModuleName -> TCM Doc
        help m = do
          b <- isDatatypeModule m
          sep [prettyTCM m, if b then text "(datatype module)" else empty]

    UninstantiatedModule x -> fsep (
      pwords "Cannot access the contents of the parameterised module"
      ++ [pretty x <> text "."] ++
      pwords "To do this the module first has to be instantiated. For instance:"
        ) $$ nest 2 (hsep [ text "module", pretty x <> text "'", text "=", pretty x, text "e1 .. en" ])

    ClashingDefinition x y -> fsep $
      pwords "Multiple definitions of" ++ [pretty x <> text "."] ++
      pwords "Previous definition at"
      ++ [prettyTCM $ nameBindingSite $ qnameName y]

    ClashingModule m1 m2 -> fsep $
      pwords "The modules" ++ [prettyTCM m1, text "and", prettyTCM m2]
      ++ pwords "clash."

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
      pwords "where M is a module name. The expression"
      ++ [pretty e, text "doesn't."]

    FieldOutsideRecord -> fsep $
      pwords "Field appearing outside record declaration."

    InvalidPattern p -> fsep $
      pretty p : pwords "is not a valid pattern"

    RepeatedVariablesInPattern xs -> fsep $
      pwords "Repeated variables in pattern:" ++ map pretty xs

    NotAnExpression e -> fsep $
      [pretty e] ++ pwords "is not a valid expression."

    NotAValidLetBinding nd -> fwords $
      "Not a valid let-declaration"

    NothingAppliedToHiddenArg e -> fsep $
      [pretty e] ++ pwords "cannot appear by itself. It needs to be the argument to" ++
      pwords "a function expecting an implicit argument."

    NothingAppliedToInstanceArg e -> fsep $
      [pretty e] ++ pwords "cannot appear by itself. It needs to be the argument to" ++
      pwords "a function expecting an instance argument."

    NoParseForApplication es -> fsep (
      pwords "Could not parse the application" ++ [pretty $ C.RawApp noRange es])

    AmbiguousParseForApplication es es' -> fsep (
      pwords "Don't know how to parse" ++ [pretty_es <> (text ".")] ++
      pwords "Could mean any one of:"
      ) $$ nest 2 (vcat $ map pretty' es')
      where
        pretty_es :: TCM Doc
        pretty_es = pretty $ C.RawApp noRange es

        pretty' :: C.Expr -> TCM Doc
        pretty' e = do
          p1 <- pretty_es
          p2 <- pretty e
          if show p1 == show p2 then unambiguous e else pretty e

        unambiguous :: C.Expr -> TCM Doc
        unambiguous e@(C.OpApp r op _ xs)
          | all (isOrdinary . namedArg) xs =
            pretty $
              foldl (C.App r) (C.Ident op) $
                (map . fmap . fmap) fromOrdinary xs
          | any (isPlaceholder . namedArg) xs =
              pretty e <+> text "(section)"
        unambiguous e = pretty e

        isOrdinary :: MaybePlaceholder (C.OpApp e) -> Bool
        isOrdinary (NoPlaceholder (C.Ordinary _)) = True
        isOrdinary _                              = False

        fromOrdinary :: MaybePlaceholder (C.OpApp e) -> e
        fromOrdinary (NoPlaceholder (C.Ordinary e)) = e
        fromOrdinary _                              = __IMPOSSIBLE__

        isPlaceholder :: MaybePlaceholder a -> Bool
        isPlaceholder Placeholder{}   = True
        isPlaceholder NoPlaceholder{} = False

    BadArgumentsToPatternSynonym x -> fsep $
      pwords "Bad arguments to pattern synonym " ++ [prettyTCM x]

    TooFewArgumentsToPatternSynonym x -> fsep $
      pwords "Too few arguments to pattern synonym " ++ [prettyTCM x]

    UnusedVariableInPatternSynonym -> fsep $
      pwords "Unused variable in pattern synonym."

    NoParseForLHS IsLHS p -> fsep (
      pwords "Could not parse the left-hand side" ++ [pretty p])

    NoParseForLHS IsPatSyn p -> fsep (
      pwords "Could not parse the pattern synonym" ++ [pretty p])

{- UNUSED
    NoParseForPatternSynonym p -> fsep $
      pwords "Could not parse the pattern synonym" ++ [pretty p]
-}

    AmbiguousParseForLHS lhsOrPatSyn p ps -> fsep (
      pwords "Don't know how to parse" ++ [pretty_p <> text "."] ++
      pwords "Could mean any one of:"
      ) $$ nest 2 (vcat $ map pretty' ps)
      where
        pretty_p :: TCM Doc
        pretty_p = pretty p

        pretty' :: C.Pattern -> TCM Doc
        pretty' p' = do
          p1 <- pretty_p
          p2 <- pretty p'
          pretty $ if show p1 == show p2 then unambiguousP p' else p'

        -- the entire pattern is shown, not just the ambiguous part,
        -- so we need to dig in order to find the OpAppP's.
        unambiguousP :: C.Pattern -> C.Pattern
        unambiguousP (C.AppP x y)         = C.AppP (unambiguousP x) $ (fmap.fmap) unambiguousP y
        unambiguousP (C.HiddenP r x)      = C.HiddenP r $ fmap unambiguousP x
        unambiguousP (C.InstanceP r x)    = C.InstanceP r $ fmap unambiguousP x
        unambiguousP (C.ParenP r x)       = C.ParenP r $ unambiguousP x
        unambiguousP (C.AsP r n x)        = C.AsP r n $ unambiguousP x
        unambiguousP (C.OpAppP r op _ xs) = foldl C.AppP (C.IdentP op) xs
        unambiguousP e                    = e

    OperatorInformation sects err ->
      prettyTCM err
        $+$
      fsep (pwords "Operators used in the grammar:")
        $$
      nest 2
        (if null sects then text "None" else
         vcat (map text $
               lines $
               Boxes.render $
               (\(col1, col2, col3) ->
                   Boxes.hsep 1 Boxes.top $
                   map (Boxes.vcat Boxes.left) [col1, col2, col3]) $
               unzip3 $
               map prettySect $
               sortBy (compare `on` show . notaName . sectNotation) $
               filter (not . closedWithoutHoles) sects))
      where
      trimLeft  = dropWhile isNormalHole
      trimRight = reverse . dropWhile isNormalHole . reverse

      closedWithoutHoles sect =
        sectKind sect == NonfixNotation
          &&
        null [ () | NormalHole {} <- trimLeft $ trimRight $
                                       notation (sectNotation sect) ]

      prettyName n = Boxes.text $
        P.render (P.pretty n) ++
        " (" ++ P.render (P.pretty (nameBindingSite n)) ++ ")"

      prettySect sect =
        ( Boxes.text (P.render (P.pretty section))
            Boxes.//
          strut
        , Boxes.text
            ("(" ++
             kind ++ " " ++
             (if notaIsOperator nota
              then "operator"
              else "notation") ++
             (if sectIsSection sect
              then " section"
              else "") ++
             (case sectLevel sect of
                Nothing          -> ""
                Just Unrelated   -> ", unrelated"
                Just (Related n) -> ", level " ++ show n) ++
             ")")
            Boxes.//
          strut
        , Boxes.text "["
            Boxes.<>
          Boxes.vcat Boxes.left
            (map (\n -> prettyName n Boxes.<> Boxes.text ",") names ++
             [prettyName name Boxes.<> Boxes.text "]"])
        )
        where
        nota    = sectNotation sect
        section = trim (notation nota)

        trim = case sectKind sect of
          InfixNotation   -> trimLeft . trimRight
          PrefixNotation  -> trimRight
          PostfixNotation -> trimLeft
          NonfixNotation  -> id
          NoNotation      -> __IMPOSSIBLE__

        (names, name) = case Set.toList $ notaNames nota of
          [] -> __IMPOSSIBLE__
          ns -> (init ns, last ns)

        strut = Boxes.emptyBox (length names) 0

        kind = case sectKind sect of
          PrefixNotation  -> "prefix"
          PostfixNotation -> "postfix"
          NonfixNotation  -> "closed"
          NoNotation      -> __IMPOSSIBLE__
          InfixNotation   ->
            case fixityAssoc $ notaFixity nota of
              NonAssoc   -> "infix"
              LeftAssoc  -> "infixl"
              RightAssoc -> "infixr"

    OperatorChangeMessage err ->
      prettyTCM err
        $+$
      fsep (pwords $
        "(the treatment of operators has changed, so code that used " ++
        "to parse may have to be changed)")

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
            prettyTCM f <+> fsep (map prettyArg ps)

          nicify f ps = do
            showImp <- showImplicitArguments
            if showImp
              then return ps
              else return ps  -- TODO: remove implicit arguments which aren't constructors

    CoverageCantSplitOn c tel cIxs gIxs
      | length cIxs /= length gIxs -> __IMPOSSIBLE__
      | otherwise                  -> addCtxTel tel $ vcat (
          [ fsep $ pwords "I'm not sure if there should be a case for the constructor" ++
                   [prettyTCM c <> text ","] ++
                   pwords "because I get stuck when trying to solve the following" ++
                   pwords "unification problems (inferred index ≟ expected index):"
          ] ++
          zipWith (\c g -> nest 2 $ prettyTCM c <+> text "≟" <+> prettyTCM g) cIxs gIxs)

    CoverageCantSplitIrrelevantType a -> fsep $
      pwords "Cannot split on argument of irrelevant datatype" ++ [prettyTCM a]


    CoverageCantSplitType a -> fsep $
      pwords "Cannot split on argument of non-datatype" ++ [prettyTCM a]

    CoverageNoExactSplit f cs -> fsep $
      pwords "Exact splitting is enabled, but not all clauses can be preserved as definitional equalities in the translation to a case tree"

    SplitError e -> prettyTCM e

    WithoutKError a u v -> fsep $
      pwords "Cannot eliminate reflexive equation" ++ [prettyTCM u] ++
      pwords "=" ++ [prettyTCM v] ++ pwords "of type" ++ [prettyTCM a] ++
      pwords "because K has been disabled."

    NotStrictlyPositive d ocs -> fsep $
      pwords "The datatype" ++ [prettyTCM d] ++
      pwords "is not strictly positive, because"
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
        th n = prettyTCM (n - 1) <> text "th"

        com []    = empty
        com (_:_) = comma

    IFSNoCandidateInScope t -> fsep $
      pwords "No variable of type" ++ [prettyTCM t] ++ pwords "was found in scope."

    UnquoteFailed e -> case e of
      BadVisibility msg arg -> fsep $
        pwords $ "Unable to unquote the argument. It should be `" ++ msg ++ "'."

      ConInsteadOfDef x def con -> fsep $
        pwords ("Use " ++ con ++ " instead of " ++ def ++ " for constructor") ++
        [prettyTCM x]

      DefInsteadOfCon x def con -> fsep $
        pwords ("Use " ++ def ++ " instead of " ++ con ++ " for non-constructor")
        ++ [prettyTCM x]

      NotAConstructor kind t ->
        fwords "Unable to unquote the term"
        $$ nest 2 (prettyTCM t)
        $$ fwords ("of type " ++ kind ++ ". Reason: not a constructor.")

      NotALiteral kind t ->
        fwords "Unable to unquote the term"
        $$ nest 2 (prettyTCM t)
        $$ fwords ("of type " ++ kind ++ ". Reason: not a literal value.")

      BlockedOnMeta m -> fsep $
        pwords $ "Unquote failed because of unsolved meta variables."

      UnquotePanic err -> __IMPOSSIBLE__

    SafeFlagPostulate e -> fsep $
      pwords "Cannot postulate" ++ [pretty e] ++ pwords "with safe flag"

    SafeFlagPragma xs ->
      let plural | length xs == 1 = ""
                 | otherwise      = "s"
      in fsep $ [fwords ("Cannot set OPTION pragma" ++ plural)]
                ++ map text xs ++ [fwords "with safe flag."]

    SafeFlagNoTerminationCheck -> fsep $
      pwords "Cannot use NO_TERMINATION_CHECK pragma with safe flag."

    SafeFlagNonTerminating -> fsep $
      pwords "Cannot use NON_TERMINATING pragma with safe flag."

    SafeFlagTerminating -> fsep $
      pwords "Cannot use TERMINATING pragma with safe flag."

    SafeFlagPrimTrustMe -> fsep (pwords "Cannot use primTrustMe with safe flag")

    NeedOptionCopatterns -> fsep $
      pwords "Option --copatterns needed to enable destructor patterns"
    NeedOptionRewriting  -> fsep $
      pwords "Option --rewriting needed to add and use rewrite rules"

    where
    mpar n args
      | n > 0 && not (null args) = parens
      | otherwise                = id

    prettyArg :: Arg I.Pattern -> TCM Doc
    prettyArg (Arg info x) = case getHiding info of
      Hidden    -> braces $ prettyPat 0 x
      Instance  -> dbraces $ prettyPat 0 x
      NotHidden -> prettyPat 1 x

    prettyPat :: Integer -> I.Pattern -> TCM Doc
    prettyPat _ (I.VarP _) = text "_"
    prettyPat _ (I.DotP _) = text "._"
    prettyPat n (I.ConP c _ args) =
      mpar n args $
        prettyTCM c <+> fsep (map (prettyArg . fmap namedThing) args)
    prettyPat _ (I.LitP l) = prettyTCM l
    prettyPat _ (I.ProjP p) = prettyTCM p

notCmp :: Comparison -> TCM Doc
notCmp cmp = text "!" <> prettyTCM cmp

-- | Print two terms that are supposedly unequal.
--   If they print to the same identifier, add some explanation
--   why they are different nevertheless.
prettyInEqual :: Term -> Term -> TCM (Doc, Doc, Doc)
prettyInEqual t1 t2 = do
  d1 <- prettyTCM t1
  d2 <- prettyTCM t2
  (d1, d2,) <$> do
     -- if printed differently, no extra explanation needed
    if P.render d1 /= P.render d2 then empty else do
      (v1, v2) <- instantiate (t1, t2)
      case (ignoreSharing v1, ignoreSharing v2) of
        (I.Var i1 _, I.Var i2 _)
          | i1 == i2  -> __IMPOSSIBLE__   -- if they're actually the same we would get the error on the arguments instead
          | otherwise -> varVar i1 i2
        (I.Def{}, I.Con{}) -> __IMPOSSIBLE__  -- ambiguous identifiers
        (I.Con{}, I.Def{}) -> __IMPOSSIBLE__
        (I.Var{}, I.Def{}) -> varDef
        (I.Def{}, I.Var{}) -> varDef
        (I.Var{}, I.Con{}) -> varCon
        (I.Con{}, I.Var{}) -> varCon
        _                  -> empty
  where
    varDef, varCon :: TCM Doc
    varDef = parens $ fwords "because one is a variable and one a defined identifier"
    varCon = parens $ fwords "because one is a variable and one a constructor"

    varVar :: Int -> Int -> TCM Doc
    varVar i j = parens $ fwords $
                   "because one has deBruijn index " ++ show i
                   ++ " and the other " ++ show j

class PrettyUnequal a where
  prettyUnequal :: a -> TCM Doc -> a -> TCM Doc

instance PrettyUnequal Term where
  prettyUnequal t1 ncmp t2 = do
    (d1, d2, d) <- prettyInEqual t1 t2
    fsep $ return d1 : ncmp : return d2 : return d : []

instance PrettyUnequal Type where
  prettyUnequal t1 ncmp t2 = prettyUnequal (unEl t1) ncmp (unEl t2)

instance PrettyTCM SplitError where
  prettyTCM err = case err of
    NotADatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot pattern match on non-datatype" ++ [prettyTCM t]

    IrrelevantDatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot pattern match on datatype" ++ [prettyTCM t] ++
      pwords "since it is declared irrelevant"

    CoinductiveDatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot pattern match on the coinductive type" ++ [prettyTCM t]

{- UNUSED
    NoRecordConstructor t -> fsep $
      pwords "Cannot pattern match on record" ++ [prettyTCM t] ++
      pwords "because it has no constructor"
 -}

    CantSplit c tel cIxs gIxs ->
      prettyTCM $ CoverageCantSplitOn c tel cIxs gIxs

    GenericSplitError s -> fsep $ pwords "Split failed:" ++ pwords s

instance PrettyTCM Call where
  prettyTCM c = case c of
    CheckClause t cl -> fsep $
      pwords "when checking that the clause"
      ++ [AP.prettyA cl] ++ pwords "has type" ++ [prettyTCM t]

    CheckPattern p tel t -> addCtxTel tel $ fsep $
      pwords "when checking that the pattern"
      ++ [prettyA p] ++ pwords "has type" ++ [prettyTCM t]

    CheckLetBinding b -> fsep $
      pwords "when checking the let binding" ++ [AP.prettyA b]

    InferExpr e -> fsep $ pwords "when inferring the type of" ++ [prettyA e]

    CheckExprCall e t -> fsep $
      pwords "when checking that the expression"
      ++ [prettyA e] ++ pwords "has type" ++ [prettyTCM t]

    IsTypeCall e s -> fsep $
      pwords "when checking that the expression"
      ++ [prettyA e] ++ pwords "is a type of sort" ++ [prettyTCM s]

    IsType_ e -> fsep $
      pwords "when checking that the expression"
      ++ [prettyA e] ++ pwords "is a type"

    CheckArguments r es t0 t1 -> fsep $
      pwords "when checking that" ++
      map hPretty es ++
      pwords (singPlural es "is a valid argument" "are valid arguments") ++
      pwords "to a function of type" ++
      [prettyTCM t0]

    CheckRecDef _ x ps cs ->
      fsep $ pwords "when checking the definition of" ++ [prettyTCM x]

    CheckDataDef _ x ps cs ->
      fsep $ pwords "when checking the definition of" ++ [prettyTCM x]

    CheckConstructor d _ _ (A.Axiom _ _ _ c _) -> fsep $
      pwords "when checking the constructor" ++ [prettyTCM c] ++
      pwords "in the declaration of" ++ [prettyTCM d]

    CheckConstructor{} -> __IMPOSSIBLE__

    CheckFunDef _ f _ ->
      fsep $ pwords "when checking the definition of" ++ [prettyTCM f]

    CheckPragma _ p ->
      fsep $ pwords "when checking the pragma"
             ++ [prettyA $ RangeAndPragma noRange p]

    CheckPrimitive _ x e -> fsep $
      pwords "when checking that the type of the primitive function" ++
      [prettyTCM x] ++ pwords "is" ++ [prettyA e]

    CheckWithFunctionType e -> fsep $
      pwords "when checking that the type" ++
      [prettyA e] ++ pwords "of the generated with function is well-formed"

    CheckDotPattern e v -> fsep $
      pwords "when checking that the given dot pattern" ++ [prettyA e] ++
      pwords "matches the inferred value" ++ [prettyTCM v]

    CheckPatternShadowing c -> fsep $
      pwords "when checking the clause" ++ [AP.prettyA c]

    InferVar x ->
      fsep $ pwords "when inferring the type of" ++ [prettyTCM x]

    InferDef _ x ->
      fsep $ pwords "when inferring the type of" ++ [prettyTCM x]

    CheckIsEmpty r t ->
      fsep $ pwords "when checking that" ++ [prettyTCM t] ++
             pwords "has no constructors"

    ScopeCheckExpr e -> fsep $ pwords "when scope checking" ++ [pretty e]

    ScopeCheckDeclaration d ->
      fwords "when scope checking the declaration" $$
      nest 2 (pretty $ simpleDecl d)

    ScopeCheckLHS x p ->
      fsep $ pwords "when scope checking the left-hand side" ++ [pretty p] ++
             pwords "in the definition of" ++ [pretty x]

    NoHighlighting -> empty

    SetRange r -> fsep (pwords "when doing something at") <+> prettyTCM r

    CheckSectionApplication _ m1 modapp -> fsep $
      pwords "when checking the module application" ++
      [prettyA $ A.Apply info m1 modapp empty empty]
      where
      info = A.ModuleInfo noRange noRange Nothing Nothing Nothing

    where
    hPretty :: Arg (Named_ Expr) -> TCM Doc
    hPretty a = pretty =<< abstractToConcreteCtx (hiddenArgumentCtx (getHiding a)) a

    simpleDecl = D.notSoNiceDeclaration

---------------------------------------------------------------------------
-- * Natural language
---------------------------------------------------------------------------

class Verbalize a where
  verbalize :: a -> String

instance Verbalize Hiding where
  verbalize h =
    case h of
      Hidden    -> "hidden"
      NotHidden -> "visible"
      Instance  -> "instance"

instance Verbalize Relevance where
  verbalize r =
    case r of
      Relevant   -> "relevant"
      Irrelevant -> "irrelevant"
      NonStrict  -> "shape-irrelevant"
      Forced{}   -> __IMPOSSIBLE__
      UnusedArg  -> __IMPOSSIBLE__

-- | Indefinite article.
data Indefinite a = Indefinite a

instance Verbalize a => Verbalize (Indefinite a) where
  verbalize (Indefinite a) =
    case verbalize a of
      "" -> ""
      w@(c:cs) | c `elem` ['a','e','i','o'] -> "an " ++ w
               | otherwise                  -> "a " ++ w
      -- Aarne Ranta would whip me if he saw this.

singPlural :: Sized a => a -> c -> c -> c
singPlural xs singular plural = if size xs == 1 then singular else plural
