{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking

module Agda.Interaction.JSON.TypeChecking where

import Data.Aeson
import Data.Function (on)
import Data.List (nub, sortBy)
import Data.Maybe (isJust)
import Data.Char (toLower)
import qualified Data.Set as Set

import Agda.Interaction.JSON.Encoding
import Agda.Interaction.JSON.Syntax
import Agda.Interaction.JSON.Utils

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Common as C
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Internal (dummySort)
import qualified Agda.Syntax.Position as P
import qualified Agda.Syntax.Scope.Monad as S
import qualified Agda.Syntax.Scope.Base as S

import Agda.Syntax.Position (Range, Range'(..))

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Context (inTopContext)
import Agda.TypeChecking.Substitute (Abstract(..), raise)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty (PrettyTCM(..), prettyA, prettyPattern)
import Agda.TypeChecking.Telescope (ifPiType)

import Agda.Utils.Pretty (render, pretty, prettyShow)
import Agda.Utils.FileName (filePath)
import Agda.Utils.Size (size)
import Agda.Utils.List
import Agda.Utils.NonemptyList (NonemptyList(..), toList)

#include "undefined.h"
import Agda.Utils.Impossible

--------------------------------------------------------------------------------

instance EncodeTCM TCErr where
  encodeTCM (TypeError _ closure) = obj
    [ "kind"      @= String "TypeError"
    , "range"     @= envRange (clEnv closure)
    , "typeError" #= encodeTCM (clValue closure)
    ]
  encodeTCM (Exception range doc) = obj
    [ "kind"        @= String "Exception"
    , "range"       @= range
    , "description" @= toJSON (render doc)
    ]
  encodeTCM (IOException _ range exception) = obj
    [ "kind"        @= String "IOException"
    , "range"       @= range
    , "exception"   @= toJSON (show exception)
    ]
  encodeTCM PatternErr = obj
    [ "kind"        @= String "PatternErr"
    , "range"       @= (NoRange :: Range)
    ]

--------------------------------------------------------------------------------

instance EncodeTCM TypeError where
  encodeTCM err = case err of
    InternalError s -> obj
      [ "kind"    @= String "InternalError"
      , "message" @= s
      ]

    NotImplemented s -> obj
      [ "kind"    @= String "NotImplemented"
      , "message" @= s
      ]

    NotSupported s -> obj
      [ "kind"    @= String "NotSupported"
      , "message" @= s
      ]

    CompilationError s -> obj
      [ "kind"    @= String "CompilationError"
      , "message" @= s
      ]

    GenericError s -> obj
      [ "kind"    @= String "GenericError"
      , "message" @= s
      ]

    GenericDocError d -> obj
      [ "kind"    @= String "GenericDocError"
      , "message" @= (render d)
      ]

    TerminationCheckFailed because -> do
      -- topLevelModuleDropper produces a function which drops the filename
      -- component of the qualified name.
      dropTopLevel <- topLevelModuleDropper
      let functionNames = map
            (pretty . dropTopLevel)
            (concatMap termErrFunctions because)
      problematicCalls <- fmap nub
            $ mapM prettyTCM
            $ sortBy (compare `on` callInfoRange)
            $ (concatMap termErrCalls because)
      obj
        [ "kind"              @= String "TerminationCheckFailed"
        , "functions"         @= functionNames
        , "problematicCalls"  @= problematicCalls
        ]

    PropMustBeSingleton -> obj
      [ "kind"  @= String "PropMustBeSingleton" ]

    DataMustEndInSort term -> obj
      [ "kind"  @= String "DataMustEndInSort"
      , "term"  #= prettyTCM term
      ]

    ShouldEndInApplicationOfTheDatatype t -> obj
      [ "kind"  @= String "ShouldEndInApplicationOfTheDatatype"
      , "type"  #= prettyTCM t
      ]

    ShouldBeAppliedToTheDatatypeParameters s t -> obj
      [ "kind"      @= String "ShouldEndInApplicationOfTheDatatype"
      , "expected"  #= prettyTCM s
      , "given"     #= prettyTCM t
      ]

    ShouldBeApplicationOf t q -> obj
      [ "kind" @= String "ShouldBeApplicationOf"
      , "type" #= prettyTCM t
      , "name" #= prettyTCM q
      ]

    ShouldBeRecordType t -> obj
      [ "kind"  @= String "ShouldBeRecordType"
      , "type"  #= prettyTCM t
      ]

    ShouldBeRecordPattern p -> obj
      [ "kind"    @= String "ShouldBeRecordPattern"
      , "pattern" #= prettyTCM p
      ]

    NotAProjectionPattern p -> obj
      [ "kind"    @= String "NotAProjectionPattern"
      , "pattern" #= prettyA p
      ]

    DifferentArities -> obj
      [ "kind" @= String "DifferentArities" ]

    WrongHidingInLHS -> obj
      [ "kind" @= String "WrongHidingInLHS" ]

    WrongHidingInLambda t -> obj
      [ "kind" @= String "WrongHidingInLambda"
      , "type" #= prettyTCM t
      ]

    WrongIrrelevanceInLambda -> obj
      [ "kind" @= String "WrongIrrelevanceInLambda" ]

    WrongNamedArgument a -> obj
      [ "kind" @= String "WrongNamedArgument"
      , "args" #= prettyTCM a
      ]

    WrongHidingInApplication t -> obj
      [ "kind" @= String "WrongHidingInApplication"
      , "type" #= prettyTCM t
      ]

    WrongInstanceDeclaration -> obj
      [ "kind" @= String "WrongInstanceDeclaration" ]

    HidingMismatch h h' -> obj
      [ "kind"      @= String "HidingMismatch"
      , "expected"  @= verbalize (Indefinite h')
      , "given"     @= verbalize (Indefinite h)
      ]

    RelevanceMismatch r r' -> obj
      [ "kind"      @= String "RelevanceMismatch"
      , "expected"  @= verbalize (Indefinite r')
      , "given"     @= verbalize (Indefinite r)
      ]

    UninstantiatedDotPattern e -> obj
        [ "kind" @= String "UninstantiatedDotPattern"
        , "expr" #= prettyTCM e
        ]

    ForcedConstructorNotInstantiated p -> obj
        [ "kind"    @= String "ForcedConstructorNotInstantiated"
        , "pattern" #= prettyA p
        ]

    IlltypedPattern p a -> ifPiType a yes no
      where
        yes dom abs = obj
          [ "kind"      @= String "IlltypedPattern"
          , "isPiType"  @= True
          , "pattern"   #= prettyA p
          , "dom"       #= prettyTCM dom
          , "abs"       @= show abs
          ]
        no t = obj
          [ "kind"      @= String "IlltypedPattern"
          , "isPiType"  @= False
          , "pattern"   #= prettyA p
          , "type"      #= prettyTCM t
          ]

    IllformedProjectionPattern p -> obj
        [ "kind"    @= String "IllformedProjectionPattern"
        , "pattern" #= prettyA p
        ]

    CannotEliminateWithPattern p a -> do
      if isJust (A.isProjP p) then
        obj
          [ "kind"          @= String "CannotEliminateWithPattern"
          , "isProjection"  @= True
          , "pattern"       #= prettyA p
          ]
      else
        obj
          [ "kind"          @= String "CannotEliminateWithPattern"
          , "isProjection"  @= False
          , "pattern"       #= prettyA p
          , "patternKind"   @= kindOfPattern (C.namedArg p)
          ]

    WrongNumberOfConstructorArguments name expected given -> obj
      [ "kind"      @= String "WrongNumberOfConstructorArguments"
      , "name"      #= prettyTCM name
      , "expected"  #= prettyTCM expected
      , "given"     #= prettyTCM given
      ]

    CantResolveOverloadedConstructorsTargetingSameDatatype datatype ctrs -> do
      obj
        [ "kind"          @= String "CantResolveOverloadedConstructorsTargetingSameDatatype"
        , "datatype"      #= prettyTCM (I.qnameToConcrete datatype)
        , "constructors"  #= mapM prettyTCM ctrs
        ]

    DoesNotConstructAnElementOf c t -> obj
      [ "kind"        @= String "DoesNotConstructAnElementOf"
      , "constructor" #= prettyTCM c
      , "type"        #= prettyTCM t
      ]

    ConstructorPatternInWrongDatatype c d -> obj
      [ "kind"        @= String "ConstructorPatternInWrongDatatype"
      , "constructor" #= prettyTCM c
      , "datatype"    #= prettyTCM d
      ]

    ShadowedModule x [] -> __IMPOSSIBLE__
    ShadowedModule x ms -> do
      (r, m) <- handleShadowedModule x ms
      obj
        [ "kind"        @= String "ShadowedModule"
        , "duplicated"  #= prettyTCM x
        , "previous"    #= prettyTCM r
        , "isDatatype"  #= S.isDatatypeModule m
        ]

    ModuleArityMismatch m I.EmptyTel args -> obj
      [ "kind"            @= String "ModuleArityMismatch"
      , "module"          #= prettyTCM m
      , "isParameterized" @= False
      ]
    ModuleArityMismatch m tel@(I.ExtendTel _ _) args -> obj
      [ "kind"            @= String "ModuleArityMismatch"
      , "module"          #= prettyTCM m
      , "isParameterized" @= True
      , "telescope"       #= prettyTCM tel
      ]

    ShouldBeEmpty t ps -> obj
      [ "kind"            @= String "ShouldBeEmpty"
      , "type"            #= prettyTCM t
      , "patterns"        #= mapM (prettyPattern 0) ps
      ]

    ShouldBeASort t -> obj
      [ "kind"            @= String "ShouldBeASort"
      , "type"            #= prettyTCM t
      ]

    ShouldBePi t -> obj
      [ "kind"            @= String "ShouldBePi"
      , "type"            #= prettyTCM t
      ]

    ShouldBePath t -> obj
      [ "kind"            @= String "ShouldBePath"
      , "type"            #= prettyTCM t
      ]

    NotAProperTerm -> obj
      [ "kind"            @= String "NotAProperTerm"
      ]

    InvalidTypeSort s -> obj
      [ "kind"            @= String "InvalidTypeSort"
      , "sort"            #= prettyTCM s
      ]

    InvalidType t -> obj
      [ "kind"            @= String "InvalidType"
      , "type"            #= prettyTCM t
      ]

    FunctionTypeInSizeUniv t -> obj
      [ "kind"            @= String "FunctionTypeInSizeUniv"
      , "term"            #= prettyTCM t
      ]

    SplitOnIrrelevant t ->obj
      [ "kind"            @= String "SplitOnIrrelevant"
      , "term"            @= verbalize (C.getRelevance t)
      , "type"            #= prettyTCM (C.unDom t)
      ]

    SplitOnNonVariable term typ ->obj
      [ "kind"            @= String "SplitOnNonVariable"
      , "term"            #= prettyTCM term
      , "type"            #= prettyTCM typ
      ]


    DefinitionIsIrrelevant x -> obj
      [ "kind"            @= String "DefinitionIsIrrelevant"
      , "name"            #= prettyTCM x
      ]

    VariableIsIrrelevant x -> obj
      [ "kind"            @= String "VariableIsIrrelevant"
      , "name"            #= prettyTCM x
      ]

    UnequalBecauseOfUniverseConflict cmp s t -> obj
      [ "kind"            @= String "UnequalBecauseOfUniverseConflict"
      , "comparison"      #= prettyTCM cmp
      , "term1"           #= prettyTCM s
      , "term2"           #= prettyTCM t
      ]


    UnequalTerms cmp s t a -> case refineUnequalTerms cmp s t of
      Just err -> encodeTCM err
      Nothing -> do
        (_, _, d) <- prettyInEqual s t
        obj
          [ "kind"            @= String "UnequalTerms"
          , "comparison"      #= prettyTCM cmp
          , "term1"           #= prettyTCM s
          , "term2"           #= prettyTCM t
          , "type"            #= prettyTCM a
          , "reason"          @= d
          ]

    UnequalTypes cmp a b -> obj
      [ "kind"            @= String "UnequalTypes"
      , "comparison"      #= prettyTCM cmp
      , "type1"           #= prettyTCM a
      , "type2"           #= prettyTCM b
      , "message"         #= prettyUnequal a (notCmp cmp) b
      ]

    UnequalRelevance cmp a b -> obj
      [ "kind"            @= String "UnequalRelevance"
      , "comparison"      #= prettyTCM cmp
      , "term1"           #= prettyTCM a
      , "term2"           #= prettyTCM b
      ]

    UnequalHiding a b -> obj
      [ "kind"            @= String "UnequalHiding"
      , "term1"           #= prettyTCM a
      , "term2"           #= prettyTCM b
      ]

    UnequalSorts a b -> obj
      [ "kind"            @= String "UnequalSorts"
      , "sort1"           #= prettyTCM a
      , "sort2"           #= prettyTCM b
      ]

    NotLeqSort a b -> obj
      [ "kind"            @= String "NotLeqSort"
      , "sort1"           #= prettyTCM a
      , "sort2"           #= prettyTCM b
      ]

    TooFewFields record fields -> obj
      [ "kind"            @= String "TooFewFields"
      , "record"          #= prettyTCM record
      , "fields"          @= map pretty fields
      ]

    TooManyFields record fields -> obj
      [ "kind"            @= String "TooManyFields"
      , "record"          #= prettyTCM record
      , "fields"          @= map pretty fields
      ]

    DuplicateConstructors xs -> obj
      [ "kind"            @= String "DuplicateConstructors"
      , "constructors"    @= map pretty xs
      ]

    DuplicateFields xs -> obj
      [ "kind"            @= String "DuplicateFields"
      , "fields"          @= map pretty xs
      ]

    WithOnFreeVariable expr term -> do
      de <- prettyA expr
      dt <- prettyTCM term
      if show de == show dt
        then obj
          [ "kind"            @= String "WithOnFreeVariable"
          , "variable"        @= dt
          ]
        else obj
          [ "kind"            @= String "WithOnFreeVariable"
          , "variable"        @= dt
          , "expression"      @= de
          ]

    UnexpectedWithPatterns xs -> obj
      [ "kind"            @= String "UnexpectedWithPatterns"
      , "patterns"        #= mapM prettyA xs
      ]

    -- The arguments are the meta variable, the parameters it can
    -- depend on and the paratemeter that it wants to depend on.
    MetaCannotDependOn meta ps i -> obj
      [ "kind"            @= String "MetaCannotDependOn"
      , "meta"            #= prettyTCM (I.MetaV meta [])
      , "wantsToDependOn" #= prettyTCM (I.var i)
      , "canDepdendOn"    #= mapM prettyTCM (map I.var ps)
      ]

    MetaOccursInItself meta -> obj
      [ "kind"            @= String "MetaOccursInItself"
      , "meta"            #= prettyTCM (I.MetaV meta [])
      ]

    MetaIrrelevantSolution meta term -> obj
      [ "kind"            @= String "MetaIrrelevantSolution"
      , "meta"            #= prettyTCM (I.MetaV meta [])
      , "term"            #= prettyTCM term
      ]

    BuiltinMustBeConstructor s expr -> obj
      [ "kind"            @= String "MetaIrrelevantSolution"
      , "expr"            #= prettyA expr
      , "message"         @= s
      ]

    NoSuchBuiltinName s -> obj
      [ "kind"            @= String "NoSuchBuiltinName"
      , "message"         @= s
      ]

    DuplicateBuiltinBinding s x y -> obj
      [ "kind"            @= String "DuplicateBuiltinBinding"
      , "term1"           #= prettyTCM x
      , "term2"           #= prettyTCM y
      , "message"         @= s
      ]

    NoBindingForBuiltin s -> obj
      [ "kind"            @= String "NoBindingForBuiltin"
      , "payload"         @= s
      , "builtins"        @= [builtinZero, builtinSuc, builtinNat]
      ]

    NoSuchPrimitiveFunction s -> obj
      [ "kind"            @= String "NoSuchPrimitiveFunction"
      , "message"         @= s
      ]

    BuiltinInParameterisedModule s -> obj
      [ "kind"            @= String "NoSuchPrimitiveFunction"
      , "message"         @= s
      ]

    IllegalLetInTelescope typedBinding -> obj
      [ "kind"            @= String "IllegalLetInTelescope"
      , "typedBinding"    @= pretty typedBinding
      ]

    NoRHSRequiresAbsurdPattern ps -> obj
      [ "kind"            @= String "NoRHSRequiresAbsurdPattern"
      , "patterns"        #= mapM prettyA ps
      ]

    AbsurdPatternRequiresNoRHS ps -> obj
      [ "kind"            @= String "AbsurdPatternRequiresNoRHS"
      , "patterns"        #= mapM prettyA ps
      ]

    LocalVsImportedModuleClash m -> obj
      [ "kind"            @= String "LocalVsImportedModuleClash"
      , "module"          #= prettyTCM m
      ]

    SolvedButOpenHoles -> obj
      [ "kind"            @= String "SolvedButOpenHoles"
      ]

    CyclicModuleDependency ms -> obj
      [ "kind"            @= String "CyclicModuleDependency"
      , "modules"         @= map pretty ms
      ]

    FileNotFound m files -> obj
      [ "kind"            @= String "FileNotFound"
      , "module"          @= pretty m
      , "filepaths"       @= map filePath files
      ]

    OverlappingProjects f m1 m2 -> obj
      [ "kind"            @= String "OverlappingProjects"
      , "module1"         @= pretty m1
      , "module2"         @= pretty m2
      , "filepath"        @= filePath f
      ]

    AmbiguousTopLevelModuleName m files -> obj
      [ "kind"            @= String "AmbiguousTopLevelModuleName"
      , "module"          @= pretty m
      , "filepaths"       @= map filePath files
      ]

    ClashingFileNamesFor m files -> obj
      [ "kind"            @= String "ClashingFileNamesFor"
      , "module"          @= pretty m
      , "filepaths"       @= map filePath files
      ]

    ModuleDefinedInOtherFile m file file' -> obj
      [ "kind"            @= String "ModuleDefinedInOtherFile"
      , "module"          @= pretty m
      , "filepath1"       @= filePath file
      , "filepath2"       @= filePath file'
      ]

    ModuleNameUnexpected given expected -> obj
      [ "kind"            @= String "ModuleNameUnexpected"
      , "expected"        @= pretty expected
      , "given"           @= pretty given
      ]

    ModuleNameDoesntMatchFileName given files -> obj
      [ "kind"            @= String "ModuleNameDoesntMatchFileName"
      , "filepaths"       @= map filePath files
      , "given"           @= pretty given
      ]

    BothWithAndRHS -> obj
      [ "kind"            @= String "BothWithAndRHS"
      ]

    AbstractConstructorNotInScope c -> obj
      [ "kind"            @= String "AbstractConstructorNotInScope"
      , "constructor"     #= prettyTCM c
      ]

    NotInScope xs -> do
      inscope <- Set.toList . S.concreteNamesInScope <$> getScope
      obj
        [ "kind"            @= String "NotInScope"
        , "payloads"        #= mapM (name inscope) xs
        ]
      where
        name inscope x = obj
          [ "name"        @= pretty x
          , "range"       #= prettyTCM (P.getRange x)
          , "suggestion"  @= suggestion inscope x
          ]
        suggestion inscope x = map prettyShow $ filter (close (strip x) . strip) inscope
          where
            strip x = map toLower $ filter (/= '_') $ prettyShow $ C.unqualify x
            maxDist n = div n 3
            close a b = editDistance a b <= maxDist (length a)

    NoSuchModule x -> obj
      [ "kind"          @= String "NoSuchModule"
      , "module"        @= pretty x
      ]

    AmbiguousName x ys -> obj
      [ "kind"          @= String "AmbiguousName"
      , "ambiguousName" @= pretty x
      , "couldReferTo"  #= mapM nameWithBinding (toList ys)
      ]

    AmbiguousModule x ys -> obj
      [ "kind"            @= String "AmbiguousModule"
      , "ambiguousModule" @= pretty x
      , "couldReferTo"    #= mapM help (toList ys)
      ]
      where
        help :: I.ModuleName -> TCM Value
        help m = obj
          [ "dataOrRecord"  #= S.isDatatypeModule m
          , "name"          #= prettyTCM m
          ]

    UninstantiatedModule x -> obj
      [ "kind"            @= String "UninstantiatedModule"
      , "module"          @= pretty x
      ]

    ClashingDefinition x y -> obj
      [ "kind"            @= String "ClashingDefinition"
      , "definition"      @= pretty x
      , "previouslyAt"    #= prettyTCM (I.nameBindingSite (I.qnameName y))
      ]

    ClashingModule m1 m2 -> obj
      [ "kind"            @= String "ClashingDefinition"
      , "module1"         #= prettyTCM m1
      , "module2"         #= prettyTCM m2
      ]

    ClashingImport x y -> obj
      [ "kind"            @= String "ClashingImport"
      , "name1"           @= pretty x
      , "name2"           #= prettyTCM y
      ]

    ClashingModuleImport x y -> obj
      [ "kind"            @= String "ClashingModuleImport"
      , "module1"         @= pretty x
      , "module2"         #= prettyTCM y
      ]

    PatternShadowsConstructor x c -> obj
      [ "kind"            @= String "PatternShadowsConstructor"
      , "patternVariable" #= prettyTCM x
      , "constructor"     #= prettyTCM c
      ]

    DuplicateImports m xs -> obj
      [ "kind"            @= String "DuplicateImports"
      , "module"          @= pretty m
      , "imports"         @= map pretty xs
      ]

    ModuleDoesntExport m xs -> obj
      [ "kind"            @= String "ModuleDoesntExport"
      , "module"          @= pretty m
      , "doesntExport"    @= map pretty xs
      ]

    NotAModuleExpr e -> obj
      [ "kind"            @= String "NotAModuleExpr"
      , "expr"            @= pretty e
      ]

    FieldOutsideRecord -> obj
      [ "kind"            @= String "FieldOutsideRecord"
      ]

    InvalidPattern p -> obj
      [ "kind"            @= String "InvalidPattern"
      , "pattern"         @= pretty p
      ]

    RepeatedVariablesInPattern xs -> obj
      [ "kind"            @= String "RepeatedVariablesInPattern"
      , "variables"       @= map pretty xs
      ]

    NotAnExpression e -> obj
      [ "kind"            @= String "NotAnExpression"
      , "expr"            @= pretty e
      ]

    NotAValidLetBinding nd -> obj
      [ "kind"            @= String "NotAnExpression"
      , "niceDeclaration" @= show nd
      ]

    NothingAppliedToHiddenArg e -> obj
      [ "kind"            @= String "NothingAppliedToHiddenArg"
      , "expr"            @= pretty e
      ]

    NothingAppliedToInstanceArg e -> obj
      [ "kind"            @= String "NothingAppliedToInstanceArg"
      , "expr"            @= pretty e
      ]

    NoParseForApplication es -> obj
      [ "kind"            @= String "NoParseForApplication"
      , "exprs"           @= pretty (C.RawApp P.noRange es)
      ]

    AmbiguousParseForApplication es es' -> obj
      [ "kind"            @= String "AmbiguousParseForApplication"
      , "cannotParse"     @= pretty (C.RawApp P.noRange es)
      , "couldMean"       #= mapM pretty' es'
      ]
      where
        pretty' e = do
          let p1 = pretty $ C.RawApp P.noRange es
          let p2 = pretty e
          if show p1 == show p2
            then prettyUnambiguousApplication e
            else return (pretty e)

    BadArgumentsToPatternSynonym x -> obj
      [ "kind"            @= String "BadArgumentsToPatternSynonym"
      , "patternSynonym"  #= prettyTCM (I.headAmbQ x)
      ]

    TooFewArgumentsToPatternSynonym x -> obj
      [ "kind"            @= String "TooFewArgumentsToPatternSynonym"
      , "patternSynonym"  #= prettyTCM (I.headAmbQ x)
      ]

    CannotResolveAmbiguousPatternSynonym defs -> obj
      [ "kind"            @= String "CannotResolveAmbiguousPatternSynonym"
      , "patternSynonym"  #= prettyTCM x
      , "shapes"          #= mapM prDef (toList defs)
      ]
      where
        (x, _) = headNe defs
        prDef (x, (xs, p)) = obj
          [ "patSyn"      #= prettyA (A.PatternSynDef x xs p)
          , "bindingSite" @= pretty (I.nameBindingSite (I.qnameName x))
          ]

    UnusedVariableInPatternSynonym -> obj
      [ "kind"            @= String "UnusedVariableInPatternSynonym"
      ]

    NoParseForLHS IsLHS p -> obj
      [ "kind"            @= String "NoParseForLHS"
      , "isLHS"           @= True
      , "LHS"             @= pretty p
      ]

    NoParseForLHS IsPatSyn p -> obj
      [ "kind"            @= String "NoParseForLHS"
      , "isLHS"           @= False
      , "patSyn"          @= pretty p
      ]

    AmbiguousParseForLHS lhsOrPatSyn p ps -> obj
      [ "kind"            @= String "AmbiguousParseForLHS"
      , "LHSOrPatSyn"     @= show lhsOrPatSyn
      , "cannotParse"     @= pretty p
      , "couldMean"       @= map pretty' ps
      ]
      where
        pretty' p' = pretty $ if show (pretty p) == show (pretty p')
            then unambiguousPattern p'
            else p'

    OperatorInformation sects err -> obj
      [ "kind"              @= String "OperatorInformation"
      , "notationSections"  @= sects
      , "typeError"         #= encodeTCM err
      ]
--
    SplitError e -> obj
      [ "kind"            @= String "SplitError"
      , "error"           #= prettyTCM e
      ]

    ImpossibleConstructor c neg -> obj
      [ "kind"            @= String "ImpossibleConstructor"
      , "constructor"     #= prettyTCM c
      , "negUni"          #= prettyTCM neg
      ]

    TooManyPolarities x n -> obj
      [ "kind"            @= String "TooManyPolarities"
      , "name"            #= prettyTCM x
      , "atMostAllowed"   @= n
      ]

    IFSNoCandidateInScope t -> obj
      [ "kind"            @= String "IFSNoCandidateInScope"
      , "type"            #= prettyTCM t
      ]

    UnquoteFailed err -> obj
      [ "kind"            @= String "UnquoteFailed"
      , "unquoteError"    #= encodeTCM err
      ]

    DeBruijnIndexOutOfScope i I.EmptyTel [] -> obj
      [ "kind"            @= String "DeBruijnIndexOutOfScope"
      , "empty"           @= True
      , "index"           @= i
      ]
    DeBruijnIndexOutOfScope i cxt names -> obj
      [ "kind"            @= String "DeBruijnIndexOutOfScope"
      , "empty"           @= False
      , "index"           @= i
      , "context"         #= inTopContext (addContext ("_" :: String) $ prettyTCM cxt')
      ]
      where
        cxt' = cxt `abstract` raise (size cxt) (nameCxt names)
        nameCxt [] = I.EmptyTel
        nameCxt (x : xs) = I.ExtendTel (C.defaultDom (I.El __DUMMY_SORT__ $ I.var 0)) $
          I.NoAbs (prettyShow x) $ nameCxt xs

    NeedOptionCopatterns -> obj
      [ "kind"            @= String "NeedOptionCopatterns"
      ]

    NeedOptionRewriting -> obj
      [ "kind"            @= String "NeedOptionRewriting"
      ]

    GeneralizeNotSupportedHere x -> obj
      [ "kind"            @= String "GeneralizeNotSupportedHere"
      , "variable"        @= show x
      ]

    GeneralizeCyclicDependency -> obj
      [ "kind"            @= String "GeneralizeCyclicDependency"
      ]

    GeneralizeUnsolvedMeta -> obj
      [ "kind"            @= String "GeneralizeUnsolvedMeta"
      ]

    NonFatalErrors ws -> obj
      [ "kind"            @= String "NonFatalErrors"
      , "warnings"        #= mapM prettyTCM ws
      ]

    InstanceSearchDepthExhausted term typ depth -> obj
      [ "kind"            @= String "InstanceSearchDepthExhausted"
      , "maxDepth"        @= depth
      , "term"            #= prettyTCM term
      , "type"            #= prettyTCM typ
      ]

    -- For unhandled errors, passing only its kind
    _ -> obj [ "kind" @= toJSON (errorString err) ]


--------------------------------------------------------------------------------

instance EncodeTCM UnquoteError where
  encodeTCM err = case err of
    BadVisibility msg arg -> obj
      [ "kind"        @= String "BadVisibility"
      , "message"     @= msg
      ]

    ConInsteadOfDef x def con -> obj
      [ "kind"        @= String "ConInsteadOfDef"
      , "constructor" #= prettyTCM x
      , "use"         @= con
      , "insteadIf"   @= def
      ]

    DefInsteadOfCon x def con -> obj
      [ "kind"        @= String "DefInsteadOfCon"
      , "non-constructor" #= prettyTCM x
      , "use"         @= def
      , "insteadIf"   @= con
      ]

    NonCanonical category term -> obj
      [ "kind"        @= String "NonCanonical"
      , "category"    @= category
      , "term"        #= prettyTCM term
      ]

    BlockedOnMeta _ m ->  obj
      [ "kind"        @= String "BlockedOnMeta"
      , "meta"        #= prettyTCM m
      ]

    UnquotePanic err -> __IMPOSSIBLE__
