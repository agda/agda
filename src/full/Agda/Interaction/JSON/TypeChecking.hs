{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking

module Agda.Interaction.JSON.TypeChecking where

import Control.Monad.State
import Data.Aeson
import Data.Function (on)
import Data.List (nub, sortBy)
import Data.Maybe (isJust)
import Data.Char (toLower)
import qualified Data.Set as Set

import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.Syntax.Internal
import Agda.Interaction.JSON.Syntax.Abstract
import Agda.Interaction.JSON.Syntax.Concrete
import Agda.Interaction.JSON.Syntax.Parser
import Agda.Interaction.JSON.Syntax.Translation
import Agda.Interaction.JSON.TypeChecking.Positivity
import qualified Agda.Syntax.Abstract             as A
import qualified Agda.Syntax.Common               as C
import qualified Agda.Syntax.Concrete             as C
import qualified Agda.Syntax.Concrete.Definitions as D
import qualified Agda.Syntax.Fixity               as F
import qualified Agda.Syntax.Info                 as I
import qualified Agda.Syntax.Internal             as I
import Agda.Syntax.Internal (dummySort)
import qualified Agda.Syntax.Position             as P
import qualified Agda.Syntax.Scope.Monad          as S
import qualified Agda.Syntax.Scope.Base           as S
import qualified Agda.Syntax.Translation.AbstractToConcrete as A2C
import qualified Agda.Syntax.Translation.InternalToAbstract as I2A
import Agda.Syntax.Position (Range, Range'(..))

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Closure (enterClosure)
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
import Agda.Utils.Monad (localState)
import Agda.Utils.Null

#include "undefined.h"
import Agda.Utils.Impossible

--------------------------------------------------------------------------------

instance EncodeTCM TCWarning where
  encodeTCM (TCWarning range warning warning' cached) =
    obj
      [ "range"     @= range
      , "warning"   @= warning
      , "warning'"  @= warning'
      , "cached"    @= cached
      ]

--------------------------------------------------------------------------------

instance EncodeTCM Warning where
  encodeTCM warning = case warning of
    NicifierIssue w -> kind "NicifierIssue"
      [ "declarationWarning"  @= w
      ]

    TerminationIssue es -> kind "TerminationIssue"
      [ "terminationErrors"   @= es
      ]

    UnreachableClauses name clauses -> kind "UnreachableClauses"
      [ "name"                @= name
      -- , "clauses"             @= clauses
      ]

    CoverageIssue name pairs -> kind "CoverageIssue"
      [ "name"                @= name
      , "declarations"        @= map f pairs
      ]
      where f (tel, ps) = I2A.NamedClause name True $
                    empty { I.clauseTel = tel, I.namedClausePats = ps }

    CoverageNoExactSplit name clauses -> kind "CoverageNoExactSplit"
      [ "name"                @= name
      , "declarations"        @= map f clauses
      ]
      where f clause = I2A.NamedClause name True clause

    NotStrictlyPositive name occursWhere -> kind "NotStrictlyPositive"
      [ "name"                @= name
      , "occursWhere"         @= occursWhere
      ]

    UnsolvedMetaVariables ranges -> kind "UnsolvedMetaVariables"
      [ "ranges"              @= ranges
      ]

    UnsolvedInteractionMetas ranges -> kind "UnsolvedInteractionMetas"
      [ "ranges"              @= ranges
      ]

    UnsolvedConstraints constraints -> kind "UnsolvedConstraints"
      [ "constraints"         @= constraints
      ]

    AbsurdPatternRequiresNoRHS clauses -> kind "AbsurdPatternRequiresNoRHS" []

    OldBuiltin old new -> kind "OldBuiltin"
      [ "old"                 @= old
      , "new"                 @= new
      ]

    EmptyRewritePragma -> kind "EmptyRewritePragma" []

    UselessPublic -> kind "UselessPublic" []

    UselessInline name -> kind "UselessInline"
      [ "name"                @= name
      ]

    InversionDepthReached name -> kind "InversionDepthReached"
      [ "name"                @= name
      ]

    GenericWarning warning -> kind "GenericWarning"
      [ "warning"             @= warning
      ]

    GenericNonFatalError message -> kind "GenericNonFatalError"
      [ "message"             @= message
      ]

    SafeFlagPostulate name -> kind "SafeFlagPostulate"
      [ "name"                @= name
      ]

    SafeFlagPragma pragmas -> kind "SafeFlagPragma"
      [ "pragmas"             @= pragmas
      ]

    SafeFlagNonTerminating -> kind "SafeFlagNonTerminating" []

    SafeFlagTerminating -> kind "SafeFlagTerminating" []

    SafeFlagPrimTrustMe -> kind "SafeFlagPrimTrustMe" []

    SafeFlagNoPositivityCheck -> kind "SafeFlagNoPositivityCheck" []

    SafeFlagPolarity -> kind "SafeFlagPolarity" []

    SafeFlagNoUniverseCheck -> kind "SafeFlagNoUniverseCheck" []

    ParseWarning warning -> kind "ParseWarning"
      [ "warning"             @= warning
      ]

    DeprecationWarning old new version -> kind "DeprecationWarning"
      [ "old"                 @= old
      , "new"                 @= new
      , "version"             @= version
      ]

    UserWarning warning -> kind "UserWarning"
      [ "warning"             @= warning
      ]

    ModuleDoesntExport source names -> kind "UserWarning"
      [ "sourceModule"        @= source
      , "names"               @= names
      ]

--------------------------------------------------------------------------------

instance EncodeTCM TCErr where
  encodeTCM (TypeError state closure) = localTCState $ do
    putTC state
    kind "TypeError"
      [ "range"     @= envRange (clEnv closure)
      , "call"      @= (envCall (clEnv closure))
      , "typeError" @= closure
      ]
  encodeTCM (Exception range doc) = kind "Exception"
    [ "range"       @= range
    , "message"     @= doc
    ]
  encodeTCM (IOException _ range exception) = kind "IOException"
    [ "range"       @= range
    , "message"     @= show exception
    ]
  encodeTCM PatternErr = kind "PatternErr"
    [ "range"       @= (NoRange :: Range)
    ]

--------------------------------------------------------------------------------

instance EncodeTCM TypeError where
  encodeTCM err = case err of
    InternalError s -> kind "InternalError"
      [ "message" @= s
      ]

    NotImplemented s -> kind "NotImplemented"
      [ "message" @= s
      ]

    NotSupported s -> kind "NotSupported"
      [ "message" @= s
      ]

    CompilationError s -> kind "CompilationError"
      [ "message" @= s
      ]

    GenericError s -> kind "GenericError"
      [ "message" @= s
      ]

    GenericDocError d -> kind "GenericDocError"
      [ "message" @= d
      ]

    -- TerminationCheckFailed because -> do
    --   -- topLevelModuleDropper produces a function which drops the filename
    --   -- component of the qualified name.
    --   dropTopLevel <- topLevelModuleDropper
    --   let functionNames = map
    --         (pretty . dropTopLevel)
    --         (concatMap termErrFunctions because)
    --   problematicCalls <- fmap nub
    --         $ mapM prettyTCM
    --         $ sortBy (compare `on` callInfoRange)
    --         $ (concatMap termErrCalls because)
    --   obj
    --     [ "kind"              @= String "TerminationCheckFailed"
    --     , "functions"         @= functionNames
    --     , "problematicCalls"  @= problematicCalls
    --     ]

    PropMustBeSingleton -> kind "PropMustBeSingleton" []

    DataMustEndInSort term -> kind "DataMustEndInSort"
      [ "term"  @= term
      ]

    ShouldEndInApplicationOfTheDatatype t -> kind "ShouldEndInApplicationOfTheDatatype"
      [ "type"  @= t
      ]

    ShouldBeAppliedToTheDatatypeParameters s t -> kind "ShouldEndInApplicationOfTheDatatype"
      [ "expected"  @= s
      , "given"     @= t
      ]

    ShouldBeApplicationOf t q -> kind "ShouldBeApplicationOf"
      [ "type" @= t
      , "name" @= q
      ]

    ShouldBeRecordType t -> kind "ShouldBeRecordType"
      [ "type"  @= t
      ]

    ShouldBeRecordPattern p -> kind "ShouldBeRecordPattern" []

    NotAProjectionPattern p -> kind "NotAProjectionPattern"
      [ "pattern" @= p
      ]

    -- DifferentArities -> obj
    --   [ "kind" @= String "DifferentArities" ]

    WrongHidingInLHS -> kind "WrongHidingInLHS" []

    WrongHidingInLambda t -> kind "WrongHidingInLambda"
      [ "type" @= t
      ]

    WrongIrrelevanceInLambda -> kind "WrongIrrelevanceInLambda" []

    WrongNamedArgument a -> kind "WrongNamedArgument"
      [ "args" @= a
      ]

    WrongHidingInApplication t -> kind "WrongHidingInApplication"
      [ "type" @= t
      ]

    WrongInstanceDeclaration -> kind "WrongInstanceDeclaration" []

    HidingMismatch h h' -> kind "HidingMismatch"
      [ "expected"  @= verbalize (Indefinite h')
      , "given"     @= verbalize (Indefinite h)
      ]

    RelevanceMismatch r r' -> kind "RelevanceMismatch"
      [ "expected"  @= verbalize (Indefinite r')
      , "given"     @= verbalize (Indefinite r)
      ]

    UninstantiatedDotPattern e -> kind "UninstantiatedDotPattern"
        [ "expr" @= e
        ]

    ForcedConstructorNotInstantiated p -> kind "ForcedConstructorNotInstantiated"
        [ "pattern" @= p
        ]

    IlltypedPattern p a -> ifPiType a yes no
      where
        yes dom abs = kind "IlltypedPattern"
          [ "isPiType"  @= True
          , "pattern"   @= p
          , "dom"       @= dom
          , "abs"       @= show abs
          ]
        no t = kind "IlltypedPattern"
          [ "isPiType"  @= False
          , "pattern"   @= p
          , "type"      @= t
          ]

    IllformedProjectionPattern p -> kind "IllformedProjectionPattern"
        [ "pattern" @= p
        ]

    CannotEliminateWithPattern p a -> do
      if isJust (A.isProjP p) then
        kind "CannotEliminateWithPattern"
          [ "isProjection"  @= True
          , "pattern"       @= p
          ]
      else
        kind "CannotEliminateWithPattern"
          [ "isProjection"  @= False
          , "pattern"       @= p
          , "patternKind"   @= kindOfPattern (C.namedArg p)
          ]

    WrongNumberOfConstructorArguments name expected given -> kind "WrongNumberOfConstructorArguments"
      [ "name"      @= name
      , "expected"  @= expected
      , "given"     @= given
      ]

    CantResolveOverloadedConstructorsTargetingSameDatatype datatype ctrs -> do
      kind "CantResolveOverloadedConstructorsTargetingSameDatatype"
        [ "datatype"      @= datatype
        , "constructors"  @= ctrs
        ]

    DoesNotConstructAnElementOf c t -> kind "DoesNotConstructAnElementOf"
      [ "constructor" @= c
      , "type"        @= t
      ]

    ConstructorPatternInWrongDatatype c d -> kind "ConstructorPatternInWrongDatatype"
      [ "constructor" @= c
      , "datatype"    @= d
      ]

    ShadowedModule x [] -> __IMPOSSIBLE__
    ShadowedModule x ms -> do
      (range, m) <- handleShadowedModule x ms
      kind "ShadowedModule"
        [ "duplicated"    @= x
        , "previous"      @= m
        , "dataOrRecord"  #= S.isDatatypeModule m
        ]

    ModuleArityMismatch m I.EmptyTel args -> kind "ModuleArityMismatch"
      [ "module"          @= m
      , "isParameterized" @= False
      ]
    ModuleArityMismatch m tel@(I.ExtendTel _ _) args -> kind "ModuleArityMismatch"
      [ "module"          @= m
      , "isParameterized" @= True
      , "telescope"       @= tel
      ]

    ShouldBeEmpty t ps -> kind "ShouldBeEmpty"
      [ "type"            @= t
      , "patterns"        #= mapM (prettyPattern 0) ps
      ]

    ShouldBeASort t -> kind "ShouldBeASort"
      [ "type"            @= t
      ]

    ShouldBePi t -> kind "ShouldBePi"
      [ "type"            @= t
      ]

    ShouldBePath t -> kind "ShouldBePath"
      [ "type"            @= t
      ]

    NotAProperTerm -> kind "NotAProperTerm" []

    InvalidTypeSort s -> kind "InvalidTypeSort"
      [ "sort"            @= s
      ]

    InvalidType t -> kind "InvalidType"
      [ "type"            @= t
      ]

    FunctionTypeInSizeUniv t -> kind "FunctionTypeInSizeUniv"
      [ "term"            @= t
      ]

    SplitOnIrrelevant t ->kind "SplitOnIrrelevant"
      [ "term"            @= verbalize (C.getRelevance t)
      , "type"            @= (C.unDom t)
      ]

    SplitOnNonVariable term typ ->kind "SplitOnNonVariable"
      [ "term"            @= term
      , "type"            @= typ
      ]


    DefinitionIsIrrelevant x -> kind "DefinitionIsIrrelevant"
      [ "name"            @= x
      ]

    VariableIsIrrelevant x -> kind "VariableIsIrrelevant"
      [ "name"            @= x
      ]

    UnequalBecauseOfUniverseConflict cmp s t -> kind "UnequalBecauseOfUniverseConflict"
      [ "comparison"      @= cmp
      , "term1"           @= s
      , "term2"           @= t
      ]


    UnequalTerms cmp s t a -> case refineUnequalTerms cmp s t of
      Just err -> encodeTCM err
      Nothing -> do
        (_, _, d) <- prettyInEqual s t
        kind "UnequalTerms"
          [ "comparison"      @= cmp
          , "term1"           @= s
          , "term2"           @= t
          , "type"            @= a
          , "reason"          @= d
          ]

    UnequalTypes cmp a b -> kind "UnequalTypes"
      [ "comparison"      @= cmp
      , "type1"           @= a
      , "type2"           @= b
      , "message"         #= prettyUnequal a (notCmp cmp) b
      ]

    UnequalRelevance cmp a b -> kind "UnequalRelevance"
      [ "comparison"      @= cmp
      , "term1"           @= a
      , "term2"           @= b
      ]

    UnequalHiding a b -> kind "UnequalHiding"
      [ "term1"           @= a
      , "term2"           @= b
      ]

    UnequalSorts a b -> kind "UnequalSorts"
      [ "sort1"           @= a
      , "sort2"           @= b
      ]

    NotLeqSort a b -> kind "NotLeqSort"
      [ "sort1"           @= a
      , "sort2"           @= b
      ]

    TooFewFields record fields -> kind "TooFewFields"
      [ "record"          @= record
      , "fields"          @= fields
      ]

    TooManyFields record fields -> kind "TooManyFields"
      [ "record"          @= record
      , "fields"          @= fields
      ]

    DuplicateConstructors xs -> kind "DuplicateConstructors"
      [ "constructors"    @=  xs
      ]

    DuplicateFields xs -> kind "DuplicateFields"
      [ "fields"          @= xs
      ]

    WithOnFreeVariable expr term -> do
      de <- prettyA expr
      dt <- prettyTCM term
      if show de == show dt
        then kind "WithOnFreeVariable"
          [ "variable"        @= term
          ]
        else kind "WithOnFreeVariable"
          [ "variable"        @= term
          , "expression"      @= expr
          ]

    UnexpectedWithPatterns xs -> kind "UnexpectedWithPatterns"
      [ "patterns"        @= xs
      ]

    -- The arguments are the meta variable, the parameters it can
    -- depend on and the paratemeter that it wants to depend on.
    MetaCannotDependOn meta ps i -> kind "MetaCannotDependOn"
      [ "meta"            @= (I.MetaV meta [])
      , "wantsToDependOn" @= (I.var i)
      , "canDepdendOn"    @= (map I.var ps)
      ]

    MetaOccursInItself meta -> kind "MetaOccursInItself"
      [ "meta"            @= (I.MetaV meta [])
      ]

    MetaIrrelevantSolution meta term -> kind "MetaIrrelevantSolution"
      [ "meta"            @= (I.MetaV meta [])
      , "term"            @= term
      ]

    BuiltinMustBeConstructor s expr -> kind "MetaIrrelevantSolution"
      [ "expr"            @= expr
      , "message"         @= s
      ]

    NoSuchBuiltinName s -> kind "NoSuchBuiltinName"
      [ "message"         @= s
      ]

    DuplicateBuiltinBinding s x y -> kind "DuplicateBuiltinBinding"
      [ "term1"           @= x
      , "term2"           @= y
      , "message"         @= s
      ]

    NoBindingForBuiltin s -> kind "NoBindingForBuiltin"
      [ "payload"         @= s
      , "builtins"        @= [builtinZero, builtinSuc, builtinNat]
      ]

    NoSuchPrimitiveFunction s -> kind "NoSuchPrimitiveFunction"
      [ "message"         @= s
      ]

    BuiltinInParameterisedModule s -> kind "NoSuchPrimitiveFunction"
      [ "message"         @= s
      ]

    IllegalLetInTelescope typedBinding -> kind "IllegalLetInTelescope"
      [ "typedBinding"    @= typedBinding
      ]

    NoRHSRequiresAbsurdPattern ps -> kind "NoRHSRequiresAbsurdPattern"
      [ "patterns"        @= ps
      ]

    -- AbsurdPatternRequiresNoRHS ps -> obj
    --   [ "kind"            @= String "AbsurdPatternRequiresNoRHS"
    --   , "patterns"        #= mapM prettyA ps
    --   ]

    LocalVsImportedModuleClash m -> kind "LocalVsImportedModuleClash"
      [ "module"          @= m
      ]

    SolvedButOpenHoles -> kind "SolvedButOpenHoles" []

    CyclicModuleDependency ms -> kind "CyclicModuleDependency"
      [ "modules"         @= ms
      ]

    FileNotFound m files -> kind "FileNotFound"
      [ "module"          @= m
      , "filepaths"       @= map filePath files
      ]

    OverlappingProjects f m1 m2 -> kind "OverlappingProjects"
      [ "module1"         @= m1
      , "module2"         @= m2
      , "filepath"        @= filePath f
      ]

    AmbiguousTopLevelModuleName m files -> kind "AmbiguousTopLevelModuleName"
      [ "module"          @= m
      , "filepaths"       @= map filePath files
      ]

    ClashingFileNamesFor m files -> kind "ClashingFileNamesFor"
      [ "module"          @= m
      , "filepaths"       @= map filePath files
      ]

    ModuleDefinedInOtherFile m file file' -> kind "ModuleDefinedInOtherFile"
      [ "module"          @= m
      , "filepath1"       @= filePath file
      , "filepath2"       @= filePath file'
      ]

    ModuleNameUnexpected given expected -> kind "ModuleNameUnexpected"
      [ "expected"        @= pretty expected
      , "given"           @= pretty given
      ]

    ModuleNameDoesntMatchFileName given files -> kind "ModuleNameDoesntMatchFileName"
      [ "filepaths"       @= map filePath files
      , "given"           @= pretty given
      ]

    BothWithAndRHS -> kind "BothWithAndRHS" []

    AbstractConstructorNotInScope c -> kind "AbstractConstructorNotInScope"
      [ "constructor"     @= c
      ]

    NotInScope xs -> do
      inscope <- Set.toList . S.concreteNamesInScope <$> getScope
      kind "NotInScope"
        [ "names"           #= mapM (name inscope) xs
        ]
      where
        name inscope x = obj
          [ "name"        @= x
          , "suggestions" @= suggestion inscope x
          ]
        suggestion inscope x = filter (close (strip x) . strip) inscope
          where
            strip x = map toLower $ filter (/= '_') $ prettyShow $ C.unqualify x
            maxDist n = div n 3
            close a b = editDistance a b <= maxDist (length a)

    NoSuchModule x -> kind "NoSuchModule"
      [ "module"        @= x
      ]

    AmbiguousName x ys -> kind "AmbiguousName"
      [ "ambiguousName" @= x
      , "couldReferTo"  @= (toList ys)
      ]

    AmbiguousModule x ys -> kind "AmbiguousModule"
      [ "ambiguousModule" @= x
      , "couldReferTo"    #= mapM help (toList ys)
      ]
      where
        help :: I.ModuleName -> TCM Value
        help m = obj
          [ "dataOrRecord"  #= S.isDatatypeModule m
          , "name"          @= m
          ]

    -- UninstantiatedModule x -> obj
    --   [ "kind"            @= String "UninstantiatedModule"
    --   , "module"          @= pretty x
    --   ]

    ClashingDefinition x y -> kind "ClashingDefinition"
      [ "definition"      @= x
      , "previouslyAt"    @= I.nameBindingSite (I.qnameName y)
      ]

    ClashingModule m1 m2 -> kind "ClashingModule"
      [ "module1"         @= m1
      , "module2"         @= m2
      ]

    ClashingImport x y -> kind "ClashingImport"
      [ "name1"           @= x
      , "name2"           @= y
      ]

    ClashingModuleImport x y -> kind "ClashingModuleImport"
      [ "module1"         @= x
      , "module2"         @= y
      ]

    PatternShadowsConstructor x c -> kind "PatternShadowsConstructor"
      [ "patternVariable" @= x
      , "constructor"     @= c
      ]

    DuplicateImports m xs -> kind "DuplicateImports"
      [ "module"          @= m
      , "imports"         @= xs
      ]

    -- ModuleDoesntExport m xs -> obj
    --   [ "kind"            @= String "ModuleDoesntExport"
    --   , "module"          @= pretty m
    --   , "doesntExport"    @= map pretty xs
    --   ]

    NotAModuleExpr e -> kind "NotAModuleExpr"
      [ "expr"            @= e
      ]

    FieldOutsideRecord -> kind "FieldOutsideRecord" []

    InvalidPattern p -> kind "InvalidPattern"
      [ "pattern"         @= p
      ]

    RepeatedVariablesInPattern xs -> kind "RepeatedVariablesInPattern"
      [ "variables"       @= xs
      ]

    NotAnExpression e -> kind "NotAnExpression"
      [ "expr"            @= e
      ]

    NotAValidLetBinding nd -> kind "NotAnExpression" []

    NothingAppliedToHiddenArg e -> kind "NothingAppliedToHiddenArg"
      [ "expr"            @= e
      ]

    NothingAppliedToInstanceArg e -> kind "NothingAppliedToInstanceArg"
      [ "expr"            @= e
      ]

    NoParseForApplication es -> kind "NoParseForApplication"
      [ "exprs"           @= (C.RawApp P.noRange es)
      ]

    AmbiguousParseForApplication es es' -> kind "AmbiguousParseForApplication"
      [ "cannotParse"     @= (C.RawApp P.noRange es)
      , "couldMean"       #= mapM pretty' es'
      ]
      where
        pretty' e = do
          let p1 = pretty $ C.RawApp P.noRange es
          let p2 = pretty e
          if show p1 == show p2
            then prettyUnambiguousApplication e
            else return (pretty e)

    BadArgumentsToPatternSynonym x -> kind "BadArgumentsToPatternSynonym"
      [ "patternSynonym"  @= (I.headAmbQ x)
      ]

    TooFewArgumentsToPatternSynonym x -> kind "TooFewArgumentsToPatternSynonym"
      [ "patternSynonym"  @= (I.headAmbQ x)
      ]

    CannotResolveAmbiguousPatternSynonym defs -> kind "CannotResolveAmbiguousPatternSynonym"
      [ "patternSynonym"  @= x
      , "shapes"          #= mapM prDef (toList defs)
      ]
      where
        (x, _) = headNe defs
        prDef (x, (xs, p)) = obj
          [ "patSyn"      @= (A.PatternSynDef x xs p)
          , "bindingSite" @= I.nameBindingSite (I.qnameName x)
          ]

    UnusedVariableInPatternSynonym -> kind "UnusedVariableInPatternSynonym" []

    NoParseForLHS IsLHS p -> kind "NoParseForLHS"
      [ "isLHS"           @= True
      , "LHS"             @= p
      ]

    NoParseForLHS IsPatSyn p -> kind "NoParseForLHS"
      [ "isLHS"           @= False
      , "patSyn"          @= p
      ]

    AmbiguousParseForLHS lhsOrPatSyn p ps -> kind "AmbiguousParseForLHS"
      [ "LHSOrPatSyn"     @= lhsOrPatSyn
      , "cannotParse"     @= p
      , "couldMean"       @= map pretty' ps
      ]
      where
        pretty' p' = pretty $ if show (pretty p) == show (pretty p')
            then unambiguousPattern p'
            else p'

    OperatorInformation sects err -> kind "OperatorInformation"
      [ "notationSections"  @= sects
      , "typeError"         @= err
      ]
--
    SplitError e -> kind "SplitError"
      [ "error"           @= e
      ]

    ImpossibleConstructor c neg -> kind "ImpossibleConstructor"
      [ "constructor"     @= c
      , "negUni"          @= neg
      ]

    TooManyPolarities x n -> kind "TooManyPolarities"
      [ "name"            @= x
      , "atMostAllowed"   @= n
      ]

    IFSNoCandidateInScope t -> kind "IFSNoCandidateInScope"
      [ "type"            @= t
      ]

    UnquoteFailed err -> kind "UnquoteFailed"
      [ "unquoteError"    @= err
      ]

    DeBruijnIndexOutOfScope i I.EmptyTel [] -> kind "DeBruijnIndexOutOfScope"
      [ "empty"           @= True
      , "index"           @= i
      ]
    DeBruijnIndexOutOfScope i cxt names -> kind "DeBruijnIndexOutOfScope"
      [ "empty"           @= False
      , "index"           @= i
      , "context"         #= inTopContext (addContext ("_" :: String) $ prettyTCM cxt')
      ]
      where
        cxt' = cxt `abstract` raise (size cxt) (nameCxt names)
        nameCxt [] = I.EmptyTel
        nameCxt (x : xs) = I.ExtendTel (C.defaultDom (I.El __DUMMY_SORT__ $ I.var 0)) $
          I.NoAbs (prettyShow x) $ nameCxt xs

    NeedOptionCopatterns -> kind "NeedOptionCopatterns" []

    NeedOptionRewriting -> kind "NeedOptionRewriting" []

    GeneralizeNotSupportedHere x -> kind "GeneralizeNotSupportedHere"
      [ "variable"        @= x
      ]

    GeneralizeCyclicDependency -> kind "GeneralizeCyclicDependency" []

    GeneralizeUnsolvedMeta -> kind "GeneralizeUnsolvedMeta" []

    NonFatalErrors ws -> kind "NonFatalErrors"
      -- we keep the TCWarnings prettified here because we don't have the right
      -- environment for encoding them (yet)
      [ "warnings"        @= ws
      ]

    InstanceSearchDepthExhausted term typ depth -> kind "InstanceSearchDepthExhausted"
      [ "maxDepth"        @= depth
      , "term"            @= term
      , "type"            @= typ
      ]

    -- For unhandled errors, passing only its kind
    _ -> obj [ "kind" @= toJSON (errorString err) ]


--------------------------------------------------------------------------------

instance EncodeTCM UnquoteError where
  encodeTCM err = case err of
    BadVisibility msg arg -> kind "BadVisibility"
      [ "message"     @= msg
      ]

    ConInsteadOfDef x def con -> kind "ConInsteadOfDef"
      [ "constructor" @= x
      , "use"         @= con
      , "insteadIf"   @= def
      ]

    DefInsteadOfCon x def con -> kind "DefInsteadOfCon"
      [ "non-constructor" @= x
      , "use"         @= def
      , "insteadIf"   @= con
      ]

    NonCanonical category term -> kind "NonCanonical"
      [ "category"    @= category
      , "term"        @= term
      ]

    BlockedOnMeta _ m ->  kind "BlockedOnMeta"
      [ "meta"        @= m
      ]

    UnquotePanic err -> __IMPOSSIBLE__

--------------------------------------------------------------------------------
-- Agda.TypeChecking.Monad.Base

instance EncodeTCM Comparison where
instance ToJSON Comparison where
  toJSON CmpEq  = String "CmpEq"
  toJSON CmpLeq = String "CmpLeq"

instance EncodeTCM Call where
  encodeTCM call = S.withContextPrecedence F.TopCtx $ case call of
    CheckClause t clause -> kind "CheckClause"
      [ "type"        @= t
      , "clause"      @= clause
      ]
    CheckPattern pattern tel t -> addContext tel $ kind "CheckPattern"
      [ "pattern"     @= pattern
      , "type"        @= t
      ]
    CheckLetBinding binding -> kind "CheckLetBinding"
      [ "binding"     @= binding
      ]
    InferExpr expr -> kind "InferExpr"
      [ "expr"        @= expr
      ]
    CheckExprCall cmp expr t -> kind "CheckExprCall"
      [ "comparison"  @= cmp
      , "expr"        @= expr
      , "type"        @= t
      ]
    CheckDotPattern expr t -> kind "CheckDotPattern"
      [ "expr"        @= expr
      , "type"        @= t
      ]
    CheckPatternShadowing clause -> kind "CheckPatternShadowing"
      [ "clause"      @= clause
      ]
    CheckProjection range name t -> kind "CheckProjection"
      [ "range"       @= range
      , "name"        @= name
      , "type"        @= t
      ]
    IsTypeCall expr sort -> kind "IsTypeCall"
      [ "expr"        @= expr
      , "sort"        @= sort
      ]
    IsType_ expr -> kind "IsType_"
      [ "expr"        @= expr
      ]
    InferVar name -> kind "InferVar"
      [ "name"        @= name
      ]
    InferDef name -> kind "InferDef"
      [ "name"        @= name
      ]
    CheckArguments range args t1 _ -> kind "CheckArguments"
      [ "range"       @= range
      , "arguments"   #= mapM (\ a -> S.withContextPrecedence (F.ArgumentCtx F.PreferParen) (A2C.abstractToConcreteHiding a a)) args
      , "type1"       @= t1
      ]
    CheckTargetType range infTy expTy -> kind "CheckTargetType"
      [ "range"       @= range
      , "infType"     @= infTy
      , "expType"     @= expTy
      ]
    CheckDataDef range name bindings constructors -> kind "CheckDataDef"
      [ "range"         @= range
      , "name"          @= name
      -- , "bindings"      @= show bindings
      -- , "constructors"  @= show constructors
      ]
    CheckRecDef range name bindings constructors -> kind "CheckDataDef"
      [ "name"          @= name
      , "range"         @= range
      -- , "bindings"      @= show bindings
      -- , "constructors"  @= show constructors
      ]
    CheckConstructor d _ _ (A.Axiom _ _ _ _ c _) -> kind "CheckConstructor"
      [ "declarationName" @= d
      , "constructorName" @= c
      ]

    CheckConstructor {} -> __IMPOSSIBLE__

    CheckFunDefCall range name _ -> kind "CheckFunDefCall"
      [ "range"         @= range
      , "name"          @= name
      -- , "clauses"       @= show clauses
      ]
    CheckPragma range pragma -> kind "CheckPragma"
      [ "range"         @= range
      , "pragma"        @= (A2C.RangeAndPragma P.noRange pragma)
      ]
    CheckPrimitive range name expr -> kind "CheckPrimitive"
      [ "range"         @= range
      , "name"          @= name
      , "expr"          @= expr
      ]
    CheckIsEmpty range t -> kind "CheckIsEmpty"
      [ "range"         @= range
      , "type"          @= t
      ]
    CheckWithFunctionType expr -> kind "CheckWithFunctionType"
      [ "expr"          @= expr
      ]
    CheckSectionApplication range m modApp -> kind "CheckSectionApplication"
      [ "range"         @= range
      , "module"        @= m
      , "modApp"        @= (A.Apply info m modApp A.initCopyInfo C.defaultImportDir)
      ]
      where
        info = I.ModuleInfo P.noRange P.noRange Nothing Nothing Nothing
    CheckNamedWhere m -> kind "CheckNamedWhere"
      [ "module"        @= m
      ]
    ScopeCheckExpr expr -> kind "ScopeCheckExpr"
      [ "expr"          @= expr
      ]
    ScopeCheckDeclaration decl -> kind "ScopeCheckDeclaration"
      [ "declarations"  @= D.notSoNiceDeclarations decl
      ]
    ScopeCheckLHS name pattern -> kind "ScopeCheckLHS"
      [ "name"          @= name
      , "pattern"       @= pattern
      ]
    NoHighlighting -> kind "NoHighlighting" []
    ModuleContents -> kind "ModuleContents" []
    SetRange range -> kind "SetRange"
      [ "range"         @= range
      ]

instance EncodeTCM Constraint where
  encodeTCM constraint = case constraint of
    ValueCmp cmp t e e' -> kind "ValueCmp"
      [ "comparison"  @= cmp
      , "term1"       #= encodeTCMTopCtx e
      , "term2"       #= encodeTCMTopCtx e'
      , "type"        #= encodeTCMTopCtx t
      ]
    ValueCmpOnFace cmp face t e e' -> kind "ValueCmpOnFace"
      [ "comparison"  @= cmp
      , "face"        @= face
      , "type"        #= encodeTCMTopCtx t
      , "term1"       #= encodeTCMTopCtx e
      , "term2"       #= encodeTCMTopCtx e'
      ]
    ElimCmp polarities isForced t e elims1 elims2 -> kind "ElimCmp"
      [ "polarities"  @= polarities
      , "isForced"    @= isForced
      , "type"        #= encodeTCMTopCtx t
      , "term"        #= encodeTCMTopCtx e
      , "elims1"      #= encodeTCMTopCtx elims1
      , "elims2"      #= encodeTCMTopCtx elims2
      ]
    TypeCmp cmp t t' -> kind "TypeCmp"
      [ "comparison"  @= cmp
      , "type1"       #= encodeTCMTopCtx t
      , "type2"       #= encodeTCMTopCtx t'
      ]
    TelCmp t t' cmp tel tel' -> kind "TelCmp"
      [ "comparison"  @= cmp
      , "type1"       #= encodeTCMTopCtx t
      , "type2"       #= encodeTCMTopCtx t'
      , "telescope1"  #= encodeTCMTopCtx tel
      , "telescope2"  #= encodeTCMTopCtx tel'
      ]
    SortCmp cmp s s' -> kind "SortCmp"
      [ "comparison"  @= cmp
      , "sort1"       #= encodeTCMTopCtx s
      , "sort2"       #= encodeTCMTopCtx s'
      ]
    LevelCmp cmp l l' -> kind "LevelCmp"
      [ "comparison"  @= cmp
      , "level1"      #= encodeTCMTopCtx l
      , "level2"      #= encodeTCMTopCtx l'
      ]
    HasBiggerSort sort -> kind "HasBiggerSort"
      [ "sort"        @= sort
      ]
    HasPTSRule sort (I.NoAbs _ binding) -> kind "HasPTSRuleNoAbs"
      [ "sort"        @= sort
      , "binding"     @= binding
      ]
    HasPTSRule sort (I.Abs context binding) -> kind "HasPTSRuleAbs"
      [ "sort"        @= sort
      , "binding"     #= addContext context (encodeTCM binding)
      ]
    UnBlock metaId -> kind "UnBlock"
      [ "metaId"      @= metaId
      ]
    Guarded constraint pid -> kind "Guarded"
      [ "constraint"  @= constraint
      , "problemId"   @= pid
      ]
    IsEmpty range t -> kind "IsEmpty"
      [ "range"       @= range
      , "type"        #= encodeTCMTopCtx t
      ]
    CheckSizeLtSat term -> kind "CheckSizeLtSat"
      [ "term"        #= encodeTCMTopCtx term
      ]
    FindInScope instanceArg metaId candidates -> kind "FindInScope"
      [ "instanceArg" @= instanceArg
      , "metaId"      @= metaId
      , "candidates"  @= maybeToList candidates
      ]
      where maybeToList :: Maybe [a] -> [a]
            maybeToList (Just xs) = xs
            maybeToList Nothing   = []
    CheckFunDef delayed defInfo name clauses -> kind "CheckFunDef"
      [ "name"          @= name
      , "declarations"  @= clauses
      ]

instance EncodeTCM ProblemConstraint where
  encodeTCM (PConstr problems constraint) = obj
    [ "problems"    @= Set.toList problems
    , "constraint"  @= constraint
    ]

instance EncodeTCM TerminationError where
  encodeTCM (TerminationError funcs calls) = obj
    [ "functions"     @= funcs
    , "calls"         @= calls
    ]

instance EncodeTCM CallInfo where
  encodeTCM callInfo = A2C.abstractToConcrete_ (callInfoTarget callInfo) >>= encodeTCM

instance EncodeTCM ProblemId where
instance ToJSON ProblemId where
  toJSON (ProblemId n) = toJSON n


instance EncodeTCM Polarity where
instance ToJSON Polarity where
  toJSON Covariant      = String "Covariant"
  toJSON Contravariant  = String "Contravariant"
  toJSON Invariant      = String "Invariant"
  toJSON Nonvariant     = String "Nonvariant"

instance EncodeTCM IsForced where
instance ToJSON IsForced where
  toJSON Forced         = String "Forced"
  toJSON NotForced      = String "NotForced"

instance EncodeTCM ExplicitToInstance where
instance ToJSON ExplicitToInstance where
  toJSON ExplicitToInstance     = String "ExplicitToInstance"
  toJSON ExplicitStayExplicit   = String "ExplicitStayExplicit"

instance EncodeTCM Candidate where
  encodeTCM (Candidate e t eti overlappable) = obj
    [ "term"          @= e
    , "type"          @= t
    , "eti"           @= eti
    , "overlappable"  @= overlappable
    ]

instance EncodeTCM LHSOrPatSyn where
instance ToJSON LHSOrPatSyn where
  toJSON IsLHS    = "IsLHS"
  toJSON IsPatSyn = "IsPatSyn"

instance EncodeTCM SplitError where
  encodeTCM (NotADatatype t) = kind "NotADatatype"
    [ "type"      @= t
    ]
  encodeTCM (IrrelevantDatatype t) = kind "IrrelevantDatatype"
    [ "type"      @= t
    ]
  encodeTCM (CoinductiveDatatype t) = kind "CoinductiveDatatype"
    [ "type"      @= t
    ]
  encodeTCM (UnificationStuck name tele inferred expected failures) =
    kind "CoinductiveDatatype"
      [ "name"      @= name
      , "telescope" @= tele
      , "inferred"  @= inferred
      , "expected"  @= expected
      , "failures"  @= failures
      ]
  encodeTCM (GenericSplitError s) = kind "GenericSplitError"
    [ "message"  @= s
    ]

instance EncodeTCM NegativeUnification where
  encodeTCM (UnifyConflict tele e e') = kind "UnifyConflict"
    [ "telescope" @= tele
    , "term1"     @= e
    , "term2"     @= e'
    ]
  encodeTCM (UnifyCycle tele n e) = kind "UnifyCycle"
    [ "telescope" @= tele
    , "index"     @= n
    , "term"      @= e
    ]

instance EncodeTCM UnificationFailure where
  encodeTCM (UnifyIndicesNotVars tele t e e' args) = kind "UnifyIndicesNotVars"
    [ "telescope" @= tele
    , "type"      @= t
    , "term1"     @= e
    , "term2"     @= e'
    , "args"      @= args
    ]
  encodeTCM (UnifyRecursiveEq tele t n e) = kind "UnifyRecursiveEq"
    [ "telescope" @= tele
    , "type"      @= t
    , "index"     @= n
    , "term"      @= e
    ]
  encodeTCM (UnifyReflexiveEq tele t e) = kind "UnifyReflexiveEq"
    [ "telescope" @= tele
    , "type"      @= t
    , "term"      @= e
    ]

instance EncodeTCM a => EncodeTCM (Closure a) where
  encodeTCM closure = enterClosure closure encodeTCM
