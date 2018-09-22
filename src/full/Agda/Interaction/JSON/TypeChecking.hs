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
    NicifierIssue w -> obj
      [ "kind"                @= String "NicifierIssue"
      , "declarationWarning"  @= w
      ]

    TerminationIssue es -> obj
      [ "kind"                @= String "TerminationIssue"
      , "terminationErrors"   @= es
      ]

    UnreachableClauses name clauses -> obj
      [ "kind"                @= String "UnreachableClauses"
      , "name"                @= name
      -- , "clauses"             @= clauses
      ]

    CoverageIssue name pairs -> obj
      [ "kind"                @= String "CoverageIssue"
      , "name"                @= name
      , "declarations"        @= map f pairs
      ]
      where f (tel, ps) = I2A.NamedClause name True $
                    empty { I.clauseTel = tel, I.namedClausePats = ps }

    CoverageNoExactSplit name clauses -> obj
      [ "kind"                @= String "CoverageNoExactSplit"
      , "name"                @= name
      , "declarations"        @= map f clauses
      ]
      where f clause = I2A.NamedClause name True clause

    NotStrictlyPositive name occursWhere -> obj
      [ "kind"                @= String "NotStrictlyPositive"
      , "name"                @= name
      , "occursWhere"         @= occursWhere
      ]

    UnsolvedMetaVariables ranges -> obj
      [ "kind"                @= String "UnsolvedMetaVariables"
      , "ranges"              @= ranges
      ]

    UnsolvedInteractionMetas ranges -> obj
      [ "kind"                @= String "UnsolvedInteractionMetas"
      , "ranges"              @= ranges
      ]

    UnsolvedConstraints constraints -> obj
      [ "kind"                @= String "UnsolvedConstraints"
      , "constraints"         @= constraints
      ]

    AbsurdPatternRequiresNoRHS clauses -> obj
      [ "kind"                @= String "AbsurdPatternRequiresNoRHS"
      -- , "clauses"             @= clauses
      ]

    OldBuiltin old new -> obj
      [ "kind"                @= String "OldBuiltin"
      , "old"                 @= old
      , "new"                 @= new
      ]

    EmptyRewritePragma -> obj
      [ "kind"                @= String "EmptyRewritePragma"
      ]

    UselessPublic -> obj
      [ "kind"                @= String "UselessPublic"
      ]

    UselessInline name -> obj
      [ "kind"                @= String "UselessInline"
      , "name"                @= name
      ]

    InversionDepthReached name -> obj
      [ "kind"                @= String "InversionDepthReached"
      , "name"                @= name
      ]

    GenericWarning warning -> obj
      [ "kind"                @= String "GenericWarning"
      , "warning"             @= warning
      ]

    GenericNonFatalError message -> obj
      [ "kind"                @= String "GenericNonFatalError"
      , "message"             @= message
      ]

    SafeFlagPostulate name -> obj
      [ "kind"                @= String "SafeFlagPostulate"
      , "name"                @= name
      ]

    SafeFlagPragma pragmas -> obj
      [ "kind"                @= String "SafeFlagPragma"
      , "pragmas"             @= pragmas
      ]

    SafeFlagNonTerminating -> obj
      [ "kind"                @= String "SafeFlagNonTerminating"
      ]

    SafeFlagTerminating -> obj
      [ "kind"                @= String "SafeFlagTerminating"
      ]

    SafeFlagPrimTrustMe -> obj
      [ "kind"                @= String "SafeFlagPrimTrustMe"
      ]

    SafeFlagNoPositivityCheck -> obj
      [ "kind"                @= String "SafeFlagNoPositivityCheck"
      ]

    SafeFlagPolarity -> obj
      [ "kind"                @= String "SafeFlagPolarity"
      ]

    SafeFlagNoUniverseCheck -> obj
      [ "kind"                @= String "SafeFlagNoUniverseCheck"
      ]

    ParseWarning warning -> obj
      [ "kind"                @= String "ParseWarning"
      , "warning"             @= warning
      ]

    DeprecationWarning old new version -> obj
      [ "kind"                @= String "DeprecationWarning"
      , "old"                 @= old
      , "new"                 @= new
      , "version"             @= version
      ]

    UserWarning warning -> obj
      [ "kind"                @= String "UserWarning"
      , "warning"             @= warning
      ]

    ModuleDoesntExport source names -> obj
      [ "kind"                @= String "UserWarning"
      , "sourceModule"        @= source
      , "names"               @= names
      ]

--------------------------------------------------------------------------------

instance EncodeTCM TCErr where
  encodeTCM (TypeError state closure) = localState $ do
    put state
    obj
      [ "kind"      @= String "TypeError"
      , "range"     @= envRange (clEnv closure)
      , "call"      @= (envCall (clEnv closure))
      , "typeError" @= closure
      ]
  encodeTCM (Exception range doc) = obj
    [ "kind"        @= String "Exception"
    , "range"       @= range
    , "message"     @= doc
    ]
  encodeTCM (IOException _ range exception) = obj
    [ "kind"        @= String "IOException"
    , "range"       @= range
    , "message"     @= show exception
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
      , "message" @= d
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

    PropMustBeSingleton -> obj
      [ "kind"  @= String "PropMustBeSingleton" ]

    DataMustEndInSort term -> obj
      [ "kind"  @= String "DataMustEndInSort"
      , "term"  @= term
      ]

    ShouldEndInApplicationOfTheDatatype t -> obj
      [ "kind"  @= String "ShouldEndInApplicationOfTheDatatype"
      , "type"  @= t
      ]

    ShouldBeAppliedToTheDatatypeParameters s t -> obj
      [ "kind"      @= String "ShouldEndInApplicationOfTheDatatype"
      , "expected"  @= s
      , "given"     @= t
      ]

    ShouldBeApplicationOf t q -> obj
      [ "kind" @= String "ShouldBeApplicationOf"
      , "type" @= t
      , "name" @= q
      ]

    ShouldBeRecordType t -> obj
      [ "kind"  @= String "ShouldBeRecordType"
      , "type"  @= t
      ]

    ShouldBeRecordPattern p -> obj
      [ "kind"    @= String "ShouldBeRecordPattern"
      -- , "pattern" @= p
      ]

    NotAProjectionPattern p -> obj
      [ "kind"    @= String "NotAProjectionPattern"
      , "pattern" @= p
      ]

    -- DifferentArities -> obj
    --   [ "kind" @= String "DifferentArities" ]

    WrongHidingInLHS -> obj
      [ "kind" @= String "WrongHidingInLHS" ]

    WrongHidingInLambda t -> obj
      [ "kind" @= String "WrongHidingInLambda"
      , "type" @= t
      ]

    WrongIrrelevanceInLambda -> obj
      [ "kind" @= String "WrongIrrelevanceInLambda" ]

    WrongNamedArgument a -> obj
      [ "kind" @= String "WrongNamedArgument"
      , "args" @= a
      ]

    WrongHidingInApplication t -> obj
      [ "kind" @= String "WrongHidingInApplication"
      , "type" @= t
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
        , "expr" @= e
        ]

    ForcedConstructorNotInstantiated p -> obj
        [ "kind"    @= String "ForcedConstructorNotInstantiated"
        , "pattern" @= p
        ]

    IlltypedPattern p a -> ifPiType a yes no
      where
        yes dom abs = obj
          [ "kind"      @= String "IlltypedPattern"
          , "isPiType"  @= True
          , "pattern"   @= p
          , "dom"       @= dom
          , "abs"       @= show abs
          ]
        no t = obj
          [ "kind"      @= String "IlltypedPattern"
          , "isPiType"  @= False
          , "pattern"   @= p
          , "type"      @= t
          ]

    IllformedProjectionPattern p -> obj
        [ "kind"    @= String "IllformedProjectionPattern"
        , "pattern" @= p
        ]

    CannotEliminateWithPattern p a -> do
      if isJust (A.isProjP p) then
        obj
          [ "kind"          @= String "CannotEliminateWithPattern"
          , "isProjection"  @= True
          , "pattern"       @= p
          ]
      else
        obj
          [ "kind"          @= String "CannotEliminateWithPattern"
          , "isProjection"  @= False
          , "pattern"       @= p
          , "patternKind"   @= kindOfPattern (C.namedArg p)
          ]

    WrongNumberOfConstructorArguments name expected given -> obj
      [ "kind"      @= String "WrongNumberOfConstructorArguments"
      , "name"      @= name
      , "expected"  @= expected
      , "given"     @= given
      ]

    CantResolveOverloadedConstructorsTargetingSameDatatype datatype ctrs -> do
      obj
        [ "kind"          @= String "CantResolveOverloadedConstructorsTargetingSameDatatype"
        , "datatype"      @= datatype
        , "constructors"  @= ctrs
        ]

    DoesNotConstructAnElementOf c t -> obj
      [ "kind"        @= String "DoesNotConstructAnElementOf"
      , "constructor" @= c
      , "type"        @= t
      ]

    ConstructorPatternInWrongDatatype c d -> obj
      [ "kind"        @= String "ConstructorPatternInWrongDatatype"
      , "constructor" @= c
      , "datatype"    @= d
      ]

    ShadowedModule x [] -> __IMPOSSIBLE__
    ShadowedModule x ms -> do
      (range, m) <- handleShadowedModule x ms
      obj
        [ "kind"          @= String "ShadowedModule"
        , "duplicated"    @= x
        , "previous"      @= m
        , "dataOrRecord"  #= S.isDatatypeModule m
        ]

    ModuleArityMismatch m I.EmptyTel args -> obj
      [ "kind"            @= String "ModuleArityMismatch"
      , "module"          @= m
      , "isParameterized" @= False
      ]
    ModuleArityMismatch m tel@(I.ExtendTel _ _) args -> obj
      [ "kind"            @= String "ModuleArityMismatch"
      , "module"          @= m
      , "isParameterized" @= True
      , "telescope"       @= tel
      ]

    ShouldBeEmpty t ps -> obj
      [ "kind"            @= String "ShouldBeEmpty"
      , "type"            @= t
      , "patterns"        #= mapM (prettyPattern 0) ps
      ]

    ShouldBeASort t -> obj
      [ "kind"            @= String "ShouldBeASort"
      , "type"            @= t
      ]

    ShouldBePi t -> obj
      [ "kind"            @= String "ShouldBePi"
      , "type"            @= t
      ]

    ShouldBePath t -> obj
      [ "kind"            @= String "ShouldBePath"
      , "type"            @= t
      ]

    NotAProperTerm -> obj
      [ "kind"            @= String "NotAProperTerm"
      ]

    InvalidTypeSort s -> obj
      [ "kind"            @= String "InvalidTypeSort"
      , "sort"            @= s
      ]

    InvalidType t -> obj
      [ "kind"            @= String "InvalidType"
      , "type"            @= t
      ]

    FunctionTypeInSizeUniv t -> obj
      [ "kind"            @= String "FunctionTypeInSizeUniv"
      , "term"            @= t
      ]

    SplitOnIrrelevant t ->obj
      [ "kind"            @= String "SplitOnIrrelevant"
      , "term"            @= verbalize (C.getRelevance t)
      , "type"            @= (C.unDom t)
      ]

    SplitOnNonVariable term typ ->obj
      [ "kind"            @= String "SplitOnNonVariable"
      , "term"            @= term
      , "type"            @= typ
      ]


    DefinitionIsIrrelevant x -> obj
      [ "kind"            @= String "DefinitionIsIrrelevant"
      , "name"            @= x
      ]

    VariableIsIrrelevant x -> obj
      [ "kind"            @= String "VariableIsIrrelevant"
      , "name"            @= x
      ]

    UnequalBecauseOfUniverseConflict cmp s t -> obj
      [ "kind"            @= String "UnequalBecauseOfUniverseConflict"
      , "comparison"      @= cmp
      , "term1"           @= s
      , "term2"           @= t
      ]


    UnequalTerms cmp s t a -> case refineUnequalTerms cmp s t of
      Just err -> encodeTCM err
      Nothing -> do
        (_, _, d) <- prettyInEqual s t
        obj
          [ "kind"            @= String "UnequalTerms"
          , "comparison"      @= cmp
          , "term1"           @= s
          , "term2"           @= t
          , "type"            @= a
          , "reason"          @= d
          ]

    UnequalTypes cmp a b -> obj
      [ "kind"            @= String "UnequalTypes"
      , "comparison"      @= cmp
      , "type1"           @= a
      , "type2"           @= b
      , "message"         #= prettyUnequal a (notCmp cmp) b
      ]

    UnequalRelevance cmp a b -> obj
      [ "kind"            @= String "UnequalRelevance"
      , "comparison"      @= cmp
      , "term1"           @= a
      , "term2"           @= b
      ]

    UnequalHiding a b -> obj
      [ "kind"            @= String "UnequalHiding"
      , "term1"           @= a
      , "term2"           @= b
      ]

    UnequalSorts a b -> obj
      [ "kind"            @= String "UnequalSorts"
      , "sort1"           @= a
      , "sort2"           @= b
      ]

    NotLeqSort a b -> obj
      [ "kind"            @= String "NotLeqSort"
      , "sort1"           @= a
      , "sort2"           @= b
      ]

    TooFewFields record fields -> obj
      [ "kind"            @= String "TooFewFields"
      , "record"          @= record
      , "fields"          @= fields
      ]

    TooManyFields record fields -> obj
      [ "kind"            @= String "TooManyFields"
      , "record"          @= record
      , "fields"          @= fields
      ]

    DuplicateConstructors xs -> obj
      [ "kind"            @= String "DuplicateConstructors"
      , "constructors"    @=  xs
      ]

    DuplicateFields xs -> obj
      [ "kind"            @= String "DuplicateFields"
      , "fields"          @= xs
      ]

    WithOnFreeVariable expr term -> do
      de <- prettyA expr
      dt <- prettyTCM term
      if show de == show dt
        then obj
          [ "kind"            @= String "WithOnFreeVariable"
          , "variable"        @= term
          ]
        else obj
          [ "kind"            @= String "WithOnFreeVariable"
          , "variable"        @= term
          , "expression"      @= expr
          ]

    UnexpectedWithPatterns xs -> obj
      [ "kind"            @= String "UnexpectedWithPatterns"
      , "patterns"        @= xs
      ]

    -- The arguments are the meta variable, the parameters it can
    -- depend on and the paratemeter that it wants to depend on.
    MetaCannotDependOn meta ps i -> obj
      [ "kind"            @= String "MetaCannotDependOn"
      , "meta"            @= (I.MetaV meta [])
      , "wantsToDependOn" @= (I.var i)
      , "canDepdendOn"    @= (map I.var ps)
      ]

    MetaOccursInItself meta -> obj
      [ "kind"            @= String "MetaOccursInItself"
      , "meta"            @= (I.MetaV meta [])
      ]

    MetaIrrelevantSolution meta term -> obj
      [ "kind"            @= String "MetaIrrelevantSolution"
      , "meta"            @= (I.MetaV meta [])
      , "term"            @= term
      ]

    BuiltinMustBeConstructor s expr -> obj
      [ "kind"            @= String "MetaIrrelevantSolution"
      , "expr"            @= expr
      , "message"         @= s
      ]

    NoSuchBuiltinName s -> obj
      [ "kind"            @= String "NoSuchBuiltinName"
      , "message"         @= s
      ]

    DuplicateBuiltinBinding s x y -> obj
      [ "kind"            @= String "DuplicateBuiltinBinding"
      , "term1"           @= x
      , "term2"           @= y
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
      , "typedBinding"    @= typedBinding
      ]

    NoRHSRequiresAbsurdPattern ps -> obj
      [ "kind"            @= String "NoRHSRequiresAbsurdPattern"
      , "patterns"        @= ps
      ]

    -- AbsurdPatternRequiresNoRHS ps -> obj
    --   [ "kind"            @= String "AbsurdPatternRequiresNoRHS"
    --   , "patterns"        #= mapM prettyA ps
    --   ]

    LocalVsImportedModuleClash m -> obj
      [ "kind"            @= String "LocalVsImportedModuleClash"
      , "module"          @= m
      ]

    SolvedButOpenHoles -> obj
      [ "kind"            @= String "SolvedButOpenHoles"
      ]

    CyclicModuleDependency ms -> obj
      [ "kind"            @= String "CyclicModuleDependency"
      , "modules"         @= ms
      ]

    FileNotFound m files -> obj
      [ "kind"            @= String "FileNotFound"
      , "module"          @= m
      , "filepaths"       @= map filePath files
      ]

    OverlappingProjects f m1 m2 -> obj
      [ "kind"            @= String "OverlappingProjects"
      , "module1"         @= m1
      , "module2"         @= m2
      , "filepath"        @= filePath f
      ]

    AmbiguousTopLevelModuleName m files -> obj
      [ "kind"            @= String "AmbiguousTopLevelModuleName"
      , "module"          @= m
      , "filepaths"       @= map filePath files
      ]

    ClashingFileNamesFor m files -> obj
      [ "kind"            @= String "ClashingFileNamesFor"
      , "module"          @= m
      , "filepaths"       @= map filePath files
      ]

    ModuleDefinedInOtherFile m file file' -> obj
      [ "kind"            @= String "ModuleDefinedInOtherFile"
      , "module"          @= m
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
      , "constructor"     @= c
      ]

    NotInScope xs -> do
      inscope <- Set.toList . S.concreteNamesInScope <$> getScope
      obj
        [ "kind"            @= String "NotInScope"
        , "names"           #= mapM (name inscope) xs
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

    NoSuchModule x -> obj
      [ "kind"          @= String "NoSuchModule"
      , "module"        @= x
      ]

    AmbiguousName x ys -> obj
      [ "kind"          @= String "AmbiguousName"
      , "ambiguousName" @= x
      , "couldReferTo"  @= (toList ys)
      ]

    AmbiguousModule x ys -> obj
      [ "kind"            @= String "AmbiguousModule"
      , "ambiguousModule" @= x
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

    ClashingDefinition x y -> obj
      [ "kind"            @= String "ClashingDefinition"
      , "definition"      @= x
      , "previouslyAt"    @= I.nameBindingSite (I.qnameName y)
      ]

    ClashingModule m1 m2 -> obj
      [ "kind"            @= String "ClashingModule"
      , "module1"         @= m1
      , "module2"         @= m2
      ]

    ClashingImport x y -> obj
      [ "kind"            @= String "ClashingImport"
      , "name1"           @= x
      , "name2"           @= y
      ]

    ClashingModuleImport x y -> obj
      [ "kind"            @= String "ClashingModuleImport"
      , "module1"         @= x
      , "module2"         @= y
      ]

    PatternShadowsConstructor x c -> obj
      [ "kind"            @= String "PatternShadowsConstructor"
      , "patternVariable" @= x
      , "constructor"     @= c
      ]

    DuplicateImports m xs -> obj
      [ "kind"            @= String "DuplicateImports"
      , "module"          @= m
      , "imports"         @= xs
      ]

    -- ModuleDoesntExport m xs -> obj
    --   [ "kind"            @= String "ModuleDoesntExport"
    --   , "module"          @= pretty m
    --   , "doesntExport"    @= map pretty xs
    --   ]

    NotAModuleExpr e -> obj
      [ "kind"            @= String "NotAModuleExpr"
      , "expr"            @= e
      ]

    FieldOutsideRecord -> obj
      [ "kind"            @= String "FieldOutsideRecord"
      ]

    InvalidPattern p -> obj
      [ "kind"            @= String "InvalidPattern"
      , "pattern"         @= p
      ]

    RepeatedVariablesInPattern xs -> obj
      [ "kind"            @= String "RepeatedVariablesInPattern"
      , "variables"       @= xs
      ]

    NotAnExpression e -> obj
      [ "kind"            @= String "NotAnExpression"
      , "expr"            @= e
      ]

    NotAValidLetBinding nd -> obj
      [ "kind"            @= String "NotAnExpression"
      -- , "niceDeclaration" @= show nd
      ]

    NothingAppliedToHiddenArg e -> obj
      [ "kind"            @= String "NothingAppliedToHiddenArg"
      , "expr"            @= e
      ]

    NothingAppliedToInstanceArg e -> obj
      [ "kind"            @= String "NothingAppliedToInstanceArg"
      , "expr"            @= e
      ]

    NoParseForApplication es -> obj
      [ "kind"            @= String "NoParseForApplication"
      , "exprs"           @= (C.RawApp P.noRange es)
      ]

    AmbiguousParseForApplication es es' -> obj
      [ "kind"            @= String "AmbiguousParseForApplication"
      , "cannotParse"     @= (C.RawApp P.noRange es)
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
      , "patternSynonym"  @= (I.headAmbQ x)
      ]

    TooFewArgumentsToPatternSynonym x -> obj
      [ "kind"            @= String "TooFewArgumentsToPatternSynonym"
      , "patternSynonym"  @= (I.headAmbQ x)
      ]

    CannotResolveAmbiguousPatternSynonym defs -> obj
      [ "kind"            @= String "CannotResolveAmbiguousPatternSynonym"
      , "patternSynonym"  @= x
      , "shapes"          #= mapM prDef (toList defs)
      ]
      where
        (x, _) = headNe defs
        prDef (x, (xs, p)) = obj
          [ "patSyn"      @= (A.PatternSynDef x xs p)
          , "bindingSite" @= I.nameBindingSite (I.qnameName x)
          ]

    UnusedVariableInPatternSynonym -> obj
      [ "kind"            @= String "UnusedVariableInPatternSynonym"
      ]

    NoParseForLHS IsLHS p -> obj
      [ "kind"            @= String "NoParseForLHS"
      , "isLHS"           @= True
      , "LHS"             @= p
      ]

    NoParseForLHS IsPatSyn p -> obj
      [ "kind"            @= String "NoParseForLHS"
      , "isLHS"           @= False
      , "patSyn"          @= p
      ]

    AmbiguousParseForLHS lhsOrPatSyn p ps -> obj
      [ "kind"            @= String "AmbiguousParseForLHS"
      , "LHSOrPatSyn"     @= lhsOrPatSyn
      , "cannotParse"     @= p
      , "couldMean"       @= map pretty' ps
      ]
      where
        pretty' p' = pretty $ if show (pretty p) == show (pretty p')
            then unambiguousPattern p'
            else p'

    OperatorInformation sects err -> obj
      [ "kind"              @= String "OperatorInformation"
      , "notationSections"  @= sects
      , "typeError"         @= err
      ]
--
    SplitError e -> obj
      [ "kind"            @= String "SplitError"
      , "error"           @= e
      ]

    ImpossibleConstructor c neg -> obj
      [ "kind"            @= String "ImpossibleConstructor"
      , "constructor"     @= c
      , "negUni"          @= neg
      ]

    TooManyPolarities x n -> obj
      [ "kind"            @= String "TooManyPolarities"
      , "name"            @= x
      , "atMostAllowed"   @= n
      ]

    IFSNoCandidateInScope t -> obj
      [ "kind"            @= String "IFSNoCandidateInScope"
      , "type"            @= t
      ]

    UnquoteFailed err -> obj
      [ "kind"            @= String "UnquoteFailed"
      , "unquoteError"    @= err
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
      , "term"            @= term
      , "type"            @= typ
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
      , "constructor" @= x
      , "use"         @= con
      , "insteadIf"   @= def
      ]

    DefInsteadOfCon x def con -> obj
      [ "kind"        @= String "DefInsteadOfCon"
      , "non-constructor" @= x
      , "use"         @= def
      , "insteadIf"   @= con
      ]

    NonCanonical category term -> obj
      [ "kind"        @= String "NonCanonical"
      , "category"    @= category
      , "term"        @= term
      ]

    BlockedOnMeta _ m ->  obj
      [ "kind"        @= String "BlockedOnMeta"
      , "meta"        @= m
      ]

    UnquotePanic err -> __IMPOSSIBLE__

--------------------------------------------------------------------------------
-- Agda.TypeChecking.Monad.Base

instance EncodeTCM Comparison where
instance ToJSON Comparison where
  toJSON CmpEq = String "CmpEq"
  toJSON CmpLeq = String "CmpLeq"

instance EncodeTCM Call where
  encodeTCM call = S.withContextPrecedence F.TopCtx $ case call of
    CheckClause t clause -> obj
      [ "kind"        @= String "CheckClause"
      , "type"        @= t
      , "clause"      @= clause
      ]
    CheckPattern pattern tel t -> addContext tel $ obj
      [ "kind"        @= String "CheckPattern"
      , "pattern"     @= pattern
      , "type"        @= t
      ]
    CheckLetBinding binding -> obj
      [ "kind"        @= String "CheckLetBinding"
      , "binding"     @= binding
      ]
    InferExpr expr -> obj
      [ "kind"        @= String "InferExpr"
      , "expr"        @= expr
      ]
    CheckExprCall cmp expr t -> obj
      [ "kind"        @= String "CheckExprCall"
      , "comparison"  @= cmp
      , "expr"        @= expr
      , "type"        @= t
      ]
    CheckDotPattern expr t -> obj
      [ "kind"        @= String "CheckDotPattern"
      , "expr"        @= expr
      , "type"        @= t
      ]
    CheckPatternShadowing clause -> obj
      [ "kind"        @= String "CheckPatternShadowing"
      , "clause"      @= clause
      ]
    CheckProjection range name t -> obj
      [ "kind"        @= String "CheckProjection"
      , "range"       @= range
      , "name"        @= name
      , "type"        @= t
      ]
    IsTypeCall expr sort -> obj
      [ "kind"        @= String "IsTypeCall"
      , "expr"        @= expr
      , "sort"        @= sort
      ]
    IsType_ expr -> obj
      [ "kind"        @= String "IsType_"
      , "expr"        @= expr
      ]
    InferVar name -> obj
      [ "kind"        @= String "InferVar"
      , "name"        @= name
      ]
    InferDef name -> obj
      [ "kind"        @= String "InferDef"
      , "name"        @= name
      ]
    CheckArguments range args t1 _ -> obj
      [ "kind"        @= String "CheckArguments"
      , "range"       @= range
      , "arguments"   #= mapM (\ a -> S.withContextPrecedence (F.ArgumentCtx F.PreferParen) (A2C.abstractToConcreteHiding a a)) args
      , "type1"       @= t1
      ]
    CheckTargetType range infTy expTy -> obj
      [ "kind"        @= String "CheckTargetType"
      , "range"       @= range
      , "infType"     @= infTy
      , "expType"     @= expTy
      ]
    CheckDataDef range name bindings constructors -> obj
      [ "kind"          @= String "CheckDataDef"
      , "range"         @= range
      , "name"          @= name
      -- , "bindings"      @= show bindings
      -- , "constructors"  @= show constructors
      ]
    CheckRecDef range name bindings constructors -> obj
      [ "kind"          @= String "CheckDataDef"
      , "name"          @= name
      , "range"         @= range
      -- , "bindings"      @= show bindings
      -- , "constructors"  @= show constructors
      ]
    CheckConstructor d _ _ (A.Axiom _ _ _ _ c _) -> obj
      [ "kind"            @= String "CheckConstructor"
      , "declarationName" @= d
      , "constructorName" @= c
      ]

    CheckConstructor {} -> __IMPOSSIBLE__

    CheckFunDefCall range name _ -> obj
      [ "kind"          @= String "CheckFunDefCall"
      , "range"         @= range
      , "name"          @= name
      -- , "clauses"       @= show clauses
      ]
    CheckPragma range pragma -> obj
      [ "kind"          @= String "CheckPragma"
      , "range"         @= range
      , "pragma"        @= (A2C.RangeAndPragma P.noRange pragma)
      ]
    CheckPrimitive range name expr -> obj
      [ "kind"          @= String "CheckPrimitive"
      , "range"         @= range
      , "name"          @= name
      , "expr"          @= expr
      ]
    CheckIsEmpty range t -> obj
      [ "kind"          @= String "CheckIsEmpty"
      , "range"         @= range
      , "type"          @= t
      ]
    CheckWithFunctionType expr -> obj
      [ "kind"          @= String "CheckWithFunctionType"
      , "expr"          @= expr
      ]
    CheckSectionApplication range m modApp -> obj
      [ "kind"          @= String "CheckSectionApplication"
      , "range"         @= range
      , "module"        @= m
      , "modApp"        @= (A.Apply info m modApp A.initCopyInfo C.defaultImportDir)
      ]
      where
        info = I.ModuleInfo P.noRange P.noRange Nothing Nothing Nothing
    CheckNamedWhere m -> obj
      [ "kind"          @= String "CheckNamedWhere"
      , "module"        @= m
      ]
    ScopeCheckExpr expr -> obj
      [ "kind"          @= String "ScopeCheckExpr"
      , "expr"          @= expr
      ]
    ScopeCheckDeclaration decl -> obj
      [ "kind"          @= String "ScopeCheckDeclaration"
      , "declarations"  @= D.notSoNiceDeclarations decl
      ]
    ScopeCheckLHS name pattern -> obj
      [ "kind"          @= String "ScopeCheckLHS"
      , "name"          @= name
      , "pattern"       @= pattern
      ]
    NoHighlighting -> obj
      [ "kind"          @= String "NoHighlighting"
      ]
    ModuleContents -> obj
      [ "kind"          @= String "ModuleContents"
      ]
    SetRange range -> obj
      [ "kind"          @= String "SetRange"
      , "range"         @= range
      ]

instance EncodeTCM Constraint where
  encodeTCM constraint = case constraint of
    ValueCmp cmp t e e' -> obj
      [ "kind"        @= String "ValueCmp"
      , "comparison"  @= cmp
      , "term1"       @= e
      , "term2"       @= e'
      , "type"        @= t
      ]
    ValueCmpOnFace cmp face t e e' -> obj
      [ "kind"        @= String "ValueCmpOnFace"
      , "comparison"  @= cmp
      , "face"        @= face
      , "type"        @= t
      , "term1"       @= e
      , "term2"       @= e'
      ]
    ElimCmp polarities isForced t e elims1 elims2 -> obj
      [ "kind"        @= String "ElimCmp"
      , "polarities"  @= polarities
      , "isForced"    @= isForced
      , "type"        @= t
      , "term"        @= e
      , "elims1"      @= elims1
      , "elims2"      @= elims2
      ]
    TypeCmp cmp t t' -> obj
      [ "kind"        @= String "TypeCmp"
      , "comparison"  @= cmp
      , "type1"       @= t
      , "type2"       @= t'
      ]
    TelCmp t t' cmp tel tel' -> obj
      [ "kind"        @= String "TelCmp"
      , "comparison"  @= cmp
      , "type1"       @= t
      , "type2"       @= t'
      , "telescope1"  @= tel
      , "telescope2"  @= tel'
      ]
    SortCmp cmp s s' -> obj
      [ "kind"        @= String "SortCmp"
      , "comparison"  @= cmp
      , "sort1"       @= s
      , "sort2"       @= s'
      ]
    LevelCmp cmp l l' -> obj
      [ "kind"        @= String "LevelCmp"
      , "comparison"  @= cmp
      , "level1"      @= l
      , "level2"      @= l'
      ]
    HasBiggerSort sort -> obj
      [ "kind"        @= String "HasBiggerSort"
      , "sort"        @= sort
      ]
    HasPTSRule sort binding -> obj
      [ "kind"        @= String "HasPTSRule"
      , "sort"        @= sort
      , "binding"     @= binding
      ]
    UnBlock metaId -> obj
      [ "kind"        @= String "UnBlock"
      , "metaId"      @= metaId
      ]
    Guarded constraint pid -> obj
      [ "kind"        @= String "Guarded"
      , "constraint"  @= constraint
      , "problemId"   @= pid
      ]
    IsEmpty range t -> obj
      [ "kind"        @= String "IsEmpty"
      , "range"       @= range
      , "type"        @= t
      ]
    CheckSizeLtSat term -> obj
      [ "kind"        @= String "CheckSizeLtSat"
      , "term"        @= term
      ]
    FindInScope instanceArg metaId candidates -> obj
      [ "kind"        @= String "FindInScope"
      , "instanceArg" @= instanceArg
      , "metaId"      @= metaId
      , "candidates"  @= candidates
      ]
    CheckFunDef delayed defInfo name clauses -> obj
      [ "kind"          @= String "CheckFunDef"
      -- , "delayed"     @= delayed
      -- , "defInfo"     @= defInfo
      , "name"          @= name
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
instance ToJSON Candidate where
  toJSON (Candidate e t eti overlappable) = object
    [ "term"          .= e
    , "type"          .= t
    , "eti"           .= eti
    , "overlappable"  .= overlappable
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
