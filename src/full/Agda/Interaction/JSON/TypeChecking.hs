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
import Agda.Interaction.JSON.Syntax.Concrete
import Agda.Interaction.JSON.Utils
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

#include "undefined.h"
import Agda.Utils.Impossible

--------------------------------------------------------------------------------

instance EncodeTCM a => EncodeTCM (Closure a) where
  encodeTCM closure = enterClosure closure encodeTCM

--------------------------------------------------------------------------------

instance EncodeTCM TCErr where
  encodeTCM (TypeError state closure) = localState $ do
    put state
    obj
      [ "kind"      @= String "TypeError"
      , "range"     @= envRange (clEnv closure)
      , "call"      #= encodeTCM (envCall (clEnv closure))
      , "typeError" #= encodeTCM closure
      ]
  encodeTCM (Exception range doc) = obj
    [ "kind"        @= String "Exception"
    , "range"       @= range
    , "message"     @= render doc
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
      , "message" @= (render d)
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
      , "term"  #= rep term
      ]

    ShouldEndInApplicationOfTheDatatype t -> obj
      [ "kind"  @= String "ShouldEndInApplicationOfTheDatatype"
      , "type"  #= rep t
      ]

    ShouldBeAppliedToTheDatatypeParameters s t -> obj
      [ "kind"      @= String "ShouldEndInApplicationOfTheDatatype"
      , "expected"  #= rep s
      , "given"     #= rep t
      ]

    ShouldBeApplicationOf t q -> obj
      [ "kind" @= String "ShouldBeApplicationOf"
      , "type" #= rep t
      , "name" #= A2C.abstractToConcrete_ q
      ]

    ShouldBeRecordType t -> obj
      [ "kind"  @= String "ShouldBeRecordType"
      , "type"  #= rep t
      ]

    ShouldBeRecordPattern p -> obj
      [ "kind"    @= String "ShouldBeRecordPattern"
      -- , "pattern" #= prettyTCM p
      ]

    NotAProjectionPattern p -> obj
      [ "kind"    @= String "NotAProjectionPattern"
      , "pattern" #= A2C.abstractToConcrete_ p
      ]

    -- DifferentArities -> obj
    --   [ "kind" @= String "DifferentArities" ]

    WrongHidingInLHS -> obj
      [ "kind" @= String "WrongHidingInLHS" ]

    WrongHidingInLambda t -> obj
      [ "kind" @= String "WrongHidingInLambda"
      , "type" #= rep t
      ]

    WrongIrrelevanceInLambda -> obj
      [ "kind" @= String "WrongIrrelevanceInLambda" ]

    WrongNamedArgument a -> obj
      [ "kind" @= String "WrongNamedArgument"
      , "args" #= A2C.abstractToConcrete_ a
      ]

    WrongHidingInApplication t -> obj
      [ "kind" @= String "WrongHidingInApplication"
      , "type" #= rep t
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
        , "expr" #= A2C.abstractToConcrete_ e
        ]

    ForcedConstructorNotInstantiated p -> obj
        [ "kind"    @= String "ForcedConstructorNotInstantiated"
        , "pattern" #= A2C.abstractToConcrete_ p
        ]

    IlltypedPattern p a -> ifPiType a yes no
      where
        yes dom abs = obj
          [ "kind"      @= String "IlltypedPattern"
          , "isPiType"  @= True
          , "pattern"   #= A2C.abstractToConcrete_ p
          , "dom"       #= prettyTCM dom
          , "abs"       @= show abs
          ]
        no t = obj
          [ "kind"      @= String "IlltypedPattern"
          , "isPiType"  @= False
          , "pattern"   #= A2C.abstractToConcrete_ p
          , "type"      #= rep t
          ]

    IllformedProjectionPattern p -> obj
        [ "kind"    @= String "IllformedProjectionPattern"
        , "pattern" #= A2C.abstractToConcrete_ p
        ]

    CannotEliminateWithPattern p a -> do
      if isJust (A.isProjP p) then
        obj
          [ "kind"          @= String "CannotEliminateWithPattern"
          , "isProjection"  @= True
          , "pattern"       #= A2C.abstractToConcrete_ p
          ]
      else
        obj
          [ "kind"          @= String "CannotEliminateWithPattern"
          , "isProjection"  @= False
          , "pattern"       #= A2C.abstractToConcrete_ p
          , "patternKind"   @= kindOfPattern (C.namedArg p)
          ]

    WrongNumberOfConstructorArguments name expected given -> obj
      [ "kind"      @= String "WrongNumberOfConstructorArguments"
      , "name"      #= A2C.abstractToConcrete_ name
      , "expected"  #= prettyTCM expected
      , "given"     #= prettyTCM given
      ]

    CantResolveOverloadedConstructorsTargetingSameDatatype datatype ctrs -> do
      obj
        [ "kind"          @= String "CantResolveOverloadedConstructorsTargetingSameDatatype"
        , "datatype"      #= A2C.abstractToConcrete_ datatype
        , "constructors"  #= mapM A2C.abstractToConcrete_ ctrs
        ]

    DoesNotConstructAnElementOf c t -> obj
      [ "kind"        @= String "DoesNotConstructAnElementOf"
      , "constructor" #= A2C.abstractToConcrete_ c
      , "type"        #= rep t
      ]

    ConstructorPatternInWrongDatatype c d -> obj
      [ "kind"        @= String "ConstructorPatternInWrongDatatype"
      , "constructor" #= A2C.abstractToConcrete_ c
      , "datatype"    #= A2C.abstractToConcrete_ d
      ]

    ShadowedModule x [] -> __IMPOSSIBLE__
    ShadowedModule x ms -> do
      (range, m) <- handleShadowedModule x ms
      obj
        [ "kind"        @= String "ShadowedModule"
        , "duplicated"  @= x
        , "previous"    @= range
        , "isDatatype"  #= S.isDatatypeModule m
        ]

    ModuleArityMismatch m I.EmptyTel args -> obj
      [ "kind"            @= String "ModuleArityMismatch"
      , "module"          #= A2C.abstractToConcrete_ m
      , "isParameterized" @= False
      ]
    ModuleArityMismatch m tel@(I.ExtendTel _ _) args -> obj
      [ "kind"            @= String "ModuleArityMismatch"
      , "module"          #= A2C.abstractToConcrete_ m
      , "isParameterized" @= True
      , "telescope"       #= prettyTCM tel
      ]

    ShouldBeEmpty t ps -> obj
      [ "kind"            @= String "ShouldBeEmpty"
      , "type"            #= rep t
      , "patterns"        #= mapM (prettyPattern 0) ps
      ]

    ShouldBeASort t -> obj
      [ "kind"            @= String "ShouldBeASort"
      , "type"            #= rep t
      ]

    ShouldBePi t -> obj
      [ "kind"            @= String "ShouldBePi"
      , "type"            #= rep t
      ]

    ShouldBePath t -> obj
      [ "kind"            @= String "ShouldBePath"
      , "type"            #= rep t
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
      , "type"            #= rep t
      ]

    FunctionTypeInSizeUniv t -> obj
      [ "kind"            @= String "FunctionTypeInSizeUniv"
      , "term"            #= rep t
      ]

    SplitOnIrrelevant t ->obj
      [ "kind"            @= String "SplitOnIrrelevant"
      , "term"            @= verbalize (C.getRelevance t)
      , "type"            #= rep (C.unDom t)
      ]

    SplitOnNonVariable term typ ->obj
      [ "kind"            @= String "SplitOnNonVariable"
      , "term"            #= rep term
      , "type"            #= rep typ
      ]


    DefinitionIsIrrelevant x -> obj
      [ "kind"            @= String "DefinitionIsIrrelevant"
      , "name"            #= A2C.abstractToConcrete_ x
      ]

    VariableIsIrrelevant x -> obj
      [ "kind"            @= String "VariableIsIrrelevant"
      , "name"            #= A2C.abstractToConcrete_ x
      ]

    UnequalBecauseOfUniverseConflict cmp s t -> obj
      [ "kind"            @= String "UnequalBecauseOfUniverseConflict"
      , "comparison"      @= cmp
      , "term1"           #= rep s
      , "term2"           #= rep t
      ]


    UnequalTerms cmp s t a -> case refineUnequalTerms cmp s t of
      Just err -> encodeTCM err
      Nothing -> do
        (_, _, d) <- prettyInEqual s t
        obj
          [ "kind"            @= String "UnequalTerms"
          , "comparison"      @= cmp
          , "term1"           #= rep s
          , "term2"           #= rep t
          , "type"            #= rep a
          , "reason"          @= d
          ]

    UnequalTypes cmp a b -> obj
      [ "kind"            @= String "UnequalTypes"
      , "comparison"      @= cmp
      , "type1"           #= rep a
      , "type2"           #= rep b
      , "message"         #= prettyUnequal a (notCmp cmp) b
      ]

    UnequalRelevance cmp a b -> obj
      [ "kind"            @= String "UnequalRelevance"
      , "comparison"      @= cmp
      , "term1"           #= rep a
      , "term2"           #= rep b
      ]

    UnequalHiding a b -> obj
      [ "kind"            @= String "UnequalHiding"
      , "term1"           #= rep a
      , "term2"           #= rep b
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
      , "record"          #= A2C.abstractToConcrete_ record
      , "fields"          @= fields
      ]

    TooManyFields record fields -> obj
      [ "kind"            @= String "TooManyFields"
      , "record"          #= A2C.abstractToConcrete_ record
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
          , "variable"        #= rep term
          ]
        else obj
          [ "kind"            @= String "WithOnFreeVariable"
          , "variable"        #= rep term
          , "expression"      #= A2C.abstractToConcrete_ expr
          ]

    UnexpectedWithPatterns xs -> obj
      [ "kind"            @= String "UnexpectedWithPatterns"
      , "patterns"        #= mapM A2C.abstractToConcrete_ xs
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
      , "term"            #= rep term
      ]

    BuiltinMustBeConstructor s expr -> obj
      [ "kind"            @= String "MetaIrrelevantSolution"
      , "expr"            #= A2C.abstractToConcrete_ expr
      , "message"         @= s
      ]

    NoSuchBuiltinName s -> obj
      [ "kind"            @= String "NoSuchBuiltinName"
      , "message"         @= s
      ]

    DuplicateBuiltinBinding s x y -> obj
      [ "kind"            @= String "DuplicateBuiltinBinding"
      , "term1"           #= rep x
      , "term2"           #= rep y
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
      , "patterns"        #= mapM A2C.abstractToConcrete_ ps
      ]

    -- AbsurdPatternRequiresNoRHS ps -> obj
    --   [ "kind"            @= String "AbsurdPatternRequiresNoRHS"
    --   , "patterns"        #= mapM prettyA ps
    --   ]

    LocalVsImportedModuleClash m -> obj
      [ "kind"            @= String "LocalVsImportedModuleClash"
      , "module"          #= A2C.abstractToConcrete_ m
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
      , "constructor"     #= A2C.abstractToConcrete_ c
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
      , "couldReferTo"  #= mapM A2C.abstractToConcrete_ (toList ys)
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
          , "name"          #= A2C.abstractToConcrete_ m
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
      , "module1"         #= A2C.abstractToConcrete_ m1
      , "module2"         #= A2C.abstractToConcrete_ m2
      ]

    ClashingImport x y -> obj
      [ "kind"            @= String "ClashingImport"
      , "name1"           @= x
      , "name2"           #= A2C.abstractToConcrete_ y
      ]

    ClashingModuleImport x y -> obj
      [ "kind"            @= String "ClashingModuleImport"
      , "module1"         @= x
      , "module2"         #= A2C.abstractToConcrete_ y
      ]

    PatternShadowsConstructor x c -> obj
      [ "kind"            @= String "PatternShadowsConstructor"
      , "patternVariable" #= A2C.abstractToConcrete_ x
      , "constructor"     #= A2C.abstractToConcrete_ c
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
      , "patternSynonym"  #= A2C.abstractToConcrete_ (I.headAmbQ x)
      ]

    TooFewArgumentsToPatternSynonym x -> obj
      [ "kind"            @= String "TooFewArgumentsToPatternSynonym"
      , "patternSynonym"  #= A2C.abstractToConcrete_ (I.headAmbQ x)
      ]

    CannotResolveAmbiguousPatternSynonym defs -> obj
      [ "kind"            @= String "CannotResolveAmbiguousPatternSynonym"
      , "patternSynonym"  #= A2C.abstractToConcrete_ x
      , "shapes"          #= mapM prDef (toList defs)
      ]
      where
        (x, _) = headNe defs
        prDef (x, (xs, p)) = obj
          [ "patSyn"      #= A2C.abstractToConcrete_ (A.PatternSynDef x xs p)
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
      , "LHSOrPatSyn"     @= show lhsOrPatSyn
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
      , "typeError"         #= encodeTCM err
      ]
--
    SplitError e -> obj
      [ "kind"            @= String "SplitError"
      , "error"           #= prettyTCM e
      ]

    ImpossibleConstructor c neg -> obj
      [ "kind"            @= String "ImpossibleConstructor"
      , "constructor"     @= c
      , "negUni"          #= prettyTCM neg
      ]

    TooManyPolarities x n -> obj
      [ "kind"            @= String "TooManyPolarities"
      , "name"            @= x
      , "atMostAllowed"   @= n
      ]

    IFSNoCandidateInScope t -> obj
      [ "kind"            @= String "IFSNoCandidateInScope"
      , "type"            #= rep t
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
      , "term"            #= rep term
      , "type"            #= rep typ
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
      , "constructor" #= A2C.abstractToConcrete_ x
      , "use"         @= con
      , "insteadIf"   @= def
      ]

    DefInsteadOfCon x def con -> obj
      [ "kind"        @= String "DefInsteadOfCon"
      , "non-constructor" #= A2C.abstractToConcrete_ x
      , "use"         @= def
      , "insteadIf"   @= con
      ]

    NonCanonical category term -> obj
      [ "kind"        @= String "NonCanonical"
      , "category"    @= category
      , "term"        #= rep term
      ]

    BlockedOnMeta _ m ->  obj
      [ "kind"        @= String "BlockedOnMeta"
      , "meta"        #= prettyTCM m
      ]

    UnquotePanic err -> __IMPOSSIBLE__

--------------------------------------------------------------------------------
-- Agda.TypeChecking.Monad.Base

instance ToJSON Comparison where
  toJSON CmpEq = String "CmpEq"
  toJSON CmpLeq = String "CmpLeq"

instance EncodeTCM Call where
  encodeTCM call = S.withContextPrecedence F.TopCtx $ case call of
    CheckClause t clause -> obj
      [ "kind"        @= String "CheckClause"
      , "type"        #= rep t
      , "clause"      #= A2C.abstractToConcrete_ clause
      ]
    CheckPattern pattern tel t -> addContext tel $ obj
      [ "kind"        @= String "CheckPattern"
      , "pattern"     #= A2C.abstractToConcrete_ pattern
      , "type"        #= rep t
      ]
    CheckLetBinding binding -> obj
      [ "kind"        @= String "CheckLetBinding"
      , "binding"     #= A2C.abstractToConcrete_ binding
      ]
    InferExpr expr -> obj
      [ "kind"        @= String "InferExpr"
      , "expr"        #= A2C.abstractToConcrete_ expr
      ]
    CheckExprCall cmp expr t -> obj
      [ "kind"        @= String "CheckExprCall"
      , "comparison"  @= cmp
      , "expr"        #= A2C.abstractToConcrete_ expr
      , "type"        #= rep t
      ]
    CheckDotPattern expr t -> obj
      [ "kind"        @= String "CheckDotPattern"
      , "expr"        #= A2C.abstractToConcrete_ expr
      , "type"        #= rep t
      ]
    CheckPatternShadowing clause -> obj
      [ "kind"        @= String "CheckPatternShadowing"
      , "clause"      #= A2C.abstractToConcrete_ clause
      ]
    CheckProjection range name t -> obj
      [ "kind"        @= String "CheckProjection"
      , "range"       @= range
      , "name"        #= A2C.abstractToConcrete_ name
      , "type"        #= rep t
      ]
    IsTypeCall expr sort -> obj
      [ "kind"        @= String "IsTypeCall"
      , "expr"        #= A2C.abstractToConcrete_ expr
      , "sort"        @= sort
      ]
    IsType_ expr -> obj
      [ "kind"        @= String "IsType_"
      , "expr"        #= A2C.abstractToConcrete_ expr
      ]
    InferVar name -> obj
      [ "kind"        @= String "InferVar"
      , "name"        #= A2C.abstractToConcrete_ name
      ]
    InferDef name -> obj
      [ "kind"        @= String "InferDef"
      , "name"        #= A2C.abstractToConcrete_ name
      ]
    CheckArguments range args t1 _ -> obj
      [ "kind"        @= String "CheckArguments"
      , "range"       @= range
      , "arguments"   #= mapM (\ a -> S.withContextPrecedence (F.ArgumentCtx F.PreferParen) (A2C.abstractToConcreteHiding a a)) args
      , "type1"       #= rep t1
      ]
    CheckTargetType range infTy expTy -> obj
      [ "kind"        @= String "CheckTargetType"
      , "range"       @= range
      , "infType"     #= rep infTy
      , "expType"     #= rep expTy
      ]
    CheckDataDef range name bindings constructors -> obj
      [ "kind"          @= String "CheckDataDef"
      , "range"         @= range
      , "name"          #= A2C.abstractToConcrete_ name
      -- , "bindings"      @= show bindings
      -- , "constructors"  @= show constructors
      ]
    CheckRecDef range name bindings constructors -> obj
      [ "kind"          @= String "CheckDataDef"
      , "name"          #= A2C.abstractToConcrete_ name
      , "range"         @= range
      -- , "bindings"      @= show bindings
      -- , "constructors"  @= show constructors
      ]
    CheckConstructor d _ _ (A.Axiom _ _ _ _ c _) -> obj
      [ "kind"            @= String "CheckConstructor"
      , "declarationName" #= A2C.abstractToConcrete_ d
      , "constructorName" #= A2C.abstractToConcrete_ c
      ]

    CheckConstructor {} -> __IMPOSSIBLE__

    CheckFunDefCall range name _ -> obj
      [ "kind"          @= String "CheckFunDefCall"
      , "range"         @= range
      , "name"          #= A2C.abstractToConcrete_ name
      -- , "clauses"       @= show clauses
      ]
    CheckPragma range pragma -> obj
      [ "kind"          @= String "CheckPragma"
      , "range"         @= range
      , "pragma"        #= A2C.abstractToConcrete_ (A2C.RangeAndPragma P.noRange pragma)
      ]
    CheckPrimitive range name expr -> obj
      [ "kind"          @= String "CheckPrimitive"
      , "range"         @= range
      , "name"          #= A2C.abstractToConcrete_ name
      , "expr"          #= A2C.abstractToConcrete_ expr
      ]
    CheckIsEmpty range t -> obj
      [ "kind"          @= String "CheckIsEmpty"
      , "range"         @= range
      , "type"          #= rep t
      ]
    CheckWithFunctionType expr -> obj
      [ "kind"          @= String "CheckWithFunctionType"
      , "expr"          #= A2C.abstractToConcrete_ expr
      ]
    CheckSectionApplication range m modApp -> obj
      [ "kind"          @= String "CheckSectionApplication"
      , "range"         @= range
      , "module"        #= A2C.abstractToConcrete_ m
      , "modApp"        #= A2C.abstractToConcrete_ (A.Apply info m modApp A.initCopyInfo C.defaultImportDir)
      ]
      where
        info = I.ModuleInfo P.noRange P.noRange Nothing Nothing Nothing
    CheckNamedWhere m -> obj
      [ "kind"          @= String "CheckNamedWhere"
      , "module"        #= A2C.abstractToConcrete_ m
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
