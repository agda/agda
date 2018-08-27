{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Instances of EncodeTCM or ToJSON under Agda.TypeChecking

module Agda.Interaction.JSON.TypeChecking where

import Data.Aeson
import Data.Function (on)
import Data.List (nub, sortBy)
import Data.Maybe (isJust)

import Agda.Interaction.JSON.Encoding
import Agda.Interaction.JSON.Syntax
import Agda.Interaction.JSON.Utils

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Common as C
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Scope.Monad as S

import Agda.Syntax.Position (Range, Range'(..))

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (PrettyTCM(..), prettyA, prettyPattern)
import Agda.TypeChecking.Telescope (ifPiType)

import Agda.Utils.Pretty (render, pretty)

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
      , "actual"    #= prettyTCM t
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
      , "actual"    @= verbalize (Indefinite h)
      ]

    RelevanceMismatch r r' -> obj
      [ "kind"      @= String "RelevanceMismatch"
      , "expected"  @= verbalize (Indefinite r')
      , "actual"    @= verbalize (Indefinite r)
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

    WrongNumberOfConstructorArguments name expected actual -> obj
      [ "kind"      @= String "WrongNumberOfConstructorArguments"
      , "name"      #= prettyTCM name
      , "expected"  #= prettyTCM expected
      , "actual"    #= prettyTCM actual
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

    -- For unhandled errors, passing only its kind
    _ -> obj [ "kind" @= toJSON (errorString err) ]
