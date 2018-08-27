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
import Agda.Syntax.Position (Range, Range'(..))

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (PrettyTCM(..), prettyA)
import Agda.TypeChecking.Telescope (ifPiType)

import Agda.Utils.Pretty (render, pretty)
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

    -- WrongNumberOfConstructorArguments name expected actual -> obj
    --   [ "kind"      @= String "WrongNumberOfConstructorArguments"
    --   , "name"      #= prettyTCM name
    --   , "expected"  #= prettyTCM expected
    --   , "actual"    #= prettyTCM actual
    --   ]
    --
    -- CantResolveOverloadedConstructorsTargetingSameDatatype datatype ctrs -> do
    --   obj
    --     [ "kind"          @= String "CantResolveOverloadedConstructorsTargetingSameDatatype"
    --     , "datatype"      #= prettyTCM (I.qnameToConcrete datatype)
    --     , "constructors"  #= mapM prettyTCM ctrs
    --     ]
    --
    -- DoesNotConstructAnElementOf c t -> obj
    --   [ "kind"        @= String "DoesNotConstructAnElementOf"
    --   , "constructor" #= prettyTCM c
    --   , "type"        #= prettyTCM t
    --   ]
    --
    -- ConstructorPatternInWrongDatatype c d -> obj
    --   [ "kind"        @= String "ConstructorPatternInWrongDatatype"
    --   , "constructor" #= prettyTCM c
    --   , "datatype"    #= prettyTCM d
    --   ]
    --
    -- ShadowedModule x [] -> __IMPOSSIBLE__
    -- ShadowedModule x ms@(m0 : _) -> do
    --   -- Clash! Concrete module name x already points to the abstract names ms.
    --   (r, m) <- do
    --     -- Andreas, 2017-07-28, issue #719.
    --     -- First, we try to find whether one of the abstract names @ms@ points back to @x@
    --     scope <- getScope
    --     -- Get all pairs (y,m) such that y points to some m ∈ ms.
    --     let xms0 = ms >>= \ m -> map (,m) $ S.inverseScopeLookupModule m scope
    --     reportSLn "scope.clash.error" 30 $ "candidates = " ++ prettyShow xms0
    --
    --     -- Try to find x (which will have a different Range, if it has one (#2649)).
    --     let xms = filter ((\ y -> not (null $ getRange y) && y == C.QName x) . fst) xms0
    --     reportSLn "scope.class.error" 30 $ "filtered candidates = " ++ prettyShow xms
    --
    --     -- If we found a copy of x with non-empty range, great!
    --     ifJust (headMaybe xms) (\ (x', m) -> return (getRange x', m)) $ {-else-} do
    --
    --     -- If that failed, we pick the first m from ms which has a nameBindingSite.
    --     let rms = ms >>= \ m -> map (,m) $
    --           filter (noRange /=) $ map A.nameBindingSite $ reverse $ A.mnameToList m
    --           -- Andreas, 2017-07-25, issue #2649
    --           -- Take the first nameBindingSite we can get hold of.
    --     reportSLn "scope.class.error" 30 $ "rangeful clashing modules = " ++ prettyShow rms
    --
    --     -- If even this fails, we pick the first m and give no range.
    --     return $ fromMaybe (noRange, m0) $ headMaybe rms
    --
    --   obj
    --     [ "kind"        @= String "ShadowedModule"
    --     , "duplicated"  #= prettyTCM x
    --     , "previous"    #= prettyTCM r
    --     , "isDatatype"  #= S.isDatatypeModule m
    --     ]


    -- For unhandled errors, passing only its kind
    _ -> obj [ "kind" @= toJSON (errorString err) ]
