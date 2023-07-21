{-# OPTIONS_GHC -Wunused-imports #-}

------------------------------------------------------------------------
-- | Handling of the INFINITY, SHARP and FLAT builtins.
------------------------------------------------------------------------

module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Agda.Interaction.Options.Base

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rules.Builtin
import Agda.TypeChecking.Rules.Term

import Agda.Utils.Lens

-- | The type of @∞@.

typeOfInf :: TCM Type
typeOfInf = hPi "a" (el primLevel) $
            (return . sort $ varSort 0) --> (return . sort $ varSort 0)

-- | The type of @♯_@.

typeOfSharp :: TCM Type
typeOfSharp = hPi "a" (el primLevel) $
              hPi "A" (return . sort $ varSort 0) $
              (El (varSort 1) <$> varM 0) -->
              (El (varSort 1) <$> primInf <#> varM 1 <@> varM 0)

-- | The type of @♭@.

typeOfFlat :: TCM Type
typeOfFlat = hPi "a" (el primLevel) $
             hPi "A" (return . sort $ varSort 0) $
             (El (varSort 1) <$> primInf <#> varM 1 <@> varM 0) -->
             (El (varSort 1) <$> varM 0)

-- | Binds the INFINITY builtin, but does not change the type's
-- definition.

bindBuiltinInf :: ResolvedName -> TCM ()
bindBuiltinInf x = bindPostulatedName builtinInf x $ \inf _ -> do
  _ <- checkExpr (A.Def inf) =<< typeOfInf
  return $ Def inf []

-- | Binds the SHARP builtin, and changes the definitions of INFINITY
-- and SHARP.

-- The following (no longer supported) definition is used:
--
-- codata ∞ {a} (A : Set a) : Set a where
--   ♯_ : (x : A) → ∞ A

bindBuiltinSharp :: ResolvedName -> TCM ()
bindBuiltinSharp x =
  bindPostulatedName builtinSharp x $ \sharp sharpDefn -> do
    sharpType <- typeOfSharp
    TelV fieldTel _ <- telView sharpType
    _ <- checkExpr (A.Def sharp) sharpType
    Def inf _ <- primInf
    infDefn   <- getConstInfo inf
    erasure   <- optErasure <$> pragmaOptions
    addConstant (defName infDefn) $
      infDefn { defPolarity       = [] -- not monotone
              , defArgOccurrences = [Unused, StrictPos]
              , theDef = Record
                  { recPars           = 2
                  , recInduction      = Just CoInductive
                  , recClause         = Nothing
                  , recConHead        = ConHead sharp (IsRecord CopatternMatching) CoInductive []  -- flat is added later
                  , recNamedCon       = True
                  , recFields         = []  -- flat is added later
                  , recTel            = fieldTel
                  , recEtaEquality'   = Inferred $ NoEta CopatternMatching
                  , recPatternMatching= CopatternMatching
                  , recMutual         = Just []
                  , recTerminates     = Just True  -- not recursive
                  , recAbstr          = ConcreteDef
                  , recComp           = emptyCompKit
                  }
              }
    addConstant sharp $
      sharpDefn { theDef = Constructor
                    { conPars   = 2
                    , conArity  = 1
                    , conSrcCon = ConHead sharp (IsRecord CopatternMatching) CoInductive [] -- flat is added as field later
                    , conData   = defName infDefn
                    , conAbstr  = ConcreteDef
                    , conComp   = emptyCompKit
                    , conProj   = Nothing
                    , conForced = []
                    , conErased = Nothing
                    , conErasure = erasure
                    , conInline  = True  -- This might make the sharp-translation superfluous.
                    }
                }
    return $ Def sharp []

-- | Binds the FLAT builtin, and changes its definition.

-- The following (no longer supported) definition is used:
--
--   ♭ : ∀ {a} {A : Set a} → ∞ A → A
--   ♭ (♯ x) = x

bindBuiltinFlat :: ResolvedName -> TCM ()
bindBuiltinFlat x =
  bindPostulatedName builtinFlat x $ \ flat flatDefn -> do
    _ <- checkExpr (A.Def flat) =<< typeOfFlat
    Def sharp _ <- primSharp
    kit         <- requireLevels
    Def inf _   <- primInf
    let sharpCon = ConHead sharp (IsRecord CopatternMatching) CoInductive [defaultArg flat]
        level    = El (mkType 0) $ Def (typeName kit) []
        tel     :: Telescope
        tel      = ExtendTel (domH $ level)                  $ Abs "a" $
                   ExtendTel (domH $ sort $ varSort 0)       $ Abs "A" $
                   ExtendTel (domN $ El (varSort 1) $ var 0) $ Abs "x" $
                   EmptyTel
        infA     = El (varSort 2) $ Def inf [ Apply $ defaultArg $ var 1 ]
        cpi      = noConPatternInfo { conPType = Just $ defaultArg infA
                                    , conPLazy = True }
    let clause   = Clause
          { clauseLHSRange  = noRange
          , clauseFullRange = noRange
          , clauseTel       = tel
          , namedClausePats = [ argN $ Named Nothing $
              ConP sharpCon cpi [ argN $ Named Nothing $ debruijnNamedVar "x" 0 ] ]
          , clauseBody      = Just $ var 0
          , clauseType      = Just $ defaultArg $ El (varSort 2) $ var 1
          , clauseCatchall    = False
          , clauseExact       = Just True
          , clauseRecursive   = Just False
          , clauseUnreachable = Just False
          , clauseEllipsis    = NoEllipsis
          , clauseWhereModule = Nothing
          }
        cc = Case (defaultArg 0) $ conCase sharp False $ WithArity 1 $ Done [defaultArg "x"] $ var 0
        projection = Projection
          { projProper   = Just inf
          , projOrig     = flat
          , projFromType = defaultArg inf
          , projIndex    = 3
          , projLams     = ProjLams $ [ argH "a" , argH "A" , argN "x" ]
          }
    fun <- emptyFunctionData
    addConstant flat $
      flatDefn { defPolarity       = []
               , defArgOccurrences = [StrictPos]  -- changing that to [Mixed] destroys monotonicity of 'Rec' in test/succeed/GuardednessPreservingTypeConstructors
               , defCopatternLHS = hasProjectionPatterns cc
               , theDef = FunctionDefn fun
                   { _funClauses      = [clause]
                   , _funCompiled     = Just $ cc
                   , _funProjection   = Right projection
                   , _funMutual       = Just []
                   , _funTerminates   = Just True
                   }
                }

    -- register flat as record field for constructor sharp
    modifySignature $ updateDefinition sharp $ updateTheDef $ over lensConstructor $ \ def ->
      def { _conSrcCon = sharpCon }
    modifySignature $ updateDefinition inf $ updateTheDef $ over lensRecord $ \ def ->
      def { _recConHead = sharpCon, _recFields = [defaultDom flat] }
    return $ Def flat []

-- The coinductive primitives.
-- moved to TypeChecking.Monad.Builtin
