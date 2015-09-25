-- {-# LANGUAGE CPP #-}

------------------------------------------------------------------------
-- | Handling of the INFINITY, SHARP and FLAT builtins.
------------------------------------------------------------------------

module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Control.Applicative

import qualified Data.Map as Map

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rules.Builtin
import Agda.TypeChecking.Rules.Term

import Agda.Utils.Permutation

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

bindBuiltinInf :: A.Expr -> TCM ()
bindBuiltinInf e = bindPostulatedName builtinInf e $ \inf _ ->
  instantiateFull =<< checkExpr (A.Def inf) =<< typeOfInf

-- | Binds the SHARP builtin, and changes the definitions of INFINITY
-- and SHARP.

-- The following (no longer supported) definition is used:
--
-- codata ∞ {a} (A : Set a) : Set a where
--   ♯_ : (x : A) → ∞ A

bindBuiltinSharp :: A.Expr -> TCM ()
bindBuiltinSharp e =
  bindPostulatedName builtinSharp e $ \sharp sharpDefn -> do
    sharpType <- typeOfSharp
    TelV fieldTel _ <- telView sharpType
    sharpE    <- instantiateFull =<< checkExpr (A.Def sharp) sharpType
    Def inf _ <- ignoreSharing <$> primInf
    infDefn   <- getConstInfo inf
    addConstant (defName infDefn) $
      infDefn { defPolarity       = [] -- not monotone
              , defArgOccurrences = [Unused, StrictPos]
              , theDef = Record
                  { recPars           = 2
                  , recInduction      = Just CoInductive
                  , recClause         = Nothing
                  , recConHead        = ConHead sharp CoInductive []  -- flat is added later
                  , recConType        = sharpType
                  , recNamedCon       = True
                  , recFields         = []  -- flat is added later
                  , recTel            = fieldTel
                  , recRecursive      = False
                  , recEtaEquality'   = Inferred False
                  , recMutual         = []
                  , recAbstr          = ConcreteDef
                  }
              }
    addConstant sharp $
      sharpDefn { theDef = Constructor
                    { conPars   = 2
                    , conSrcCon = ConHead sharp CoInductive [] -- flat is added as field later
                    , conData   = defName infDefn
                    , conAbstr  = ConcreteDef
                    , conInd    = CoInductive
                    }
                }
    return sharpE

-- | Binds the FLAT builtin, and changes its definition.

-- The following (no longer supported) definition is used:
--
--   ♭ : ∀ {a} {A : Set a} → ∞ A → A
--   ♭ (♯ x) = x

bindBuiltinFlat :: A.Expr -> TCM ()
bindBuiltinFlat e =
  bindPostulatedName builtinFlat e $ \ flat flatDefn -> do
    flatE       <- instantiateFull =<< checkExpr (A.Def flat) =<< typeOfFlat
    Def sharp _ <- ignoreSharing <$> primSharp
    kit         <- requireLevels
    Def inf _   <- ignoreSharing <$> primInf
    let sharpCon = ConHead sharp CoInductive [flat]
        level    = El (mkType 0) $ Def (typeName kit) []
        tel     :: Telescope
        tel      = ExtendTel (domH $ level)                  $ Abs "a" $
                   ExtendTel (domH $ sort $ varSort 0)       $ Abs "A" $
                   ExtendTel (domN $ El (varSort 1) $ var 0) $ Abs "x" $
                   EmptyTel
        infA     = El (varSort 2) $ Def inf [ Apply $ defaultArg $ var 1 ]
        cpi      = ConPatternInfo Nothing $ Just $ defaultArg infA
    let clause   = Clause
          { clauseRange     = noRange
          , clauseTel       = tel
          , clausePerm      = idP 1
          , namedClausePats = [ argN $ Named Nothing $
              ConP sharpCon cpi [ argN $ Named Nothing $ VarP "x" ] ]
          , clauseBody      = Bind $ Abs "x" $ Body $ var 0
          , clauseType      = Just $ defaultArg $ El (varSort 2) $ var 1
          , clauseCatchall  = False
          }
        cc = Case 0 $ Branches False
                               (Map.singleton sharp
                                 $ WithArity 1 $ Done [defaultArg "x"] $ var 0)
                               Map.empty
                               Nothing
        projection = Projection
          { projProper   = Just flat
          , projFromType = inf
          , projIndex    = 3
          , projDropPars = teleNoAbs (take 2 $ telToList tel) $ Lam defaultArgInfo $ Abs "x" $ Var 0 [Proj flat]
          , projArgInfo  = defaultArgInfo
          }
    addConstant flat $
      flatDefn { defPolarity       = []
               , defArgOccurrences = [StrictPos]  -- changing that to [Mixed] destroys monotonicity of 'Rec' in test/succeed/GuardednessPreservingTypeConstructors
               , theDef = Function
                   { funClauses    = [clause]
                   , funCompiled   = Just $ cc
                   , funInv        = NotInjective
                   , funMutual     = []
                   , funAbstr      = ConcreteDef
                   , funDelayed    = NotDelayed
                   , funProjection = Just projection
                   , funSmashable  = False
                   , funStatic     = False
                   , funCopy       = False
                   , funTerminates = Just True
                   , funExtLam     = Nothing
                   , funWith       = Nothing
                   , funCopatternLHS = isCopatternLHS [clause]
                   }
                }

    -- register flat as record field for constructor sharp
    modifySignature $ updateDefinition sharp $ updateTheDef $ \ def ->
      def { conSrcCon = sharpCon }
    modifySignature $ updateDefinition inf $ updateTheDef $ \ def ->
      def { recConHead = sharpCon, recFields = [defaultArg flat] }
    return flatE

-- The coinductive primitives.
-- moved to TypeChecking.Monad.Builtin
