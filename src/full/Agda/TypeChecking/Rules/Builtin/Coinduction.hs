------------------------------------------------------------------------
-- | Handling of the INFINITY, SHARP and FLAT builtins.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Builtin.Coinduction where

import Control.Applicative
import Control.Monad.Error

import qualified Data.Map as Map

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rules.Builtin
import Agda.TypeChecking.Rules.Term

import Agda.Utils.Impossible
import Agda.Utils.Permutation

#include "../../../undefined.h"

varSort n = Type $ Max [Plus 0 $ NeutralLevel $ Var n []]

-- | The type of @&#x221e@.

typeOfInf :: TCM Type
typeOfInf = do
  kit <- requireLevels
  return $
    El Inf (Pi (argH $ El (mkType 0) (lvlType kit))
               (Abs "a" $ El (sSuc $ varSort 0)
                             (Pi (argN $ El (sSuc $ varSort 0)
                                            (Sort $ varSort 0))
                                 (Abs "A" $ El (sSuc $ varSort 1)
                                               (Sort $ varSort 1)))))

-- | The type of @&#x266f_@.

typeOfSharp :: TCM Type
typeOfSharp = do
  kit <- requireLevels
  inf <- (\t -> case t of
                  Def q _ -> q
                  _       -> __IMPOSSIBLE__)
         <$> primInf
  return $
    El Inf (Pi (argH $ El (mkType 0) (lvlType kit))
               (Abs "a" $ El (sSuc $ varSort 0)
                             (Pi (argH $ El (sSuc $ varSort 0) (Sort $ varSort 0))
                                 (Abs "A" $ El (varSort 1)
                                               (Pi (argN $ El (varSort 1) (Var 0 []))
                                                   (Abs "x" $ El (varSort 2)
                                                                 (Def inf [argH (Var 2 []), argN (Var 1 [])])))))))

-- | The type of @&#x266d@.

typeOfFlat :: TCM Type
typeOfFlat = do
  kit <- requireLevels
  inf <- (\t -> case t of
                  Def q _ -> q
                  _       -> __IMPOSSIBLE__)
         <$> primInf
  return $
    El Inf (Pi (argH $ El (mkType 0) (lvlType kit))
               (Abs "a" $ El (sSuc $ varSort 0)
                             (Pi (argH $ El (sSuc $ varSort 0) (Sort $ varSort 0))
                                 (Abs "A" $ El (varSort 1)
                                               (Fun (argN $ El (varSort 1)
                                                               (Def inf [argH (Var 1 []), argN (Var 0 [])]))
                                                    (El (varSort 1) (Var 0 [])))))))

-- | Binds the INFINITY builtin, but does not change the type's
-- definition.

bindBuiltinInf :: A.Expr -> TCM ()
bindBuiltinInf e = bindPostulatedName builtinInf e $ \inf _ ->
  instantiateFull =<< checkExpr (A.Def inf) =<< typeOfInf

-- | Binds the SHARP builtin, and changes the definitions of INFINITY
-- and SHARP.

-- The following (no longer supported) definition is used:
--
-- codata &#x221e {a} (A : Set a) : Set a where
--   &#x266f_ : (x : A) → &#x221e A

bindBuiltinSharp :: A.Expr -> TCM ()
bindBuiltinSharp e =
  bindPostulatedName builtinSharp e $ \sharp sharpDefn -> do
    sharpE  <- instantiateFull =<< checkExpr (A.Def sharp) =<< typeOfSharp
    inf     <- primInf
    infDefn <- case inf of
      Def inf _ -> getConstInfo inf
      _         -> __IMPOSSIBLE__
    addConstant (defName infDefn) $
      infDefn { theDef = Datatype
                  { dataPars           = 2
                  , dataIxs            = 0
                  , dataInduction      = CoInductive
                  , dataClause         = Nothing
                  , dataCons           = [sharp]
                  , dataSort           = varSort 1
                  , dataPolarity       = [Invariant, Invariant]
                  , dataArgOccurrences = [Unused, Positive]
                  , dataAbstr          = ConcreteDef
                  }
              }
    addConstant sharp $
      sharpDefn { theDef = Constructor
                    { conPars   = 2
                    , conSrcCon = sharp
                    , conData   = defName infDefn
                    , conAbstr  = ConcreteDef
                    , conInd    = CoInductive
                    }
                }
    return sharpE

-- | Binds the FLAT builtin, and changes its definition.

-- The following (no longer supported) definition is used:
--
--   &#x266d : ∀ {a} {A : Set a} → &#x221e A → A
--   &#x266d (&#x266f x) = x

bindBuiltinFlat :: A.Expr -> TCM ()
bindBuiltinFlat e =
  bindPostulatedName builtinFlat e $ \flat flatDefn -> do
    flatE  <- instantiateFull =<< checkExpr (A.Def flat) =<< typeOfFlat
    sharp  <- (\t -> case t of
                 Def q _ -> q
                 _       -> __IMPOSSIBLE__)
              <$> primSharp
    kit    <- requireLevels
    let clause = Clause { clauseRange = noRange
                        , clauseTel   = ExtendTel (argH (El (mkType 0) (Def (typeName kit) [])))
                                                  (Abs "a" (ExtendTel (argH (El (sSuc $ varSort 0)
                                                                                (Sort $ varSort 0)))
                                                                      (Abs "A" (ExtendTel (argN (El (varSort 1) (Var 0 [])))
                                                                                          (Abs "x" EmptyTel)))))
                        , clausePerm  = idP 3
                        , clausePats  = [ argH (VarP "a")
                                        , argH (VarP "A")
                                        , argN (ConP sharp Nothing [argN (VarP "x")])
                                        ]
                        , clauseBody  = Bind $ Abs "h0" $
                                        Bind $ Abs "h1" $
                                        Bind $ Abs "h2" $ Body (Var 0 [])
                        }
    addConstant flat $
      flatDefn { theDef = Function
                   { funClauses        = [clause]
                   , funCompiled       = Case 2 (Branches (Map.singleton sharp (Done 3 (Var 0 [])))
                                                          Map.empty
                                                          Nothing)
                   , funInv            = NotInjective
                   , funPolarity       = [Invariant, Invariant, Invariant]
                   , funArgOccurrences = [Unused, Unused, Positive]
                   , funAbstr          = ConcreteDef
                   , funDelayed        = NotDelayed
                   , funProjection     = Nothing
                     {- flat is a projection, but in the termination checker
                        it destroys the (inductive) structural ordering.
                        Thus, we do not register it as a projection. -}
                   }
                }
    return flatE

-- | The coinductive primitives.

data CoinductionKit = CoinductionKit
  { nameOfInf   :: QName
  , nameOfSharp :: QName
  , nameOfFlat  :: QName
  }

-- | Tries to build a 'CoinductionKit'.

coinductionKit :: TCM (Maybe CoinductionKit)
coinductionKit = (do
  Def inf   _ <- primInf
  Def sharp _ <- primSharp
  Def flat  _ <- primFlat
  return $ Just $ CoinductionKit
    { nameOfInf   = inf
    , nameOfSharp = sharp
    , nameOfFlat  = flat
    })
    `catchError` \_ -> return Nothing
