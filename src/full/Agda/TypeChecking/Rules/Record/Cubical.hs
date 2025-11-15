{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Record.Cubical
  ( addCompositionForRecord
  ) where

import Prelude hiding (null, not, (&&), (||))

import Control.Monad
import Data.Maybe

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.Rules.Data (defineCompData, defineKanOperationForFields)

import Agda.Utils.Boolean
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Impossible
import Agda.Utils.Size


addCompositionForRecord
  :: QName       -- ^ Datatype name.
  -> EtaEquality
  -> ConHead
  -> Telescope   -- ^ @Γ@ parameters.
  -> [Arg QName] -- ^ Projection names.
  -> Telescope   -- ^ @Γ ⊢ Φ@ field types.
  -> Type        -- ^ @Γ ⊢ T@ target type.
  -> TCM ()
addCompositionForRecord name eta con tel fs ftel rect = do
  cxt <- getContextTelescope
  inTopContext $ do

    -- Record has no fields: attach composition data to record constructor
    if null fs then do
      kit <- defineCompData name con (abstract cxt tel) [] ftel rect empty
      modifySignature $ updateDefinition (conName con) $ updateTheDef $ \case
        r@Constructor{} -> r { conComp = kit, conProj = Just [] }  -- no projections
        _ -> __IMPOSSIBLE__

    -- No-eta record with pattern matching (i.e., withOUT copattern
    -- matching): define composition as for a data type, attach it to
    -- the record.
    else if theEtaEquality eta == NoEta PatternMatching then do
      kit <- defineCompData name con (abstract cxt tel) (unArg <$> fs) ftel rect empty
      modifySignature $ updateDefinition name $ updateTheDef $ \case
        r@Record{} -> r { recComp = kit }
        _ -> __IMPOSSIBLE__

    -- Record has fields: attach composition data to record type
    else do
      -- If record has irrelevant fields but irrelevant projections are disabled,
      -- we cannot generate composition data.
      kit <- ifM (return (any isIrrelevant fs)
                  `and2M` do not . optIrrelevantProjections <$> pragmaOptions)
        {-then-} (return emptyCompKit)
        {-else-} (defineCompKitR name (abstract cxt tel) ftel fs rect)
      modifySignature $ updateDefinition name $ updateTheDef $ \case
        r@Record{} -> r { recComp = kit }
        _          -> __IMPOSSIBLE__


defineCompKitR ::
    QName          -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM CompKit
defineCompKitR name params fsT fns rect = do
  required <- mapM getTerm'
        [ someBuiltin builtinInterval
        , someBuiltin builtinIZero
        , someBuiltin builtinIOne
        , someBuiltin builtinIMin
        , someBuiltin builtinIMax
        , someBuiltin builtinINeg
        , someBuiltin builtinPOr
        , someBuiltin builtinItIsOne
        ]
  reportSDoc "tc.rec.cxt" 30 $ prettyTCM params
  reportSDoc "tc.rec.cxt" 30 $ prettyTCM fsT
  reportSDoc "tc.rec.cxt" 30 $ pretty rect
  if not $ all isJust required then return $ emptyCompKit else do
    transp <- whenDefined [builtinTrans]              (defineKanOperationR DoTransp name params fsT fns rect)
    hcomp  <- whenDefined [builtinTrans,builtinHComp] (defineKanOperationR DoHComp name params fsT fns rect)
    return $ CompKit
      { nameOfTransp = transp
      , nameOfHComp  = hcomp
      }
  where
    whenDefined xs m = do
      xs <- mapM getTerm' xs
      if all isJust xs then m else return Nothing


defineKanOperationR
  :: Command
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM (Maybe QName)
defineKanOperationR cmd name params fsT fns rect = do
  let project = (\ t fn -> t `applyE` [Proj ProjSystem fn])
  stuff <- fmap fst <$> defineKanOperationForFields cmd Nothing project name params fsT fns rect

  caseMaybe stuff (return Nothing) $ \ (theName, gamma, rtype, clause_types, bodies) -> do
  -- phi = 1 clause
  c' <- do
           io <- primIOne
           Just io_name <- getBuiltinName' builtinIOne
           one <- primItIsOne
           tInterval <- primIntervalType
           let
              (ix,rhs) =
                case cmd of
                  -- TranspRArgs = phi : I, a0 : ..
                  -- Γ = Δ^I , CompRArgs
                  -- pats = ... | phi = i1
                  -- body = a0
                  DoTransp -> (1,Var 0 [])
                  -- HCompRArgs = phi : I, u : .., a0 : ..
                  -- Γ = Δ, CompRArgs
                  -- pats = ... | phi = i1
                  -- body = u i1 itIsOne
                  DoHComp  -> (2,Var 1 [] `apply` [argN io, setRelevance irrelevant $ argN one])

              p = ConP (ConHead io_name IsData Inductive [])
                       (noConPatternInfo { conPType = Just (Arg defaultArgInfo tInterval)
                                         , conPFallThrough = True })
                         []

              -- gamma, rtype

              s = singletonS ix p

              pats :: [NamedArg DeBruijnPattern]
              pats = s `applySubst` teleNamedArgs gamma

              t :: Type
              t = s `applyPatSubst` rtype

              gamma' :: Telescope
              gamma' = unflattenTel (ns0 ++ ns1) $ s `applyPatSubst` (g0 ++ g1)
               where
                (g0,_:g1) = splitAt (size gamma - 1 - ix) $ flattenTel gamma
                (ns0,_:ns1) = splitAt (size gamma - 1 - ix) $ teleNames gamma

              c = Clause { clauseFullRange = noRange
                         , clauseLHSRange  = noRange
                         , clauseTel       = gamma'
                         , namedClausePats = pats
                         , clauseBody      = Just $ rhs
                         , clauseType      = Just $ argN t
                         , clauseCatchall    = empty
                         , clauseRecursive   = NotRecursive  -- definitely non-recursive!
                         , clauseUnreachable = Just False
                         , clauseEllipsis    = NoEllipsis
                         , clauseWhereModule = Nothing
                         }
           reportSDoc "trans.rec.face" 17 $ text $ show c
           return c
  cs <- forM (zip3 fns clause_types bodies) $ \ (fname, clause_ty, body) -> do
          let
              pats = teleNamedArgs gamma ++ [defaultNamedArg $ ProjP ProjSystem $ unArg fname]
              c = Clause { clauseFullRange = noRange
                         , clauseLHSRange  = noRange
                         , clauseTel       = gamma
                         , namedClausePats = pats
                         , clauseBody      = Just body
                         , clauseType      = Just $ argN (unDom clause_ty)
                         , clauseCatchall    = empty
                         , clauseRecursive   = MaybeRecursive
                             -- Andreas 2020-02-06 TODO
                             -- Or: NotRecursive;  is it known to be non-recursive?
                         , clauseUnreachable = Just False
                         , clauseEllipsis    = NoEllipsis
                         , clauseWhereModule = Nothing
                         }
          reportSDoc "trans.rec" 17 $ text $ show c
          reportSDoc "trans.rec" 16 $ text "type =" <+> text (show (clauseType c))
          reportSDoc "trans.rec" 15 $ prettyTCM $ abstract gamma (unDom clause_ty)
          reportSDoc "trans.rec" 10 $ text "body =" <+> prettyTCM (abstract gamma body)
          return c
  addClauses theName $ c' : cs
  reportSDoc "trans.rec" 15 $ text $ "compiling clauses for " ++ show theName
  (mst, _, cc) <- inTopContext (compileClauses Nothing cs)
  whenJust mst $ setSplitTree theName
  setCompiledClauses theName cc
  reportSDoc "trans.rec" 15 $ text $ "compiled"
  return $ Just theName

