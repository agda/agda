
-- | Reconstruct dropped parameters from constructors.  Used by
--   with-abstraction to avoid ill-typed abstractions (#745). Note that the
--   term is invalid after parameter reconstruction. Parameters need to be
--   dropped again before using it.

module Agda.TypeChecking.ReconstructParameters where

import Data.Maybe
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Datatypes

import Agda.Utils.Size
import Agda.Utils.Either
import Agda.Utils.Function (applyWhen)

import Agda.Utils.Impossible

reconstructParametersInType :: Type -> TCM Type
reconstructParametersInType = reconstructParametersInType' defaultAction

reconstructParametersInType' :: Action TCM -> Type -> TCM Type
reconstructParametersInType' act a =
  traverse (reconstructParameters' act (sort $ getSort a)) a

reconstructParametersInTel :: Telescope -> TCM Telescope
reconstructParametersInTel EmptyTel = return EmptyTel
reconstructParametersInTel (ExtendTel a tel) = do
  ar <- reconstructParametersInType (unDom a)
  addContext (absName tel, a) $
    ExtendTel (ar <$ a) <$> traverse reconstructParametersInTel tel

reconstructParametersInEqView :: EqualityView -> TCM EqualityView
reconstructParametersInEqView (EqualityType s eq l a u v) =
  EqualityType s eq l <$> traverse (reconstructParameters $ sort s) a
                      <*> traverse (reconstructParameters $ El s $ unArg a) u
                      <*> traverse (reconstructParameters $ El s $ unArg a) v
reconstructParametersInEqView (OtherType a) = OtherType <$> reconstructParametersInType a
reconstructParametersInEqView (IdiomType a) = IdiomType <$> reconstructParametersInType a

reconstructParameters :: Type -> Term -> TCM Term
reconstructParameters = reconstructParameters' defaultAction

reconstructParameters' :: Action TCM -> Type -> Term -> TCM Term
reconstructParameters' act a v = do
  reportSDoc "tc.with.reconstruct" 30 $
    sep [ "reconstructing parameters in"
        , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM a ] ]
  v <- checkInternal' reconstructAction v CmpLeq a

  reportSDoc "tc.with.reconstruct" 30 $
    nest 2 $ "-->" <+> prettyTCM v
  return v
  where
    reconstructAction = defaultAction{ postAction = reconstruct }

    reconstruct a v = do
      reportSDoc "tc.with.reconstruct" 30 $
        sep [ "reconstructing in"
        , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM a ] ]
      case unSpine v of
        Con h ci vs -> do
          hh <- fromRight __IMPOSSIBLE__ <$> getConHead (conName h)
          TelV tel a <- telView a
          let under = size tel  -- under-applied when under > 0
          reportSDoc "tc.reconstruct" 50 $
            sep [ "reconstructing"
                , nest 2 $ sep [ prettyTCM v <+> ":"
                               , nest 2 $ prettyTCM a ] ]
          case (unEl a) of
            Def d es -> do
              Just n <- defParameters <$> getConstInfo d
              let prePs = applySubst (strengthenS impossible under) . take n $ es
              let hiddenPs = map (Apply .
                                  -- The parameters are erased in the
                                  -- type of a constructor.
                                  applyQuantity zeroQuantity .
                                  hideAndRelParams) $
                             fromMaybe __IMPOSSIBLE__ $
                             allApplyElims prePs
              reportSDoc "tc.reconstruct" 50 $ "The hiddenPs are" <+> pretty hiddenPs
              tyCon <- defType <$> getConstInfo (conName hh)
              reportSDoc "tc.reconstruct" 50 $ "Here we start infering spine"
              ((_,Con hh ci psAfterAct),_) <- inferSpine' act tyCon (Con hh ci []) (Con hh ci []) hiddenPs
              ((_,conWithPars),_) <- inferSpine' reconstructAction tyCon (Con hh ci []) (Con hh ci []) psAfterAct
              reportSDoc "tc.reconstruct" 50 $ "The spine has been inferred:" <+> pretty conWithPars
              return $ applyWithoutReversing conWithPars vs
            _ -> __IMPOSSIBLE__
        _  -> do
          vv <- elimView EvenLone v
          unSpineAndReconstruct a vv
    unSpineAndReconstruct :: Type -> Term -> TCM Term
    unSpineAndReconstruct a v =
      case v of
        Var i vs -> do
          ty <- typeOfBV i
          ctx <- getContextTelescope
          reportSDoc "tc.reconstruct" 50 $ (text ("Var case "++(show i)++" with context")) <+> prettyTCM ctx
          loop ty (Var i) vs
        Def nam vs -> do
          reportSDoc "tc.reconstruct" 50 $ "Def case"
          ty <- defType <$> getConstInfo nam
          loop ty (Def nam) vs
        MetaV id vs -> do
          reportSDoc "tc.reconstruct" 50 $ "MetaVar case"
          ty <- getMetaType id
          loop ty (MetaV id) vs
        _ -> do
          reportSDoc "tc.reconstruct" 50 $ "Another case" <+> pretty v
          return v
    -- @loop ty f vs@ where @ty@ is the type of @f []@ and vs are valid
    -- arguments to something of type @ty@
    loop :: Type -> (Elims -> Term) -> Elims -> TCM Term
    loop ty f = loop' ty f f
    -- We duplicate @f@ because we don't want the parameters to be reconstructed in
    -- type, since it would cause type-checking error when running @checkInternal'@.
    -- The first one @fTe@ is for term, the other one @fTy@ for type.
    loop' ty fTe _   []           = do
      reportSDoc "tc.reconstruct" 50 $ "Loop ended" <+> (pretty $ fTe [])
      return $ fTe []
    loop' ty fTe fTy (Apply u:es) = do
      reportSDoc "tc.reconstruct" 50 $ "The type before app is:" <+> pretty ty
      reportSDoc "tc.reconstruct" 50 $ "The term before app is:" <+> prettyTCM (fTe [])
      uu <- dropParameters u
      reportSDoc "tc.reconstruct" 50 $ "The app is:" <+> pretty uu
      ty' <- piApplyM ty uu
      reportSDoc "tc.reconstruct" 50 $ "The type after app is:" <+> pretty ty'
      loop' ty' (fTe . (Apply u :)) (fTy . (Apply uu :)) es
    loop' ty fTe fTy (Proj o p:es) = do
      reportSDoc "tc.reconstruct" 50 $ "The type is:" <+> pretty ty
      reportSDoc "tc.reconstruct" 50 $ "The term is:" <+> pretty (fTe [])
      reportSDoc "tc.reconstruct" 50 $ "The proj is:" <+> prettyTCM p
      ty' <- reduce ty
      case unEl ty' of
        Def r pars -> do
          ~(Just (El _ (Pi _ b))) <- getDefType p ty'
          tyProj <- defType <$> getConstInfo p
          let reconstructWithoutPostFixing = reconstructAction { elimViewAction = elimView NoPostfix }
          let hiddenPs = map (Apply .
                              -- The parameters are erased in the
                              -- type of a projection.
                              applyQuantity zeroQuantity) $
                         mapHide tyProj $
                         fromMaybe __IMPOSSIBLE__ $
                         allApplyElims pars
          reportSDoc "tc.reconstruct" 50 $ "The params are" <+> pretty hiddenPs
          ((_,Def p psAfterAct),_) <- inferSpine' act tyProj (Def p []) (Def p []) hiddenPs
          ((_,projWithPars),_) <- inferSpine' reconstructWithoutPostFixing tyProj (Def p []) (Def p []) psAfterAct
          reportSDoc "tc.reconstruct" 50 $ "Spine infered" <+> pretty projWithPars
          let fTe' x = applyWithoutReversing projWithPars ((Apply $ defaultArg $ fTe []):x)
          loop' (absApp b (fTy [])) fTe' (fTy . (Proj o p:)) es
        _ -> __IMPOSSIBLE__
    loop' ty _   _   (IApply {}:vs) = __IMPOSSIBLE__

    applyWithoutReversing :: Term -> Elims -> Term
    applyWithoutReversing (Var i es)   ess = Var i (es++ess)
    applyWithoutReversing (Def n es)   ess = Def n (es++ess)
    applyWithoutReversing (Con h i es) ess = Con h i (es++ess)
    applyWithoutReversing (MetaV i es) ess = MetaV i (es++ess)
    applyWithoutReversing (Dummy s es) ess = Dummy s (es++ess)
    applyWithoutReversing _            _   = __IMPOSSIBLE__

    mapHide (El _ (Pi a b)) (p:tl) =
      applyWhen (getHiding a == Hidden) hideAndRelParams p : mapHide (unAbs b) tl
    mapHide t l = l

dropParameters :: TermLike a => a -> TCM a
dropParameters = traverseTermM $
    \case
        Con c ci vs -> do
          Constructor{ conData = d } <- theDef <$> getConstInfo (conName c)
          Just n <- defParameters <$> getConstInfo d
          return $ Con c ci $ drop n vs
        v@(Def f vs) -> do
          isRelevantProjection f >>= \case
            Nothing -> return v
            Just pr -> return $ applyE (projDropPars pr ProjSystem) vs
        v -> return v
