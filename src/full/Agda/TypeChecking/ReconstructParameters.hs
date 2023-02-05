
-- | Reconstruct dropped parameters from constructors.  Used by
--   with-abstraction to avoid ill-typed abstractions (#745). Note that the
--   term is invalid after parameter reconstruction. Parameters need to be
--   dropped again before using it.

module Agda.TypeChecking.ReconstructParameters where

import Data.Functor ( ($>) )
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
  reportSDoc "tc.reconstruct" 30 $
    sep [ "reconstructing parameters in"
        , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM a ] ]
  v <- checkInternal' (reconstructAction' act) v CmpLeq a

  reportSDoc "tc.reconstruct" 30 $
    nest 2 $ "-->" <+> prettyTCM v
  return v

reconstructAction :: Action TCM
reconstructAction = reconstructAction' defaultAction

reconstructAction' :: Action TCM -> Action TCM
reconstructAction' act = act{ postAction = \ty tm -> postAction act ty tm >>= reconstruct ty }

reconstruct :: Type -> Term -> TCM Term
reconstruct ty v = do
    reportSDoc "tc.reconstruct" 30 $
      sep [ "reconstructing in"
      , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM ty ] ]
    case v of
      Con h ci vs -> do
        hh <- fromRight __IMPOSSIBLE__ <$> getConHead (conName h)
        TelV tel dataTy <- telView ty
        reportSDoc "tc.reconstruct" 50 $
          sep [ "reconstructing"
              , nest 2 $ sep [ prettyTCM v <+> ":"
                             , nest 2 $ prettyTCM dataTy ] ]
        pars <- addContext tel $ extractParameters (conName h) dataTy
        -- If the constructor is underapplied, we need to escape from the telescope.
        let escape = applySubst $ strengthenS __IMPOSSIBLE__ $ size tel
        return $ Con hh ci $ map Apply (escape pars) ++ vs
      Def f es -> projView v >>= \case
        ProjectionView _f a es -> do
          recTy <- infer =<< dropParameters (unArg a)
          pars <- extractParameters f recTy
          loop ty (Def f . (map Apply pars ++) . (Apply a:)) es
        LoneProjectionLike _f i -> reduce (unEl ty) >>= \case
          Pi recTy _ -> do
            pars <- extractParameters f (unDom recTy)
            return $ Def f $ map Apply pars
          _ -> __IMPOSSIBLE__
        NoProjection{} -> do
          ty <- defType <$> getConstInfo f
          loop ty (Def f) es
      Var i es -> do
        ty <- typeOfBV i
        loop ty (Var i) es
      MetaV m es -> do
        ty <- getMetaType m
        loop ty (MetaV m) es
      _ -> return v

  where
    -- @loop ty f vs@ where @ty@ is the type of @f []@ and vs are valid
    -- arguments to something of type @ty@
    loop :: Type -> (Elims -> Term) -> Elims -> TCM Term
    loop ty f []           = do
      reportSDoc "tc.reconstruct" 50 $ "Loop ended" <+> pretty (f [])
      return $ f []
    loop ty f (Apply u:es) = do
      reportSDoc "tc.reconstruct" 50 $ "The type before app is:" <+> pretty ty
      reportSDoc "tc.reconstruct" 50 $ "The term before app is:" <+> prettyTCM (f [])
      uu <- dropParameters u
      reportSDoc "tc.reconstruct" 50 $ "The app is:" <+> pretty uu
      ty' <- piApplyM ty uu
      reportSDoc "tc.reconstruct" 50 $ "The type after app is:" <+> pretty ty'
      loop ty' (f . (Apply u :)) es
    loop ty f (Proj o p:es) = do
      reportSDoc "tc.reconstruct" 50 $ "The type is:" <+> pretty ty
      reportSDoc "tc.reconstruct" 50 $ "The term is:" <+> pretty (f [])
      reportSDoc "tc.reconstruct" 50 $ "The proj is:" <+> prettyTCM p
      pars <- extractParameters p ty
      ~(Just (El _ (Pi _ b))) <- getDefType p =<< reduce ty
      let fTm = f []
      fe <- dropParameters fTm
      loop (absApp b fe) (Def p . (map Apply pars ++) . (Apply (defaultArg fTm) :)) es
    loop ty _ (IApply {}:vs) = __IMPOSSIBLE__

-- Extract the parameters from the type of a constructor
-- application or the type of the principal argument of a
-- projection.
extractParameters :: QName -> Type -> TCM Args
extractParameters q ty = reduce (unEl ty) >>= \case
  Def d prePs -> do
    dt <- defType <$> getConstInfo d
    reportSDoc "tc.reconstruct" 50 $ "Start traversing parameters: " <+> pretty prePs
    postPs <- checkInternal' reconstructAction prePs CmpEq (dt , Def d)
    reportSDoc "tc.reconstruct" 50 $ "Traversed parameters:" <+> pretty postPs
    info <- getConstInfo q
    let mkParam erasure =
            (if erasure then applyQuantity zeroQuantity else id)
          . hideAndRelParams
          . isApplyElim' __IMPOSSIBLE__
    if -- Case: data or record constructor
       | Constructor{ conPars = n, conErasure = e } <- theDef info ->
           return $ map (mkParam e) $ take n postPs
       -- Case: regular projection
       | isProperProjection (theDef info) ->
         case theDef info of
           Function{ funErasure = e } ->
             return $ map (mkParam e) postPs
           _ -> __IMPOSSIBLE__
       -- Case: projection-like function
       | otherwise -> do
           TelV tel _ <- telViewUpTo (size postPs) $ defType info
           return $ zipWith ($>) (teleArgs tel :: Args) $ map (unArg . isApplyElim' __IMPOSSIBLE__) postPs
  _ -> __IMPOSSIBLE__

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
