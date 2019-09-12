
-- | Reconstruct dropped parameters from constructors.  Used by
--   with-abstraction to avoid ill-typed abstractions (#745). Note that the
--   term is invalid after parameter reconstruction. Parameters need to be
--   dropped again before using it.

module Agda.TypeChecking.ReconstructParameters where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty

import Agda.Utils.Size

import Agda.Utils.Impossible

reconstructParametersInType :: Type -> TCM Type
reconstructParametersInType a =
  traverse (reconstructParameters (sort $ getSort a)) a

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

reconstructParameters :: Type -> Term -> TCM Term
reconstructParameters a v = do
  reportSDoc "tc.with.reconstruct" 30 $
    sep [ "reconstructing parameters in"
        , nest 2 $ sep [ prettyTCM v <+> ":", nest 2 $ prettyTCM a ] ]
  v <- checkInternal' (defaultAction{ postAction = reconstruct }) v CmpLeq a
  reportSDoc "tc.with.reconstruct" 30 $
    nest 2 $ "-->" <+> prettyTCM v
  return v
  where
    reconstruct a v = do
      case v of
        Con h ci vs -> do
          TelV tel a <- telView a
          let under = size tel  -- under-applied when under > 0
          reportSDoc "tc.with.reconstruct" 50 $
            sep [ "reconstructing"
                , nest 2 $ sep [ prettyTCM v <+> ":"
                               , nest 2 $ prettyTCM a ] ]
          case (unEl a) of
            Def d es -> do
              Just n <- defParameters <$> getConstInfo d
              let ps = applySubst (strengthenS __IMPOSSIBLE__ under) . take n $ es
              reportSLn "tc.with.reconstruct" 50 $ show n ++ " parameters"
              -- TODO: the reconstructed parameters are not reconstructed recursively!
              return $ Con h ci (ps ++ vs)
            _ -> __IMPOSSIBLE__
        _        -> return v

dropParameters :: TermLike a => a -> TCM a
dropParameters = traverseTermM dropPars
  where
    dropPars v =
      case v of
        Con c ci vs -> do
          Constructor{ conData = d } <- theDef <$> getConstInfo (conName c)
          Just n <- defParameters <$> getConstInfo d
          return $ Con c ci $ drop n vs
        _        -> return v
