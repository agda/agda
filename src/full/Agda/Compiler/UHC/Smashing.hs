

{-# LANGUAGE CPP #-}

-- DISABLED - NOT USED ANYMORE

-- | Smash functions which return something that can be inferred
--   (something of a type with only one element)

module Agda.Compiler.UHC.Smashing where

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal as SI
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

--import Agda.Compiler.UHC.AuxAST as AA
--import Agda.Compiler.UHC.Transform
--import Agda.Compiler.UHC.Naming

import Agda.Utils.Lens

#if __GLASGOW_HASKELL__ <= 708
import Agda.Utils.Monad
#endif

import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HM

#include "undefined.h"
import Agda.Utils.Impossible

{-
type SmashT m = FreshNameT (TransformT m)

defnPars :: Integral n => Defn -> n
defnPars (Record      {recPars = p}) = fromIntegral p
defnPars (Constructor {conPars = p}) = fromIntegral p
defnPars _                           = 0

smash'em :: Transform
smash'em amod = do
  fs' <- smashFuns (xmodFunDefs amod)
  return $ (amod { xmodFunDefs = fs' })

-- | Main function, smash as much as possible
smashFuns :: [Fun] -> TransformT TCM [Fun]
smashFuns funs = do
    defs <- (sigDefinitions <$> use stImports)
    funs' <- evalFreshNameT "nl.uu.agda.smashing" $ forM funs $ \f -> case f of
      AA.Fun{} -> case xfunQName f >>= flip HM.lookup defs of

          Just (def@(Defn {theDef = (Function { funSmashable = True })})) -> do
              reportSLn "uhc.smashing" 10 $ "running on:" ++ (show (xfunQName f))
              minfered <- runMaybeT $ smashable (length (xfunArgs f) + defnPars (theDef def)) (defType def)
              case minfered of
                  Just infered -> do
                      reportSDoc "smashing" 5 $ vcat
                        [ prettyTCM (defName def) <+> text "is smashable"]
                      return f { xfunExpr = infered
                               , xfunInline = True
                               , xfunComment = xfunComment f ++ " [SMASHED]"
                               }
                  Nothing -> return f
          _ -> do
              reportSDoc "uhc.smashing" 10 $ vcat
                [ (text . show) f <+> text " was not found or is not eligible for smashing."]
              return f
      _ -> do
        reportSLn "uhc.smashing" 10 $ "smashing!"
        return f
    return funs'

fail' :: Monad m => MaybeT m a
fail' = fail ""

(+++) :: Telescope -> Telescope -> Telescope
xs +++ ys = unflattenTel names $ map (raise (size ys)) (flattenTel xs) ++ flattenTel ys
  where names = teleNames xs ++ teleNames ys

-- | Can a datatype be inferred? If so, return the only possible value.
inferable :: Set QName -> QName -> [SI.Arg Term] ->  MaybeT (SmashT TCM) Expr
inferable visited dat _    | dat `Set.member` visited = fail'
inferable visited dat args = do
  reportSLn "uhc.smashing" 10 $ "  inferring:" ++ (show dat)
  defs <- sigDefinitions <$> use stImports
  let def = fromMaybe __IMPOSSIBLE__ $ HM.lookup dat defs
  case theDef def of
      d@Datatype{} -> do
          case dataCons d of
            [c] -> inferableArgs c (dataPars d)
            _   -> fail'
      r@Record{}   -> inferableArgs (recCon r) (recPars r)
      (Function{ funSmashable = True }) -> do
        term <- liftTCM $ normalise $ Def dat $ map SI.Apply args
        inferableTerm visited' term
      d -> do
        reportSLn "uhc.smashing" 10 $ "  failed (inferable): " ++ (show d)
        fail'
  where
    inferableArgs :: QName -> Nat -> MaybeT (SmashT TCM) Expr
    inferableArgs c pars = do
        reportSLn "uhc.smashing" 10 $ "  inferring args for: " ++ show c
        defs <- sigDefinitions <$> use stImports
        let def = fromMaybe __IMPOSSIBLE__ $ HM.lookup c defs
        TelV tel _ <- liftTCM $ telView (defType def `apply` genericTake pars args)
        reportSDoc "uhc.smashing" 10 $ nest 2 $ vcat
          [ text "inferableArgs!"
          , text "tele" <+> prettyTCM tel
          , text "constr:" <+> prettyTCM c
          ]
        conFun <- lift $ lift $ getConstrFun c
        (apps1 conFun <$>) $ forM (flattenTel tel) (inferableTerm visited' . unEl . unDom)
    visited' = Set.insert dat visited

inferableTerm :: Set QName -> Term -> MaybeT (SmashT TCM) Expr
inferableTerm visited t = do
  case ignoreSharing t of
    Def q es    ->
      case allApplyElims es of
        Just vs -> inferable visited q vs
        Nothing -> fail'
    Pi _   b    -> do
        t' <- inferableTerm visited (unEl $ unAbs b)
        lift $ buildLambda 1 t'
    Sort {}     -> return AA.UNIT
    t'          -> do
      reportSLn "uhc.smashing" 10 $ "  failed to infer: " ++ show t'
      fail'

-- | Find the only possible value for a certain type. If we fail return Nothing
smashable :: Int -> Type -> MaybeT (SmashT TCM) Expr
smashable origArity typ = do
    TelV tele retType <- liftTCM $ telView typ
    retType' <- return retType

    inf <- inferableTerm Set.empty (unEl retType')
    reportSDoc "uhc.smashing" 10 $ nest 2 $ vcat
      [ text "Result is"
      , text "inf: " <+> (text . show) inf
      , text "type: " <+> prettyTCM retType'
      ]
    lift $ buildLambda (size tele - origArity) inf

buildLambda :: Int -> Expr -> SmashT TCM Expr
buildLambda n e | n <= 0    = return e
buildLambda n e | otherwise = do
  v <- freshLocalName
  e' <- buildLambda (n - 1) e
  return $ AA.Lam v e'

-}
