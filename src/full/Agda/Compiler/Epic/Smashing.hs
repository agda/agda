{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

-- | Smash functions which return something that can be inferred
--   (something of a type with only one element)

module Agda.Compiler.Epic.Smashing where

import Control.Monad.State

import Data.List
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal as SI
import Agda.TypeChecking.Monad hiding (funInline)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

import Agda.Compiler.Epic.AuxAST as AA
import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface

import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HM

#include "undefined.h"
import Agda.Utils.Impossible

defnPars :: Integral n => Defn -> n
defnPars (Record      {recPars = p}) = fromIntegral p
defnPars (Constructor {conPars = p}) = fromIntegral p
defnPars d                           = 0

-- | Main function, smash as much as possible
smash'em :: [Fun] -> Compile TCM [Fun]
smash'em funs = do
    defs <- lift $ use $ stImports . sigDefinitions
    funs' <- forM funs $ \f -> case f of
      AA.Fun{} -> case funQName f >>= flip HM.lookup defs of
          Nothing -> do
              lift $ reportSDoc "epic.smashing" 10 $ vcat
                [ (text . show) f <+> text " was not found"]
              return f

          Just def -> do
              lift $ reportSLn "epic.smashing" 10 $ "running on:" ++ (show (funQName f))
              minfered <- smashable (length (funArgs f) + defnPars (theDef def)) (defType def)
              case minfered of
                  Just infered -> do
                      lift $ reportSDoc "smashing" 5 $ vcat
                        [ prettyTCM (defName def) <+> text "is smashable"]
                      return f { funExpr = infered
                               , funInline = True
                               , funComment = funComment f ++ " [SMASHED]"
                               }
                  Nothing -> return f
      _ -> do
        lift $ reportSLn "epic.smashing" 10 $ "smashing!"
        return f
    return funs'

(+++) :: Telescope -> Telescope -> Telescope
xs +++ ys = unflattenTel names $ map (raise (size ys)) (flattenTel xs) ++ flattenTel ys
  where names = teleNames xs ++ teleNames ys

-- | Can a datatype be inferred? If so, return the only possible value.
inferable :: Set QName -> QName -> [Arg Term] ->  Compile TCM (Maybe Expr)
inferable visited dat args | dat `Set.member` visited = return Nothing
inferable visited dat args = do
  lift $ reportSLn "epic.smashing" 10 $ "  inferring:" ++ (show dat)
  defs <- lift $ use $ stImports . sigDefinitions
  let def = fromMaybe __IMPOSSIBLE__ $ HM.lookup dat defs
  case theDef def of
      d@Datatype{} -> do
          case dataCons d of
            [c] -> inferableArgs c (dataPars d)
            _   -> return Nothing
      r@Record{}   -> inferableArgs (recCon r) (recPars r)
      f@Function{} -> do
        term <- lift $ normalise $ Def dat $ map SI.Apply args
        inferableTerm visited' term
      d -> do
        lift $ reportSLn "epic.smashing" 10 $ "  failed (inferable): " ++ (show d)
        return Nothing
  where
    inferableArgs c pars = do
        defs <- lift $ use $ stImports . sigDefinitions
        let def = fromMaybe __IMPOSSIBLE__ $ HM.lookup c defs
        forc <- getForcedArgs c
        TelV tel _ <- lift $ telView (defType def `piApply` genericTake pars args)
        tag <- getConstrTag c
        lift $ reportSDoc "epic.smashing" 10 $ nest 2 $ vcat
          [ text "inferableArgs!"
          , text "tele" <+> prettyTCM tel
          , text "constr:" <+> prettyTCM c
          ]
        (AA.Con tag c <$>) <$> sequence <$> forM (notForced forc $ flattenTel tel) (inferableTerm visited' . unEl . unDom)
    visited' = Set.insert dat visited

inferableTerm :: Set QName -> Term -> Compile TCM (Maybe Expr)
inferableTerm visited t = do
  case ignoreSharing t of
    Def q es    ->
      case allApplyElims es of
        Just vs -> inferable visited q vs
        Nothing -> return Nothing
    Pi _   b    -> (AA.Lam "_" <$>) <$> inferableTerm visited (unEl $ unAbs b)
    Sort {}     -> return . return $ AA.UNIT
    t           -> do
      lift $ reportSLn "epic.smashing" 10 $ "  failed to infer: " ++ show t
      return Nothing

-- | Find the only possible value for a certain type. If we fail return Nothing
smashable :: Int -> Type -> Compile TCM (Maybe Expr)
smashable origArity typ = do
    defs <- lift $ use $ stImports . sigDefinitions
    TelV tele retType <- lift $ telView typ
    retType' <- return retType -- lift $ reduce retType

    inf <- inferableTerm Set.empty (unEl retType')
    lift $ reportSDoc "epic.smashing" 10 $ nest 2 $ vcat
      [ text "Result is"
      , text "inf: " <+> (text . show) inf
      , text "type: " <+> prettyTCM retType'
      ]
    return $ buildLambda (size tele - origArity) <$> inf

buildLambda :: (Ord n, Num n) => n -> Expr -> Expr
buildLambda n e | n <= 0    = e
buildLambda n e | otherwise = AA.Lam "_" (buildLambda (n - 1) e)
