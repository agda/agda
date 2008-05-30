{-# OPTIONS -cpp #-}

module Agda.TypeChecking.Injectivity where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints
import Agda.Utils.List
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

headSymbol :: Term -> TCM (Maybe TermHead)
headSymbol v = do
  v <- constructorForm v
  case v of
    Def f _ -> do
      def <- theDef <$> getConstInfo f
      case def of
        Datatype{}  -> return (Just $ ConHead f)
        Record{}    -> return (Just $ ConHead f)
        Axiom{}     -> return (Just $ ConHead f)
        _           -> return Nothing
    Con c _ -> return (Just $ ConHead c)
    Sort _  -> return (Just SortHead)
    Pi _ _  -> return (Just PiHead)
    Fun _ _ -> return (Just PiHead)
    Lit _   -> return Nothing -- handle literal heads as well? can't think of
                              -- any examples where it would be useful...
    _       -> return Nothing

checkInjectivity :: QName -> [Clause] -> TCM FunctionInverse
checkInjectivity f cs = do
  reportSLn "tc.inj.check" 40 $ "Checking injectivity of " ++ show f
  es <- concat <$> mapM entry cs
  let (hs, ps) = unzip es
  reportSLn "tc.inj.check" 40 $ "  right hand sides: " ++ show hs
  if all isJust hs && distinct hs
    then do
      let inv = Map.fromList (map fromJust hs `zip` ps)
      reportSLn "tc.inj.check" 20 $ show f ++ " is injective."
      reportSDoc "tc.inj.check" 30 $ nest 2 $ vcat $
        map (\ (h, ps) -> text (show h) <+> text "-->" <+>
                          fsep (punctuate comma $ map (text . show) ps)
            ) $ Map.toList inv
      return $ Inverse inv
    else return NotInjective
  where
    entry (Clause _ _ ps b) = do
      mv <- rhs b
      case mv of
        Nothing -> return []
        Just v  -> do
          h <- headSymbol v
          return [(h, ps)]

    rhs (NoBind b) = rhs b
    rhs (Bind b)   = underAbstraction_ b rhs
    rhs (Body v)   = return $ Just v
    rhs NoBody     = return Nothing

-- | Argument should be on weak head normal form.
functionInverse :: Term -> TCM InvView
functionInverse v = case ignoreBlocking v of
  Def f args -> do
    d <- theDef <$> getConstInfo f
    case d of
      Function{ funInv = inv } -> case inv of
        NotInjective  -> return NoInv
        Inverse m     -> return $ Inv f args m
      _ -> return NoInv
  _ -> return NoInv

data InvView = Inv QName Args (Map TermHead [Arg Pattern])
             | NoInv

useInjectivity :: Type -> Term -> Term -> TCM Constraints
useInjectivity a u v = do
  uinv <- functionInverse u
  vinv <- functionInverse v
  case (uinv, vinv) of
    (Inv f fArgs _, Inv g gArgs _)
      | f == g    -> do
        a <- defType <$> getConstInfo f
        reportSDoc "tc.inj.use" 20 $ vcat
          [ fsep (pwords "comparing application of injective function" ++ [prettyTCM f] ++
                pwords "at")
          , nest 2 $ fsep $ punctuate comma $ map prettyTCM fArgs
          , nest 2 $ fsep $ punctuate comma $ map prettyTCM gArgs
          , nest 2 $ text "and type" <+> prettyTCM a
          ]
        equalArgs a fArgs gArgs
      | otherwise -> fallBack
    (Inv f args inv, NoInv) -> do
      reportSDoc "tc.inj.use" 20 $ fsep $
        pwords "inverting injective function" ++ [prettyTCM f, text "for", prettyTCM v]
      invert inv args =<< headSymbol v
    (NoInv, Inv g args inv) -> do
      reportSDoc "tc.inj.use" 20 $ fsep $
        pwords "inverting injective function" ++ [prettyTCM g, text "for", prettyTCM u]
      invert inv args =<< headSymbol u
    (NoInv, NoInv)          -> fallBack
  where
    fallBack = buildConstraint $ ValueEq a u v

    invert inv args Nothing  = fallBack
    invert inv args (Just h) = case Map.lookup h inv of
      Nothing -> typeError $ UnequalTerms u v a
      Just ps -> instArgs args ps

    instArgs args ps = concat <$> zipWithM instArg args ps
    instArg a p = inst (unArg a) (unArg p)

    inst (MetaV m vs) (ConP c _) = do
      HasType _ mty <- mvJudgement <$> lookupMeta m
      let TelV tel dty = telView mty
      d <- reduce $ unEl dty
      case ignoreBlocking d of
        Def d us -> do
            Datatype{dataPars = np} <- theDef <$> getConstInfo d
            def  <- getConstInfo c
            let cty                       = defType def
                Constructor{conPars = np} = theDef def
                cty'                      = cty `piApply` genericTake np us
            argm <- newArgsMetaCtx cty' tel vs
            -- Compute the type of the instantiation and the orignial type.
            -- We need to make sure they are the same to ensure that index
            -- arguments to the constructor are instantiated.
            let mtyI = cty' `piApply` argm
                mtyO = mty `piApply` vs
            reportSDoc "tc.inj.use" 50 $ text "inversion:" <+> nest 2 (vcat
              [ sep [ prettyTCM (MetaV m vs) <+> text ":="
                    , nest 2 $ prettyTCM (Con c argm)
                    ]
              , text "of type" <+> prettyTCM mtyO
              ] )
            noConstraints $ equalType mtyO mtyI
            noConstraints $ assignV (mty `piApply` vs) m vs (Con c argm)
            equalTerm a u v
          `catchError` \err -> case err of
            TypeError _ _ -> throwError err
            Exception _ _ -> throwError err
            PatternErr _  -> fallBack
            AbortAssign _ -> fallBack

        _ -> fallBack
    inst (Con c vs) (ConP c' ps)
      | c == c'   = instArgs vs ps
      | otherwise = __IMPOSSIBLE__
    inst _ _ = return []

