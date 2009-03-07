{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Polarity where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Error
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad.Builtin
import Agda.Interaction.Options
import Agda.Utils.Monad
import Agda.Utils.Impossible
import Agda.Utils.Size

#include "../undefined.h"

getArity :: QName -> TCM Arity
getArity x = do
  def <- theDef <$> getConstInfo x
  case def of
    Axiom{}                                 -> return 0
    Function{ funClauses = c : _ }          -> return $ genericLength (clausePats c)
    Function{ funClauses = [] }             -> return 0
    Datatype{ dataPars = np, dataIxs = ni } -> return np
    Record{ recPars = n }                   -> return n
    Constructor{}                           -> return 0
    Primitive{}                             -> return 0

computePolarity :: QName -> TCM ()
computePolarity x = do
  reportSLn "tc.polarity.set" 15 $ "Computing polarity of " ++ show x
  n <- getArity x
  reportSLn "tc.polarity.set" 20 $ "  arity = " ++ show n
  pol0 <- mapM getPol [0..n - 1]

  -- Not very nice, but should work
  setPolarity x $ pol0 ++ [Covariant]
  pol1 <- sizePolarity x

  let pol = pol0 ++ pol1
  reportSLn "tc.polarity.set" 10 $ "Polarity of " ++ show x ++ ": " ++ show pol
  setPolarity x pol
  where
    getPol :: Nat -> TCM Polarity
    getPol i = do
        o <- getArgOccurrence x i
        case o of
          Positive -> return Covariant
          Negative -> return Invariant  -- Negative isn't the same as contravariant
          Unused   -> return Invariant  -- add NonVariant?

-- | Hack for polarity of size indices.
sizePolarity :: QName -> TCM [Polarity]
sizePolarity d =
  ifM (not . optSizedTypes <$> commandLineOptions) (return []) $ do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = np, dataCons = cons } -> do
      let TelV tel _      = telView $ defType def
          (parTel, ixTel) = genericSplitAt np $ telToList tel
      case ixTel of
        []                -> return []  -- No size index
        Arg _ (_, a) : _  -> ifM (not <$> isSizeType a) (return []) $ do
          let check c = do
                t <- normalise =<< defType <$> getConstInfo c
                addCtxTel (telFromList parTel) $ do
                  let pars = reverse [ Arg NotHidden $ Var i [] | i <- [0..np - 1] ]
                      TelV conTel target = telView $ t `piApply` pars
                  case conTel of
                    EmptyTel  -> return False  -- no size argument
                    ExtendTel arg@(Arg _ a) tel ->
                      ifM (not <$> isSizeType a) (return False) $ do -- also no size argument
                        -- First constructor argument has type Size

                        -- check only positive occurences in tel
                        isPos <- underAbstraction arg tel $ \tel -> do
                          pols <- zipWithM polarity [0..] $ map (snd . unArg) $ telToList tel
                          return $ all (== Covariant) pols

                        -- check that the size argument appears in the
                        -- right spot in the target type
                        let sizeArg = size tel
                        isLin <- checkSizeIndex np sizeArg target

                        return $ isPos && isLin
                      
          ifM (and <$> mapM check cons)
              (return [Covariant])
              (return [Invariant])
    _ -> return []

checkSizeIndex :: Nat -> Nat -> Type -> TCM Bool
checkSizeIndex np i (El _ (Def _ args)) = do
  let excl = not $ freeIn i (pars ++ ixs)
  s <- sizeView ix
  case s of
    SizeSuc (Var j []) -> return $ and [ excl, i == j ]
    _                  -> return False
  where
    (pars, Arg _ ix : ixs) = genericSplitAt np args
checkSizeIndex _ _ _ = __IMPOSSIBLE__

(/\) :: Polarity -> Polarity -> Polarity
a /\ b | a == b    = a
       | otherwise = Invariant

neg :: Polarity -> Polarity
neg Covariant     = Contravariant
neg Contravariant = Covariant
neg Invariant     = Invariant

composePol :: Polarity -> Polarity -> Polarity
composePol Invariant _     = Invariant
composePol Covariant x     = x
composePol Contravariant x = neg x

class HasPolarity a where
  polarities :: Nat -> a -> TCM [Polarity]

polarity :: HasPolarity a => Nat -> a -> TCM Polarity
polarity i x = do
  ps <- polarities i x
  case ps of
    [] -> return Covariant
    ps -> return $ foldr1 (/\) ps

instance HasPolarity a => HasPolarity (Arg a) where
  polarities i = polarities i . unArg

instance HasPolarity a => HasPolarity (Abs a) where
  polarities i = polarities (i + 1) . absBody

instance HasPolarity a => HasPolarity [a] where
  polarities i xs = concat <$> mapM (polarities i) xs

instance (HasPolarity a, HasPolarity b) => HasPolarity (a, b) where
  polarities i (x, y) = (++) <$> polarities i x <*> polarities i y

instance HasPolarity Type where
  polarities i (El _ v) = polarities i v

instance HasPolarity Term where
  polarities i v = case v of
    Var n ts  | n == i -> (Covariant :) <$> polarities i ts
              | otherwise -> polarities i ts
    Lam _ t    -> polarities i t
    Lit _      -> return []
    Def x ts   -> do
      pols <- getPolarity (force x)
      let compose p ps = map (composePol p) ps
      concat . zipWith compose (pols ++ repeat Invariant) <$> mapM (polarities i) ts
    Con _ ts   -> polarities i ts
    Pi a b     -> (++) <$> (map neg <$> polarities i a) <*> polarities i b
    Fun a b    -> (++) <$> (map neg <$> polarities i a) <*> polarities i b
    Sort _     -> return []
    MetaV _ ts -> map (const Invariant) <$> polarities i ts

