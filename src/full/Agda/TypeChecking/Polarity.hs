{-# LANGUAGE CPP #-}
module Agda.TypeChecking.Polarity where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Error
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad.Builtin
import Agda.Interaction.Options
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Impossible
import Agda.Utils.Size

#include "../undefined.h"

-- | Get the next polarity from a list, 'Invariant' if empty.
nextPolarity :: [Polarity] -> (Polarity, [Polarity])
nextPolarity []       = (Invariant, [])
nextPolarity (p : ps) = (p, ps)

-- | Replace 'Nonvariant' by 'Invariant'.
purgeNonvariant :: [Polarity] -> [Polarity]
purgeNonvariant = map (\ p -> if p == Nonvariant then Invariant else p)

-- | Main function of this module.
computePolarity :: QName -> TCM ()
computePolarity x = do
  reportSLn "tc.polarity.set" 25 $ "Computing polarity of " ++ show x

  -- get basic polarity from shape of def (arguments matched on or not?)
  def      <- getConstInfo x
  let usagePol = usagePolarity $ theDef def
  reportSLn "tc.polarity.set" 15 $ "Polarity of " ++ show x ++ " from definition form: " ++ show usagePol
  let n = genericLength usagePol  -- n <- getArity x
  reportSLn "tc.polarity.set" 20 $ "  arity = " ++ show n

  -- refine polarity by positivity information
  pol0 <- zipWith (/\) usagePol <$> mapM getPol [0..n - 1]
  reportSLn "tc.polarity.set" 15 $ "Polarity of " ++ show x ++ " from positivity: " ++ show pol0

  -- compute polarity of sized types
  setPolarity x $ pol0 ++ [Covariant] -- Not very nice, but should work
  pol1 <- sizePolarity x

  -- refine polarity again by using type information
  let t = defType def
  reportSDoc "tc.polarity.set" 15 $ text "Refining polarity with type " <+> prettyTCM t
  pol <- dependentPolarity t $ pol0 ++ pol1
  reportSLn "tc.polarity.set" 10 $ "Polarity of " ++ show x ++ ": " ++ show pol

  -- set the polarity in the signature
  setPolarity x $ purgeNonvariant pol -- temporarily disable non-variance
  where
    getPol :: Nat -> TCM Polarity
    getPol i = do
        o <- getArgOccurrence x i
        case o of
          GuardPos -> return Covariant
          Positive -> return Covariant
          Negative -> return Invariant  -- Negative isn't the same as contravariant
          Unused   -> return Nonvariant

{- UNUSED, replaced by usagePolarity
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
-}

-- | Extract a basic approximate polarity info from the shape of definition.
--   Arguments that are matched against get 'Invariant', others 'Nonvariant'.
--   For data types, parameters get 'Nonvariant', indices 'Invariant'.
usagePolarity :: Defn -> [Polarity]
usagePolarity def = case def of
    Axiom{}                                 -> []
    Function{ funClauses = [] }             -> []
    Function{ funClauses = cs }             -> usage $ map clausePats cs
    Datatype{ dataPars = np, dataIxs = ni } -> genericReplicate np Nonvariant
    Record{ recPars = n }                   -> genericReplicate n Nonvariant
    Constructor{}                           -> []
    Primitive{}                             -> []
  where
    usage = foldr1 (zipWith (/\)) . map (map (usagePat . unArg))
    usagePat VarP{} = Nonvariant
    usagePat DotP{} = Nonvariant
    usagePat ConP{} = Invariant
    usagePat LitP{} = Invariant

{- OLD
usagePolarity :: QName -> TCM [Polarity]
usagePolarity x = do
  ci  <- getConstInfo x
  let t = defType ci
  case theDef ci of
    Axiom{}                                 -> return []
    Function{ funClauses = [] }             -> return []
    Function{ funClauses = cs }             -> dependentPolarity t $ usage $ map clausePats cs
    Datatype{ dataPars = np, dataIxs = ni } -> dependentPolarity t $ genericReplicate np Nonvariant
    Record{ recPars = n }                   -> dependentPolarity t $ genericReplicate n Nonvariant
    Constructor{}                           -> return []
    Primitive{}                             -> return []
  where
    usage = foldr1 (zipWith (/\)) . map (map (usagePat . unArg))
    usagePat VarP{} = Nonvariant
    usagePat DotP{} = Nonvariant
    usagePat ConP{} = Invariant
    usagePat LitP{} = Invariant
-}

{-  DOES NOT ACHIEVE INTENDED EFFECT
-- | Compute the basic polarity of a definition according to its type.
--   Dependent arguments are 'Invariant', others are 'Nonvariant'.
typePolarity :: Type -> TCM [Polarity]
typePolarity t = do
      t <- reduce $ unEl t
      case t of
        Pi a b@NoAbs{} -> (Nonvariant :) <$> typePolarity (absBody b)
        Pi a b@Abs{}   -> do
          let c = absBody b
              p = if 0 `freeInIgnoringSortAnn` c then Invariant else Nonvariant
          (p :) <$> typePolarity c
        _              -> return []
-}

-- | Make arguments 'Invariant' if the type of a not-'Nonvariant'
--   later argument depends on it.
dependentPolarity :: Type -> [Polarity] -> TCM [Polarity]
dependentPolarity t []          = return []  -- all remaining are 'Invariant'
dependentPolarity t pols@(p:ps) = do
  t <- reduce $ unEl t
  case t of
    Pi a b -> do
      let c = absBody b
      ps <- dependentPolarity c ps
      p  <- case b of
              Abs{} | p /= Invariant  ->
                ifM (freeInIgnoringNonvariant 0 c ps)
                  (return Invariant)
                  (return p)
              _ -> return p
      return $ p : ps
    _ -> return pols

-- | Check whether a variable is free in a type expression,
--   ignoring domains of non-variant arguments.
freeInIgnoringNonvariant :: Nat -> Type -> [Polarity] -> TCM Bool
freeInIgnoringNonvariant i t []     = return $ i `freeInIgnoringSortAnn` t
freeInIgnoringNonvariant i t (p:ps) = do
  t <- reduce $ unEl t
  case t of
    Pi a b -> if p /= Nonvariant && i `freeInIgnoringSortAnn` a then return True
              else freeInIgnoringNonvariant (i + 1) (absBody b) ps
    _ -> return $ i `freeInIgnoringSortAnn` t

-- | Hack for polarity of size indices.
sizePolarity :: QName -> TCM [Polarity]
sizePolarity d =
  ifM (not . optSizedTypes <$> pragmaOptions) (return []) $ do
  def <- getConstInfo d
  case theDef def of
    Datatype{ dataPars = np, dataCons = cons } -> do
      let TelV tel _      = telView' $ defType def
          (parTel, ixTel) = genericSplitAt np $ telToList tel
      case ixTel of
        []                 -> return []  -- No size index
        Dom _ _ (_, a) : _ -> ifM (not <$> isSizeType a) (return []) $ do
          let check c = do
                t <- defType <$> getConstInfo c
                addCtxTel (telFromList parTel) $ do
--OLD:                  let pars = reverse [ defaultArg $ var i | i <- [0..np - 1] ]
                  let pars = map (defaultArg . var) $ downFrom np
                  TelV conTel target <- telView =<< (t `piApplyM` pars)
                  case conTel of
                    EmptyTel  -> return False  -- no size argument
                    ExtendTel arg  tel ->
                      ifM (not <$> isSizeType (unDom arg)) (return False) $ do -- also no size argument
                        -- First constructor argument has type Size

                        -- check only positive occurences in tel
                        isPos <- underAbstraction arg tel $ \tel -> do
                          pols <- zipWithM polarity [0..] $ map (snd . unDom) $ telToList tel
                          return $ all (`elem` [Nonvariant, Covariant]) pols

                        -- check that the size argument appears in the
                        -- right spot in the target type
                        let sizeArg = size tel
                        isLin <- checkSizeIndex np sizeArg target

                        return $ isPos && isLin

          ifM (andM $ map check cons)
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
    (pars, Arg _ _ ix : ixs) = genericSplitAt np args
checkSizeIndex _ _ _ = __IMPOSSIBLE__

-- | Infimum on the information lattice.
--   'Invariant' is bottom (dominant for inf),
--   'Nonvariant' is top (neutral for inf).
(/\) :: Polarity -> Polarity -> Polarity
Nonvariant /\ b = b
a /\ Nonvariant = a
a /\ b | a == b    = a
       | otherwise = Invariant

-- | 'Polarity' negation, swapping monotone and antitone.
neg :: Polarity -> Polarity
neg Covariant     = Contravariant
neg Contravariant = Covariant
neg Invariant     = Invariant
neg Nonvariant    = Nonvariant

composePol :: Polarity -> Polarity -> Polarity
composePol Nonvariant _    = Nonvariant
composePol _ Nonvariant    = Nonvariant
composePol Invariant _     = Invariant
composePol Covariant x     = x
composePol Contravariant x = neg x

-- | @polarities i a@ computes the list of polarities of de Bruijn index @i@
--   in syntactic entity @a@.
class HasPolarity a where
  polarities :: Nat -> a -> TCM [Polarity]

-- | @polarity i a@ computes the polarity of de Bruijn index @i@
--   in syntactic entity @a@ by taking the infimum of all 'polarities'.
polarity :: HasPolarity a => Nat -> a -> TCM Polarity
polarity i x = do
  ps <- polarities i x
  case ps of
    [] -> return Nonvariant
    ps -> return $ foldr1 (/\) ps

instance HasPolarity a => HasPolarity (Arg a) where
  polarities i = polarities i . unArg

instance HasPolarity a => HasPolarity (Dom a) where
  polarities i = polarities i . unDom

instance HasPolarity a => HasPolarity (Abs a) where
  polarities i (Abs   _ b) = polarities (i + 1) b
  polarities i (NoAbs _ v) = polarities i v

instance HasPolarity a => HasPolarity [a] where
  polarities i xs = concat <$> mapM (polarities i) xs

instance (HasPolarity a, HasPolarity b) => HasPolarity (a, b) where
  polarities i (x, y) = (++) <$> polarities i x <*> polarities i y

instance HasPolarity Type where
  polarities i (El _ v) = polarities i v

instance HasPolarity Term where
  polarities i v = case v of
    -- Andreas, 2012-09-06: taking the polarities of the arguments
    -- without taking the variance of the function into account seems wrong.
    Var n ts  | n == i -> (Covariant :) . map (const Invariant) <$> polarities i ts
              | otherwise -> map (const Invariant) <$> polarities i ts
    Lam _ t    -> polarities i t
    Lit _      -> return []
    Level l    -> polarities i l
    Def x ts   -> do
      pols <- getPolarity x
      let compose p ps = map (composePol p) ps
      concat . zipWith compose (pols ++ repeat Invariant) <$> mapM (polarities i) ts
    Con _ ts   -> polarities i ts -- constructors can be seen as monotone in all args.
    Pi a b     -> (++) <$> (map neg <$> polarities i a) <*> polarities i b
    Sort s     -> return [] -- polarities i s -- return []
    MetaV _ ts -> map (const Invariant) <$> polarities i ts
    DontCare t -> polarities i t -- return []

instance HasPolarity Level where
  polarities i (Max as) = polarities i as

instance HasPolarity PlusLevel where
  polarities i ClosedLevel{} = return []
  polarities i (Plus _ l) = polarities i l

instance HasPolarity LevelAtom where
  polarities i l = case l of
    MetaLevel _ vs   -> map (const Invariant) <$> polarities i vs
    BlockedLevel _ v -> polarities i v
    NeutralLevel v   -> polarities i v
    UnreducedLevel v -> polarities i v
