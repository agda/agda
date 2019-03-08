{-# LANGUAGE CPP               #-}

module Agda.TypeChecking.Polarity where

import Control.Monad.State

import Data.Maybe
import Data.Traversable (traverse)

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Free hiding (Occurrence(..))
import Agda.TypeChecking.Positivity.Occurrence

import Agda.Interaction.Options

import Agda.Utils.List
import Agda.Utils.Maybe ( whenNothingM )
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- * Polarity lattice.
------------------------------------------------------------------------

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

-- | What is the polarity of a function composition?
composePol :: Polarity -> Polarity -> Polarity
composePol Nonvariant _    = Nonvariant
composePol _ Nonvariant    = Nonvariant
composePol Invariant _     = Invariant
composePol Covariant x     = x
composePol Contravariant x = neg x

polFromOcc :: Occurrence -> Polarity
polFromOcc o = case o of
  GuardPos  -> Covariant
  StrictPos -> Covariant
  JustPos   -> Covariant
  JustNeg   -> Contravariant
  Mixed     -> Invariant
  Unused    -> Nonvariant

------------------------------------------------------------------------
-- * Auxiliary functions
------------------------------------------------------------------------

-- | Get the next polarity from a list, 'Invariant' if empty.
nextPolarity :: [Polarity] -> (Polarity, [Polarity])
nextPolarity []       = (Invariant, [])
nextPolarity (p : ps) = (p, ps)

-- | Replace 'Nonvariant' by 'Covariant'.
--   (Arbitrary bias, but better than 'Invariant', see issue 1596).
purgeNonvariant :: [Polarity] -> [Polarity]
purgeNonvariant = map (\ p -> if p == Nonvariant then Covariant else p)


-- | A quick transliterations of occurrences to polarities.
polarityFromPositivity :: QName -> TCM ()
polarityFromPositivity x = inConcreteOrAbstractMode x $ \ def -> do

  -- Get basic polarity from positivity analysis.
  let npars = droppedPars def
  let pol0 = replicate npars Nonvariant ++ map polFromOcc (defArgOccurrences def)
  reportSLn "tc.polarity.set" 15 $
    "Polarity of " ++ prettyShow x ++ " from positivity: " ++ prettyShow pol0

  -- set the polarity in the signature (not the final polarity, though)
  setPolarity x $ drop npars pol0

------------------------------------------------------------------------
-- * Computing the polarity of a symbol.
------------------------------------------------------------------------

-- | Main function of this module.
computePolarity :: [QName] -> TCM ()
computePolarity xs = do

 -- Andreas, 2017-04-26, issue #2554
 -- First, for mutual definitions, obtain a crude polarity from positivity.
 when (length xs >= 2) $ mapM_ polarityFromPositivity xs

 -- Then, refine it.
 forM_ xs $ \ x -> inConcreteOrAbstractMode x $ \ def -> do
  reportSLn "tc.polarity.set" 25 $ "Refining polarity of " ++ prettyShow x

  -- Again: get basic polarity from positivity analysis.
  let npars = droppedPars def
  let pol0 = replicate npars Nonvariant ++ map polFromOcc (defArgOccurrences def)
  reportSLn "tc.polarity.set" 15 $
    "Polarity of " ++ prettyShow x ++ " from positivity: " ++ prettyShow pol0

{-
  -- get basic polarity from shape of def (arguments matched on or not?)
  def      <- getConstInfo x
  let usagePol = usagePolarity $ theDef def
  reportSLn "tc.polarity.set" 15 $ "Polarity of " ++ prettyShow x ++ " from definition form: " ++ prettyShow usagePol
  let n = genericLength usagePol  -- n <- getArity x
  reportSLn "tc.polarity.set" 20 $ "  arity = " ++ show n

  -- refine polarity by positivity information
  pol0 <- zipWith (/\) usagePol <$> mapM getPol [0..n - 1]
  reportSLn "tc.polarity.set" 15 $ "Polarity of " ++ prettyShow x ++ " from positivity: " ++ prettyShow pol0
-}

  -- compute polarity of sized types
  pol1 <- sizePolarity x pol0

  -- refine polarity again by using type information
  let t = defType def
  -- Instantiation takes place in Rules.Decl.instantiateDefinitionType
  -- t <- instantiateFull t -- Andreas, 2014-04-11 Issue 1099: needed for
  --                        -- variable occurrence test in  dependentPolarity.
  reportSDoc "tc.polarity.set" 15 $
    "Refining polarity with type " <+> prettyTCM t
  reportSDoc "tc.polarity.set" 60 $
    "Refining polarity with type (raw): " <+> (text .show) t

  pol <- dependentPolarity t (enablePhantomTypes (theDef def) pol1) pol1
  reportSLn "tc.polarity.set" 10 $ "Polarity of " ++ prettyShow x ++ ": " ++ prettyShow pol

  -- set the polarity in the signature
  setPolarity x $ drop npars pol -- purgeNonvariant pol -- temporarily disable non-variance

-- | Data and record parameters are used as phantom arguments all over
--   the test suite (and possibly in user developments).
--   @enablePhantomTypes@ turns 'Nonvariant' parameters to 'Covariant'
--   to enable phantoms.
enablePhantomTypes :: Defn -> [Polarity] -> [Polarity]
enablePhantomTypes def pol = case def of
  Datatype{ dataPars = np } -> enable np
  Record  { recPars  = np } -> enable np
  _                         -> pol
  where enable np = let (pars, rest) = splitAt np pol
                    in  purgeNonvariant pars ++ rest

{- UNUSED
-- | Extract a basic approximate polarity info from the shape of definition.
--   Arguments that are matched against get 'Invariant', others 'Nonvariant'.
--   For data types, parameters get 'Nonvariant', indices 'Invariant'.
usagePolarity :: Defn -> [Polarity]
usagePolarity def = case def of
    Axiom{}                                 -> []
    Function{ funClauses = [] }             -> []
    Function{ funClauses = cs }             -> usage $ map namedClausePats cs
    Datatype{ dataPars = np, dataIxs = ni } -> genericReplicate np Nonvariant
    Record{ recPars = n }                   -> genericReplicate n Nonvariant
    Constructor{}                           -> []
    Primitive{}                             -> []
  where
    usage = foldr1 (zipWith (/\)) . map (map (usagePat . namedArg))
    usagePat VarP{} = Nonvariant
    usagePat DotP{} = Nonvariant
    usagePat ConP{} = Invariant
    usagePat LitP{} = Invariant
-}

-- | Make arguments 'Invariant' if the type of a not-'Nonvariant'
--   later argument depends on it.
--   Also, enable phantom types by turning 'Nonvariant' into something
--   else if it is a data/record parameter but not a size argument. [See issue 1596]
--
--   Precondition: the "phantom" polarity list has the same length as the polarity list.
dependentPolarity :: Type -> [Polarity] -> [Polarity] -> TCM [Polarity]
dependentPolarity t _      []          = return []  -- all remaining are 'Invariant'
dependentPolarity t []     (_ : _)     = __IMPOSSIBLE__
dependentPolarity t (q:qs) pols@(p:ps) = do
  t <- reduce $ unEl t
  reportSDoc "tc.polarity.dep" 20 $ "dependentPolarity t = " <+> prettyTCM t
  reportSDoc "tc.polarity.dep" 70 $ "dependentPolarity t = " <+> (text . show) t
  case t of
    Pi dom b -> do
      ps <- underAbstraction dom b $ \ c -> dependentPolarity c qs ps
      let fallback = ifM (isJust <$> isSizeType (unDom dom)) (return p) (return q)
      p <- case b of
        Abs{} | p /= Invariant  ->
          -- Andreas, 2014-04-11 see Issue 1099
          -- Free variable analysis is not in the monad,
          -- hence metas must have been instantiated before!
          ifM (relevantInIgnoringNonvariant 0 (absBody b) ps)
            {- then -} (return Invariant)
            {- else -} fallback
        _ -> fallback
      return $ p : ps
    _ -> return pols

-- | Check whether a variable is relevant in a type expression,
--   ignoring domains of non-variant arguments.
relevantInIgnoringNonvariant :: Nat -> Type -> [Polarity] -> TCM Bool
relevantInIgnoringNonvariant i t []     = return $ i `relevantInIgnoringSortAnn` t
relevantInIgnoringNonvariant i t (p:ps) = do
  t <- reduce $ unEl t
  case t of
    Pi a b -> if p /= Nonvariant && i `relevantInIgnoringSortAnn` a then return True
              else relevantInIgnoringNonvariant (i + 1) (absBody b) ps
    _ -> return $ i `relevantInIgnoringSortAnn` t

------------------------------------------------------------------------
-- * Sized types
------------------------------------------------------------------------

-- | Hack for polarity of size indices.
--   As a side effect, this sets the positivity of the size index.
--   See test/succeed/PolaritySizeSucData.agda for a case where this is needed.
sizePolarity :: QName -> [Polarity] -> TCM [Polarity]
sizePolarity d pol0 = do
  let exit = return pol0
  ifM (not <$> sizedTypesOption) exit $ do
    def <- getConstInfo d
    case theDef def of
      Datatype{ dataPars = np, dataCons = cons } -> do
        let TelV tel _      = telView' $ defType def
            (parTel, ixTel) = splitAt np $ telToList tel
        case ixTel of
          []                 -> exit  -- No size index
          Dom{unDom = (_,a)} : _ -> ifM ((/= Just BoundedNo) <$> isSizeType a) exit $ do
            -- we assume the size index to be 'Covariant' ...
            let pol   = take np pol0
                polCo = pol ++ [Covariant]
                polIn = pol ++ [Invariant]
            setPolarity d $ polCo
            -- and seek confirm it by looking at the constructor types
            let check c = do
                  t <- defType <$> getConstInfo c
                  addContext (telFromList parTel) $ do
                    let pars = map (defaultArg . var) $ downFrom np
                    TelV conTel target <- telView =<< (t `piApplyM` pars)
                    case conTel of
                      EmptyTel  -> return False  -- no size argument
                      ExtendTel arg  tel ->
                        ifM ((/= Just BoundedNo) <$> isSizeType (unDom arg)) (return False) $ do -- also no size argument
                          -- First constructor argument has type Size

                          -- check that only positive occurences in tel
                          let isPos = underAbstraction arg tel $ \ tel -> do
                                pols <- zipWithM polarity [0..] $ map (snd . unDom) $ telToList tel
                                reportSDoc "tc.polarity.size" 25 $
                                  text $ "to pass size polarity check, the following polarities need all to be covariant: " ++ prettyShow pols
                                return $ all (`elem` [Nonvariant, Covariant]) pols

                          -- check that the size argument appears in the
                          -- right spot in the target type
                          let sizeArg = size tel
                              isLin = addContext conTel $ checkSizeIndex d np sizeArg target

                          ok <- isPos `and2M` isLin
                          reportSDoc "tc.polarity.size" 15 $
                            "constructor" <+> prettyTCM c <+>
                            text (if ok then "passes" else "fails") <+>
                            "size polarity check"
                          return ok

            ifNotM (andM $ map check cons)
                (return polIn) -- no, does not conform to the rules of sized types
              $ do  -- yes, we have a sized type here
                -- Andreas, 2015-07-01
                -- As a side effect, mark the size also covariant for subsequent
                -- positivity checking (which feeds back into polarity analysis).
                modifyArgOccurrences d $ \ occ -> take np occ ++ [JustPos]
                return polCo
      _ -> exit

-- | @checkSizeIndex d np i a@ checks that constructor target type @a@
--   has form @d ps (↑ⁿ i) idxs@ where @|ps| = np@.
--
--   Precondition: @a@ is reduced and of form @d ps idxs0@.
checkSizeIndex :: QName -> Nat -> Nat -> Type -> TCM Bool
checkSizeIndex d np i a = do
  reportSDoc "tc.polarity.size" 15 $ withShowAllArguments $ vcat
    [ "checking that constructor target type " <+> prettyTCM a
    , "  is data type " <+> prettyTCM d
    , "  and has size index (successor(s) of) " <+> prettyTCM (var i)
    ]
  case unEl a of
    Def d0 es -> do
      whenNothingM (sameDef d d0) __IMPOSSIBLE__
      s <- deepSizeView $ unArg ix
      case s of
        DSizeVar j _ | i == j
          -> return $ not $ freeIn i (pars ++ ixs)
        _ -> return False
      where
        (pars, Apply ix : ixs) = splitAt np es
    _ -> __IMPOSSIBLE__

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

instance HasPolarity a => HasPolarity (Elim' a) where
  polarities i Proj{}    = return []
  polarities i (Apply a) = polarities i a
  polarities i (IApply x y a) = polarities i (x,(y,a))

instance HasPolarity Term where
  polarities i v = do
   v <- instantiate v
   case v of
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
    Con _ _ ts -> polarities i ts -- constructors can be seen as monotone in all args.
    Pi a b     -> (++) <$> (map neg <$> polarities i a) <*> polarities i b
    Sort s     -> return [] -- polarities i s -- return []
    MetaV _ ts -> map (const Invariant) <$> polarities i ts
    DontCare t -> polarities i t -- return []
    Dummy{}    -> return []

instance HasPolarity Level where
  polarities i (Max as) = polarities i as

instance HasPolarity PlusLevel where
  polarities i ClosedLevel{} = return []
  polarities i (Plus _ l) = polarities i l

instance HasPolarity LevelAtom where
  polarities i l = case l of
    MetaLevel _ vs   -> map (const Invariant) <$> polarities i vs
    BlockedLevel _ v -> polarities i v
    NeutralLevel _ v -> polarities i v
    UnreducedLevel v -> polarities i v
