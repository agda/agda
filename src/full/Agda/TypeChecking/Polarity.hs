-- | Computing the polarity (variance) of function arguments,
--   for the sake of subtyping.

module Agda.TypeChecking.Polarity
  ( -- * Polarity computation
    computePolarity
    -- * Auxiliary functions
  , composePol
  , nextPolarity
  , purgeNonvariant
  , polFromOcc
  , neg
  , (\/)
  ) where

import Control.Monad  ( forM_, zipWithM )

import Data.Maybe
import Data.Semigroup ( Semigroup(..) )

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Datatypes (getNumberOfParameters)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Free
import Agda.TypeChecking.Polarity.Base
import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.List
import Agda.Utils.Maybe ( whenNothingM )
import Agda.Utils.Monad
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Utils.Singleton
import Agda.Utils.Size

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

-- | Supremum on the information lattice.
--   'Invariant' is bottom (neutral for sup),
--   'Nonvariant' is top (dominant for sup).
(\/) :: Polarity -> Polarity -> Polarity
Invariant \/ b = b
a \/ Invariant = a
a \/ b | a == b    = a
       | otherwise = Nonvariant

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
polFromOcc = \case
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
polarityFromPositivity
  :: (HasConstInfo m, MonadTCEnv m, MonadTCState m, MonadDebug m)
  => QName -> m ()
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
computePolarity
  :: ( HasOptions m, HasConstInfo m, HasBuiltins m
     , MonadTCEnv m, MonadTCState m, MonadReduce m, MonadAddContext m, MonadTCError m
     , MonadDebug m, MonadPretty m )
  => [QName] -> m ()
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
dependentPolarity
  :: (HasOptions m, HasBuiltins m, MonadReduce m, MonadAddContext m, MonadDebug m)
  => Type -> [Polarity] -> [Polarity] -> m [Polarity]
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
relevantInIgnoringNonvariant :: MonadReduce m => Nat -> Type -> [Polarity] -> m Bool
relevantInIgnoringNonvariant i t []     = return $ i `relevantInIgnoringSortAnn` t
relevantInIgnoringNonvariant i t (p:ps) =
  ifNotPiType t
    {-then-} (\ t -> return $ i `relevantInIgnoringSortAnn` t) $
    {-else-} \ a b ->
      if p /= Nonvariant && i `relevantInIgnoringSortAnn` a
        then return True
        else relevantInIgnoringNonvariant (i + 1) (absBody b) ps

------------------------------------------------------------------------
-- * Sized types
------------------------------------------------------------------------

-- | Hack for polarity of size indices.
--   As a side effect, this sets the positivity of the size index.
--   See test/succeed/PolaritySizeSucData.agda for a case where this is needed.
sizePolarity
  :: forall m .
     ( HasOptions m, HasConstInfo m, HasBuiltins m, ReadTCState m
     , MonadTCEnv m, MonadTCState m, MonadReduce m, MonadAddContext m, MonadTCError m
     , MonadDebug m, MonadPretty m )
  => QName -> [Polarity] -> m [Polarity]
sizePolarity d pol0 = do
  let exit = return pol0
  ifNotM sizedTypesOption exit $ {- else -} do
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
            let check :: QName -> m Bool
                check c = do
                  t <- defType <$> getConstInfo c
                  addContext (telFromList parTel) $ do
                    let pars = map (defaultArg . var) $ downFrom np
                    TelV conTel target <- telView =<< (t `piApplyM` pars)
                    loop target conTel
                  where
                  loop :: Type -> Telescope -> m Bool
                  -- no suitable size argument
                  loop _ EmptyTel = do
                    reportSDoc "tc.polarity.size" 15 $
                      "constructor" <+> prettyTCM c <+> "fails size polarity check"
                    return False

                  -- try argument @dom@
                  loop target (ExtendTel dom tel) = do
                    isSz <- isSizeType dom
                    underAbstraction dom tel $ \ tel -> do
                      let continue = loop target tel

                      -- check that dom == Size
                      if isSz /= Just BoundedNo then continue else do

                        -- check that the size argument appears in the
                        -- right spot in the target type
                        let sizeArg = size tel
                        isLin <- addContext tel $ checkSizeIndex d sizeArg target
                        if not isLin then continue else do

                          -- check that only positive occurences in tel
                          pols <- zipWithM polarity [0..] $ map (snd . unDom) $ telToList tel
                          reportSDoc "tc.polarity.size" 25 $
                            text $ "to pass size polarity check, the following polarities need all to be covariant: " ++ prettyShow pols
                          if any (`notElem` [Nonvariant, Covariant]) pols then continue else do
                            reportSDoc "tc.polarity.size" 15 $
                              "constructor" <+> prettyTCM c <+> "passes size polarity check"
                            return True

            ifNotM (andM $ map check cons)
                (return polIn) -- no, does not conform to the rules of sized types
              $ do  -- yes, we have a sized type here
                -- Andreas, 2015-07-01
                -- As a side effect, mark the size also covariant for subsequent
                -- positivity checking (which feeds back into polarity analysis).
                modifyArgOccurrences d $ \ occ -> take np occ ++ [JustPos]
                return polCo
      _ -> exit

-- | @checkSizeIndex d i a@ checks that constructor target type @a@
--   has form @d ps (↑ⁿ i) idxs@ where @|ps| = np(d)@.
--
--   Precondition: @a@ is reduced and of form @d ps idxs0@.
checkSizeIndex
  :: (HasConstInfo m, ReadTCState m, MonadDebug m, MonadPretty m, MonadTCError m)
  => QName -> Nat -> Type -> m Bool
checkSizeIndex d i a = do
  reportSDoc "tc.polarity.size" 15 $ withShowAllArguments $ vcat
    [ "checking that constructor target type " <+> prettyTCM a
    , "  is data type " <+> prettyTCM d
    , "  and has size index (successor(s) of) " <+> prettyTCM (var i)
    ]
  case unEl a of
    Def d0 es -> do
      whenNothingM (sameDef d d0) __IMPOSSIBLE__
      np <- fromMaybe __IMPOSSIBLE__ <$> getNumberOfParameters d0
      let (pars, Apply ix : ixs) = splitAt np es
      s <- deepSizeView $ unArg ix
      case s of
        DSizeVar (ProjectedVar j []) _ | i == j
          -> return $ not $ freeIn i (pars ++ ixs)
        _ -> return False
    _ -> __IMPOSSIBLE__

-- | @polarity i a@ computes the least polarity of de Bruijn index @i@
--   in syntactic entity @a@.
polarity
  :: (HasPolarity a, HasConstInfo m, MonadReduce m)
  => Nat -> a -> m Polarity
polarity i x = getLeastPolarity $ polarity' i Covariant x

-- | A monoid for lazily computing the infimum of the polarities of a variable in some object.
-- Allows short-cutting.

newtype LeastPolarity m = LeastPolarity { getLeastPolarity :: m Polarity}

instance Monad m => Singleton Polarity (LeastPolarity m) where
  singleton = LeastPolarity . return

instance Monad m => Semigroup (LeastPolarity m) where
  LeastPolarity mp <> LeastPolarity mq = LeastPolarity $ do
    mp >>= \case
      Invariant  -> return Invariant  -- Shortcut for the absorbing element.
      Nonvariant -> mq                -- The neutral element.
      p          -> (p /\) <$> mq

instance Monad m => Monoid (LeastPolarity m) where
  mempty  = singleton Nonvariant
  mappend = (<>)

-- | Bind for 'LeastPolarity'.
(>>==) :: Monad m => m a -> (a -> LeastPolarity m) -> LeastPolarity m
m >>== k = LeastPolarity $ m >>= getLeastPolarity . k

-- | @polarity' i p a@ computes the least polarity of de Bruijn index @i@
--   in syntactic entity @a@, where root occurrences count as @p@.
--
--   Ignores occurrences in sorts.
class HasPolarity a where
  polarity'
    :: (HasConstInfo m, MonadReduce m)
    => Nat -> Polarity -> a -> LeastPolarity m

  default polarity'
    :: (HasConstInfo m, MonadReduce m, HasPolarity b, Foldable t, t b ~ a)
    => Nat -> Polarity -> a -> LeastPolarity m
  polarity' i = foldMap . polarity' i

instance HasPolarity a => HasPolarity [a]
instance HasPolarity a => HasPolarity (Arg a)
instance HasPolarity a => HasPolarity (Dom a)
instance HasPolarity a => HasPolarity (Elim' a)
instance HasPolarity a => HasPolarity (Level' a)
instance HasPolarity a => HasPolarity (PlusLevel' a)

-- | Does not look into sort.
instance HasPolarity a => HasPolarity (Type'' t a)

instance (HasPolarity a, HasPolarity b) => HasPolarity (a, b) where
  polarity' i p (x, y) = polarity' i p x <> polarity' i p y

instance HasPolarity a => HasPolarity (Abs a) where
  polarity' i p (Abs   _ b) = polarity' (i + 1) p b
  polarity' i p (NoAbs _ v) = polarity' i p v

instance HasPolarity Term where
  polarity' i p v = instantiate v >>== \case
    -- Andreas, 2012-09-06: taking the polarity' of the arguments
    -- without taking the variance of the function into account seems wrong.
    Var n ts
      | n == i    -> singleton p <> polarity' i Invariant ts
      | otherwise -> polarity' i Invariant ts
    Lam _ t       -> polarity' i p t
    Lit _         -> mempty
    Level l       -> polarity' i p l
    Def x ts      -> getPolarity x >>== \ pols ->
                       let ps = map (composePol p) pols ++ repeat Invariant
                       in  mconcat $ zipWith (polarity' i) ps ts
    Con _ _ ts    -> polarity' i p ts   -- Constructors can be seen as monotone in all args.
    Pi a b        -> polarity' i (neg p) a <> polarity' i p b
    Sort s        -> mempty -- polarity' i p s -- mempty
    MetaV _ ts    -> polarity' i Invariant ts
    DontCare t    -> polarity' i p t -- mempty
    Dummy{}       -> mempty
