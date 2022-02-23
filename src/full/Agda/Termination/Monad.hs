
-- | The monad for the termination checker.
--
--   The termination monad @TerM@ is an extension of
--   the type checking monad 'TCM' by an environment
--   with information needed by the termination checker.

module Agda.Termination.Monad where

import Prelude hiding (null)

import Control.Applicative hiding (empty)

import qualified Control.Monad.Fail as Fail

import Control.Monad          ( forM )
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.Except
import Control.Monad.Reader

import Data.Semigroup ( Semigroup(..) )
import qualified Data.Set as Set

import Agda.Interaction.Options (optTerminationDepth)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Literal
import Agda.Syntax.Position (noRange)

import Agda.Termination.CutOff
import Agda.Termination.Order (Order,le,unknown)
import Agda.Termination.RecCheck (anyDefs)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Benchmark
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Benchmark as B
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List   ( hasElem )
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Monoid
import Agda.Utils.Null
import Agda.Utils.Pretty (Pretty, prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Agda.Utils.Impossible

-- | The mutual block we are checking.
--
--   The functions are numbered according to their order of appearance
--   in this list.

type MutualNames = [QName]

-- | The target of the function we are checking.

type Target = QName

-- | The current guardedness level.

type Guarded = Order

-- | The termination environment.

data TerEnv = TerEnv

  -- First part: options, configuration.

  { terUseDotPatterns :: Bool
    -- ^ Are we mining dot patterns to find evindence of structal descent?
  , terSizeSuc :: Maybe QName
    -- ^ The name of size successor, if any.
  , terSharp   :: Maybe QName
    -- ^ The name of the delay constructor (sharp), if any.
  , terCutOff  :: CutOff
    -- ^ Depth at which to cut off the structural order.

  -- Second part: accumulated info during descent into decls./term.

  , terCurrent :: QName
    -- ^ The name of the function we are currently checking.
  , terMutual  :: MutualNames
    -- ^ The names of the functions in the mutual block we are checking.
    --   This includes the internally generated functions
    --   (with, extendedlambda, coinduction).
  , terUserNames :: [QName]
    -- ^ The list of name actually appearing in the file (abstract syntax).
    --   Excludes the internally generated functions.
  , terHaveInlinedWith :: Bool
    -- ^ Does the actual clause result from with-inlining?
    --   (If yes, it may be ill-typed.)
  , terTarget  :: Maybe Target
    -- ^ Target type of the function we are currently termination checking.
    --   Only the constructors of 'Target' are considered guarding.
  , terDelayed :: Delayed
    -- ^ Are we checking a delayed definition?
  , terMaskArgs :: [Bool]
    -- ^ Only consider the 'notMasked' 'False' arguments for establishing termination.
    --   See issue #1023.
  , terMaskResult :: Bool
    -- ^ Only consider guardedness if 'False' (not masked).
  , _terSizeDepth :: Int  -- lazy by intention!
    -- ^ How many @SIZELT@ relations do we have in the context
    --   (= clause telescope).  Used to approximate termination
    --   for metas in call args.
  , terPatterns :: MaskedDeBruijnPatterns
    -- ^ The patterns of the clause we are checking.
  , terPatternsRaise :: !Int
    -- ^ Number of additional binders we have gone under
    --   (and consequently need to raise the patterns to compare to terms).
    --   Updated during call graph extraction, hence strict.
  , terGuarded :: !Guarded
    -- ^ The current guardedness status.  Changes as we go deeper into the term.
    --   Updated during call graph extraction, hence strict.
  , terUseSizeLt :: Bool
    -- ^ When extracting usable size variables during construction of the call
    --   matrix, can we take the variable for use with SIZELT constraints from the context?
    --   Yes, if we are under an inductive constructor.
    --   No, if we are under a record constructor.
    --   (See issue #1015).
  , terUsableVars :: VarSet
    -- ^ Pattern variables that can be compared to argument variables using SIZELT.
  }

-- | An empty termination environment.
--
--   Values are set to a safe default meaning that with these
--   initial values the termination checker will not miss
--   termination errors it would have seen with better settings
--   of these values.
--
--   Values that do not have a safe default are set to
--   @__IMPOSSIBLE__@.

defaultTerEnv :: TerEnv
defaultTerEnv = TerEnv
  { terUseDotPatterns           = False -- must be False initially!
  , terSizeSuc                  = Nothing
  , terSharp                    = Nothing
  , terCutOff                   = defaultCutOff
  , terUserNames                = __IMPOSSIBLE__ -- needs to be set!
  , terMutual                   = __IMPOSSIBLE__ -- needs to be set!
  , terCurrent                  = __IMPOSSIBLE__ -- needs to be set!
  , terHaveInlinedWith          = False
  , terTarget                   = Nothing
  , terDelayed                  = NotDelayed
  , terMaskArgs                 = repeat False   -- use all arguments (mask none)
  , terMaskResult               = False          -- use result (do not mask)
  , _terSizeDepth               = __IMPOSSIBLE__ -- needs to be set!
  , terPatterns                 = __IMPOSSIBLE__ -- needs to be set!
  , terPatternsRaise            = 0
  , terGuarded                  = le -- not initially guarded
  , terUseSizeLt                = False -- initially, not under data constructor
  , terUsableVars               = VarSet.empty
  }

-- | Termination monad service class.

class (Functor m, Monad m) => MonadTer m where
  terAsk   :: m TerEnv
  terLocal :: (TerEnv -> TerEnv) -> m a -> m a

  terAsks :: (TerEnv -> a) -> m a
  terAsks f = f <$> terAsk

-- | Termination monad.

newtype TerM a = TerM { terM :: ReaderT TerEnv TCM a }
  deriving ( Functor
           , Applicative
           , Monad
           , Fail.MonadFail
           , MonadError TCErr
           , MonadStatistics
           , HasOptions
           , HasBuiltins
           , MonadDebug
           , HasConstInfo
           , MonadIO
           , MonadTCEnv
           , MonadTCState
           , MonadTCM
           , ReadTCState
           , MonadReduce
           , MonadAddContext
           , PureTCM
           )

-- This could be derived automatically, but the derived type family becomes `BenchPhase (ReaderT TerEnv TCM)` which
-- is *fine* but triggers complaints that the "type family application is no smaller than the instance head, why not
-- nuke everything with UndecidableInstances".
instance MonadBench TerM where
  type BenchPhase TerM = Phase
  getBenchmark              = TerM $ B.getBenchmark
  putBenchmark              = TerM . B.putBenchmark
  modifyBenchmark           = TerM . B.modifyBenchmark
  finally (TerM m) (TerM f) = TerM $ (B.finally m f)

instance MonadTer TerM where
  terAsk     = TerM $ ask
  terLocal f = TerM . local f . terM

-- | Generic run method for termination monad.
runTer :: TerEnv -> TerM a -> TCM a
runTer tenv (TerM m) = runReaderT m tenv

-- | Run TerM computation in default environment (created from options).

runTerDefault :: TerM a -> TCM a
runTerDefault cont = do

  -- Assemble then initial configuration of the termination environment.

  cutoff <- optTerminationDepth <$> pragmaOptions

  -- Get the name of size suc (if sized types are enabled)
  suc <- sizeSucName

  -- The name of sharp (if available).
  sharp <- fmap nameOfSharp <$> coinductionKit

  let tenv = defaultTerEnv
        { terSizeSuc                  = suc
        , terSharp                    = sharp
        , terCutOff                   = cutoff
        }

  runTer tenv cont

-- -- * Termination monad is a 'MonadTCM'.

-- instance MonadError TCErr TerM where
--   throwError = liftTCM . throwError
--   catchError m handler = TerM $ ReaderT $ \ tenv -> do
--     runTer tenv m `catchError` (\ err -> runTer tenv $ handler err)

instance Semigroup m => Semigroup (TerM m) where
  (<>) = liftA2 (<>)

instance (Semigroup m, Monoid m) => Monoid (TerM m) where
  mempty  = pure mempty
  mappend = (<>)
  mconcat = mconcat <.> sequence

-- * Modifiers and accessors for the termination environment in the monad.

terGetUseDotPatterns :: TerM Bool
terGetUseDotPatterns = terAsks terUseDotPatterns

terSetUseDotPatterns :: Bool -> TerM a -> TerM a
terSetUseDotPatterns b = terLocal $ \ e -> e { terUseDotPatterns = b }

terGetSizeSuc :: TerM (Maybe QName)
terGetSizeSuc = terAsks terSizeSuc

terGetCurrent :: TerM QName
terGetCurrent = terAsks terCurrent

terSetCurrent :: QName -> TerM a -> TerM a
terSetCurrent q = terLocal $ \ e -> e { terCurrent = q }

terGetSharp :: TerM (Maybe QName)
terGetSharp = terAsks terSharp

terGetCutOff :: TerM CutOff
terGetCutOff = terAsks terCutOff

terGetMutual :: TerM MutualNames
terGetMutual = terAsks terMutual

terGetUserNames :: TerM [QName]
terGetUserNames = terAsks terUserNames

terGetTarget :: TerM (Maybe Target)
terGetTarget = terAsks terTarget

terSetTarget :: Maybe Target -> TerM a -> TerM a
terSetTarget t = terLocal $ \ e -> e { terTarget = t }

terGetHaveInlinedWith :: TerM Bool
terGetHaveInlinedWith = terAsks terHaveInlinedWith

terSetHaveInlinedWith :: TerM a -> TerM a
terSetHaveInlinedWith = terLocal $ \ e -> e { terHaveInlinedWith = True }

terGetDelayed :: TerM Delayed
terGetDelayed = terAsks terDelayed

terSetDelayed :: Delayed -> TerM a -> TerM a
terSetDelayed b = terLocal $ \ e -> e { terDelayed = b }

terGetMaskArgs :: TerM [Bool]
terGetMaskArgs = terAsks terMaskArgs

terSetMaskArgs :: [Bool] -> TerM a -> TerM a
terSetMaskArgs b = terLocal $ \ e -> e { terMaskArgs = b }

terGetMaskResult :: TerM Bool
terGetMaskResult = terAsks terMaskResult

terSetMaskResult :: Bool -> TerM a -> TerM a
terSetMaskResult b = terLocal $ \ e -> e { terMaskResult = b }

terGetPatterns :: TerM (MaskedDeBruijnPatterns)
terGetPatterns = do
  n   <- terAsks terPatternsRaise
  mps <- terAsks terPatterns
  return $ if n == 0 then mps else map (fmap (raise n)) mps

terSetPatterns :: MaskedDeBruijnPatterns -> TerM a -> TerM a
terSetPatterns ps = terLocal $ \ e -> e { terPatterns = ps }

terRaise :: TerM a -> TerM a
terRaise = terLocal $ \ e -> e { terPatternsRaise = terPatternsRaise e + 1 }

terGetGuarded :: TerM Guarded
terGetGuarded = terAsks terGuarded

terModifyGuarded :: (Order -> Order) -> TerM a -> TerM a
terModifyGuarded f = terLocal $ \ e -> e { terGuarded = f $ terGuarded e }

terSetGuarded :: Order -> TerM a -> TerM a
terSetGuarded = terModifyGuarded . const

terUnguarded :: TerM a -> TerM a
terUnguarded = terSetGuarded unknown

-- | Lens for '_terSizeDepth'.

terSizeDepth :: Lens' Int TerEnv
terSizeDepth f e = f (_terSizeDepth e) <&> \ i -> e { _terSizeDepth = i }

-- | Lens for 'terUsableVars'.

terGetUsableVars :: TerM VarSet
terGetUsableVars = terAsks terUsableVars

terModifyUsableVars :: (VarSet -> VarSet) -> TerM a -> TerM a
terModifyUsableVars f = terLocal $ \ e -> e { terUsableVars = f $ terUsableVars e }

terSetUsableVars :: VarSet -> TerM a -> TerM a
terSetUsableVars = terModifyUsableVars . const

-- | Lens for 'terUseSizeLt'.

terGetUseSizeLt :: TerM Bool
terGetUseSizeLt = terAsks terUseSizeLt

terModifyUseSizeLt :: (Bool -> Bool) -> TerM a -> TerM a
terModifyUseSizeLt f = terLocal $ \ e -> e { terUseSizeLt = f $ terUseSizeLt e }

terSetUseSizeLt :: Bool -> TerM a -> TerM a
terSetUseSizeLt = terModifyUseSizeLt . const

-- | Compute usable vars from patterns and run subcomputation.
withUsableVars :: UsableSizeVars a => a -> TerM b -> TerM b
withUsableVars pats m = do
  vars <- usableSizeVars pats
  reportSLn "term.size" 70 $ "usableSizeVars = " ++ show vars
  reportSDoc "term.size" 20 $ if null vars then "no usuable size vars" else
    "the size variables amoung these variables are usable: " <+>
      sep (map (prettyTCM . var) $ VarSet.toList vars)
  terSetUsableVars vars $ m

-- | Set 'terUseSizeLt' when going under constructor @c@.
conUseSizeLt :: QName -> TerM a -> TerM a
conUseSizeLt c m = do
  ifM (liftTCM $ isEtaOrCoinductiveRecordConstructor c)  -- Non-eta inductive records are the same as datatypes
    (terSetUseSizeLt False m)
    (terSetUseSizeLt True m)

-- | Set 'terUseSizeLt' for arguments following projection @q@.
--   We disregard j<i after a non-coinductive projection.
--   However, the projection need not be recursive (Issue 1470).
projUseSizeLt :: QName -> TerM a -> TerM a
projUseSizeLt q m = do
  co <- isCoinductiveProjection False q
  reportSLn "term.size" 20 $ applyUnless co ("not " ++) $
    "using SIZELT vars after projection " ++ prettyShow q
  terSetUseSizeLt co m

-- | For termination checking purposes flat should not be considered a
--   projection. That is, it flat doesn't preserve either structural order
--   or guardedness like other projections do.
--   Andreas, 2012-06-09: the same applies to projections of recursive records.
isProjectionButNotCoinductive :: MonadTCM tcm => QName -> tcm Bool
isProjectionButNotCoinductive qn = liftTCM $ do
  b <- isProjectionButNotCoinductive' qn
  reportSDoc "term.proj" 60 $ do
    "identifier" <+> prettyTCM qn <+> do
      text $
        if b then "is an inductive projection"
          else "is either not a projection or coinductive"
  return b
  where
    isProjectionButNotCoinductive' qn = do
      flat <- fmap nameOfFlat <$> coinductionKit
      if Just qn == flat
        then return False
        else do
          mp <- isProjection qn
          case mp of
            Just Projection{ projProper = Just{}, projFromType = t }
              -> isInductiveRecord (unArg t)
            _ -> return False

-- | Check whether a projection belongs to a coinductive record
--   and is actually recursive.
--   E.g.
--   @
--      isCoinductiveProjection (Stream.head) = return False
--
--      isCoinductiveProjection (Stream.tail) = return True
--   @
isCoinductiveProjection :: MonadTCM tcm => Bool -> QName -> tcm Bool
isCoinductiveProjection mustBeRecursive q = liftTCM $ do
  reportSLn "term.guardedness" 40 $ "checking isCoinductiveProjection " ++ prettyShow q
  flat <- fmap nameOfFlat <$> coinductionKit
  -- yes for ♭
  if Just q == flat then return True else do
    pdef <- getConstInfo q
    case isProjection_ (theDef pdef) of
      Just Projection{ projProper = Just{}, projFromType = Arg _ r, projIndex = n } ->
        caseMaybeM (isRecord r) __IMPOSSIBLE__ $ \ rdef -> do
          -- no for inductive or non-recursive record
          if recInduction rdef /= Just CoInductive then return False else do
            reportSLn "term.guardedness" 40 $ prettyShow q ++ " is coinductive; record type is " ++ prettyShow r
            if not mustBeRecursive then return True else do
              reportSLn "term.guardedness" 40 $ prettyShow q ++ " must be recursive"
              if not (safeRecRecursive rdef) then return False else do
                reportSLn "term.guardedness" 40 $ prettyShow q ++ " has been declared recursive, doing actual check now..."
                -- TODO: the following test for recursiveness of a projection should be cached.
                -- E.g., it could be stored in the @Projection@ component.
                -- Now check if type of field mentions mutually recursive symbol.
                -- Get the type of the field by dropping record parameters and record argument.
                let TelV tel core = telView' (defType pdef)
                    (pars, tel') = splitAt n $ telToList tel
                    mut = fromMaybe __IMPOSSIBLE__ $ recMutual rdef
                -- Check if any recursive symbols appear in the record type.
                -- Q (2014-07-01): Should we normalize the type?
                -- A (2017-01-13): Yes, since we also normalize during positivity check?
                -- See issue #1899.
                reportSDoc "term.guardedness" 40 $ inTopContext $ sep
                  [ "looking for recursive occurrences of"
                  , sep (map prettyTCM mut)
                  , "in"
                  , addContext pars $ prettyTCM (telFromList tel')
                  , "and"
                  , addContext tel $ prettyTCM core
                  ]
                when (null mut) __IMPOSSIBLE__
                names <- anyDefs (mut `hasElem`) (map (snd . unDom) tel', core)
                reportSDoc "term.guardedness" 40 $
                  "found" <+> if null names then "none" else sep (map prettyTCM $ Set.toList names)
                return $ not $ null names
      _ -> do
        reportSLn "term.guardedness" 40 $ prettyShow q ++ " is not a proper projection"
        return False
  where
  -- Andreas, 2018-02-24, issue #2975, example:
  -- @
  -- record R : Set where
  --   coinductive
  --   field force : R

  --   r : R
  --   force r = r
  -- @
  -- The termination checker expects the positivity checker to have run on the
  -- record declaration R to know whether R is recursive.
  -- However, here, because the awkward processing of record declarations (see #434),
  -- that has not happened.  To avoid crashing (as in Agda 2.5.3),
  -- we rather give the possibly wrong answer here,
  -- restoring the behavior of Agda 2.5.2.  TODO: fix record declaration checking.
  safeRecRecursive :: Defn -> Bool
  safeRecRecursive (Record { recMutual = Just qs }) = not $ null qs
  safeRecRecursive _ = False

-- * De Bruijn pattern stuff

-- | How long is the path to the deepest atomic pattern?
patternDepth :: forall a. Pattern' a -> Int
patternDepth = getMaxNat . foldrPattern depth where
  depth :: Pattern' a -> MaxNat -> MaxNat
  depth ConP{} = succ      -- add 1 to the maximum of the depth of the subpatterns
  depth _      = id        -- atomic pattern (leaf) has depth 0

-- | A dummy pattern used to mask a pattern that cannot be used
--   for structural descent.

unusedVar :: DeBruijnPattern
unusedVar = litP (LitString "term.unused.pat.var")

-- | Extract variables from 'DeBruijnPattern's that could witness a decrease
--   via a SIZELT constraint.
--
--   These variables must be under an inductive constructor (with no record
--   constructor in the way), or after a coinductive projection (with no
--   inductive one in the way).

class UsableSizeVars a where
  usableSizeVars :: a -> TerM VarSet

instance UsableSizeVars DeBruijnPattern where
  usableSizeVars = foldrPattern $ \case
    VarP _ x   -> const $ ifM terGetUseSizeLt (return $ VarSet.singleton $ dbPatVarIndex x) $
                   {-else-} return mempty
    ConP c _ _ -> conUseSizeLt $ conName c
    LitP{}     -> none
    DotP{}     -> none
    ProjP{}    -> none
    IApplyP{}  -> none
    DefP{} -> none
    where none _ = return mempty

instance UsableSizeVars [DeBruijnPattern] where
  usableSizeVars ps =
    case ps of
      []               -> return mempty
      (ProjP _ q : ps) -> projUseSizeLt q $ usableSizeVars ps
      (p         : ps) -> mappend <$> usableSizeVars p <*> usableSizeVars ps

instance UsableSizeVars (Masked DeBruijnPattern) where
  usableSizeVars (Masked m p) = (`foldrPattern` p) $ \case
    VarP _ x   -> const $ ifM terGetUseSizeLt (return $ VarSet.singleton $ dbPatVarIndex x) $
                   {-else-} return mempty
    ConP c _ _ -> if m then none else conUseSizeLt $ conName c
    LitP{}     -> none
    DotP{}     -> none
    ProjP{}    -> none
    IApplyP{}  -> none
    DefP{}     -> none
    where none _ = return mempty

instance UsableSizeVars MaskedDeBruijnPatterns where
  usableSizeVars ps =
    case ps of
      []                          -> return mempty
      (Masked _ (ProjP _ q) : ps) -> projUseSizeLt q $ usableSizeVars ps
      (p                    : ps) -> mappend <$> usableSizeVars p <*> usableSizeVars ps

-- * Masked patterns (which are not eligible for structural descent, only for size descent)
--   See issue #1023.

type MaskedDeBruijnPatterns = [Masked DeBruijnPattern]

data Masked a = Masked
  { getMask   :: Bool  -- ^ True if thing not eligible for structural descent.
  , getMasked :: a     -- ^ Thing.
  } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

masked :: a -> Masked a
masked = Masked True

notMasked :: a -> Masked a
notMasked = Masked False

instance Decoration Masked where
  traverseF f (Masked m a) = Masked m <$> f a

-- | Print masked things in double parentheses.
instance PrettyTCM a => PrettyTCM (Masked a) where
  prettyTCM (Masked m a) = applyWhen m (parens . parens) $ prettyTCM a

-- * Call pathes

-- | The call information is stored as free monoid
--   over 'CallInfo'.  As long as we never look at it,
--   only accumulate it, it does not matter whether we use
--   'Set', (nub) list, or 'Tree'.
--   Internally, due to lazyness, it is anyway a binary tree of
--   'mappend' nodes and singleton leafs.
--   Since we define no order on 'CallInfo' (expensive),
--   we cannot use a 'Set' or nub list.
--   Performance-wise, I could not see a difference between Set and list.

newtype CallPath = CallPath { callInfos :: [CallInfo] }
  deriving (Show, Semigroup, Monoid)

-- | Only show intermediate nodes.  (Drop last 'CallInfo').
instance Pretty CallPath where
  pretty (CallPath cis0) = if null cis then empty else
    P.hsep (map (\ ci -> arrow P.<+> P.pretty ci) cis) P.<+> arrow
    where
      cis   = init cis0
      arrow = "-->"

-- * Size depth estimation

-- | A very crude way of estimating the @SIZELT@ chains
--   @i > j > k@ in context.  Returns 3 in this case.
--   Overapproximates.

-- TODO: more precise analysis, constructing a tree
-- of relations between size variables.
terSetSizeDepth :: Telescope -> TerM a -> TerM a
terSetSizeDepth tel cont = do
  n <- liftTCM $ sum <$> do
    forM (telToList tel) $ \ dom -> do
      a <- reduce $ snd $ unDom dom
      ifM (isJust <$> isSizeType a) (return 1) {- else -} $
        case unEl a of
          MetaV{} -> return 1
          _       -> return 0
  terLocal (set terSizeDepth n) cont
