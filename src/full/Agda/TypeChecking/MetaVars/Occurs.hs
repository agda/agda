{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE UndecidableInstances #-}

{- | The occurs check for unification.  Does pruning on the fly.

  When hitting a meta variable:

  - Compute flex/rigid for its arguments.
  - Compare to allowed variables.
  - Mark arguments with rigid occurrences of disallowed variables for deletion.
  - Attempt to delete marked arguments.
  - We don't need to check for success, we can just continue occurs checking.
-}

module Agda.TypeChecking.MetaVars.Occurs where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader

import Data.Foldable (foldMap)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse)

import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free hiding (Occurrence(..))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
-- import Agda.TypeChecking.MetaVars

import Agda.Utils.Either

import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )

import Agda.Utils.Lens
import Agda.Utils.List (downFrom)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

{- To address issue 585 (meta var occurrences in mutual defs)

data B : Set where
  inn : A -> B

out : B -> A
out (inn a) = a

postulate
  P : (y : A) (z : Unit -> B) → Set
  p : (x : Unit -> B) → P (out (x unit)) x

mutual
  d : Unit -> B
  d unit = inn _           -- Y

  g : P (out (d unit)) d
  g = p _             -- X

-- Agda solves  d unit = inn (out (d unit))
--
-- out (X unit) = out (d unit) = out (inn Y) = Y
-- X = d

When doing the occurs check on d, we need to look at the definition of
d to discover that it mentions X.

To this end, we extend the state by names of definitions that have to
be checked when they occur.  At the beginning, this is initialized
with the names in the current mutual block.  Each time we encounter a
name in the list during occurs check, we delete it (if check is
successful).  This way, we do not duplicate work.

-}

modifyOccursCheckDefs :: (Set QName -> Set QName) -> TCM ()
modifyOccursCheckDefs f = stOccursCheckDefs %= f

-- | Set the names of definitions to be looked at
--   to the defs in the current mutual block.
initOccursCheck :: MetaVariable -> TCM ()
initOccursCheck mv = modifyOccursCheckDefs . const =<<
  if (miMetaOccursCheck (mvInfo mv) == DontRunMetaOccursCheck)
   then do
     reportSLn "tc.meta.occurs" 20 $
       "initOccursCheck: we do not look into definitions"
     return Set.empty
   else do
     reportSLn "tc.meta.occurs" 20 $
       "initOccursCheck: we look into the following definitions:"
     mb <- asks envMutualBlock
     case mb of
       Nothing -> do
         reportSLn "tc.meta.occurs" 20 $ "(none)"
         return Set.empty
       Just b  -> do
         ds <- mutualNames <$> lookupMutualBlock b
         reportSDoc "tc.meta.occurs" 20 $ sep $ map prettyTCM $ Set.toList ds
         return ds


-- | Is a def in the list of stuff to be checked?
defNeedsChecking :: QName -> TCM Bool
defNeedsChecking d = Set.member d <$> use stOccursCheckDefs

-- | Remove a def from the list of defs to be looked at.
tallyDef :: QName -> TCM ()
tallyDef d = modifyOccursCheckDefs $ \ s -> Set.delete d s

data OccursCtx
  = Flex          -- ^ We are in arguments of a meta.
  | Rigid         -- ^ We are not in arguments of a meta but a bound var.
  | StronglyRigid -- ^ We are at the start or in the arguments of a constructor.
  | Top           -- ^ We are at the term root (this turns into @StronglyRigid@).
  | Irrel         -- ^ We are in an irrelevant argument.
  deriving (Eq, Show)

data UnfoldStrategy = YesUnfold | NoUnfold
  deriving (Eq, Show)

defArgs :: UnfoldStrategy -> OccursCtx -> OccursCtx
defArgs NoUnfold  _   = Flex
defArgs YesUnfold ctx = weakly ctx

unfold :: UnfoldStrategy -> Term -> TCM (Blocked Term)
unfold NoUnfold  v = notBlocked <$> instantiate v
unfold YesUnfold v = reduceB v

-- | Leave the top position.
leaveTop :: OccursCtx -> OccursCtx
leaveTop Top = StronglyRigid
leaveTop ctx = ctx

-- | Leave the strongly rigid position.
weakly :: OccursCtx -> OccursCtx
weakly Top           = Rigid
weakly StronglyRigid = Rigid
weakly ctx = ctx

strongly :: OccursCtx -> OccursCtx
strongly Rigid = StronglyRigid
strongly ctx = ctx

patternViolation' :: Int -> String -> TCM a
patternViolation' n err = do
  reportSLn "tc.meta.occurs" n err
  patternViolation

abort :: OccursCtx -> TypeError -> TCM a
abort Top           err = typeError err
abort StronglyRigid err = typeError err -- here, throw an uncatchable error (unsolvable constraint)
abort Flex          err = patternViolation' 70 (show err) -- throws a PatternErr, which leads to delayed constraint
abort Rigid         err = patternViolation' 70 (show err)
abort Irrel         err = patternViolation' 70 (show err)

-- | Distinguish relevant and irrelevant variables in occurs check.
type Vars = ([Nat],[Nat])

goIrrelevant :: Vars -> Vars
goIrrelevant (relVs, irrVs) = (irrVs ++ relVs, [])

allowedVar :: Nat -> Vars -> Bool
allowedVar i (relVs, irrVs) = i `elem` relVs

takeRelevant :: Vars -> [Nat]
takeRelevant = fst

liftUnderAbs :: Vars -> Vars
liftUnderAbs (relVs, irrVs) = (0 : map (1+) relVs, map (1+) irrVs)

-- | Extended occurs check.
class Occurs t where
  occurs :: UnfoldStrategy -> OccursCtx -> MetaId -> Vars -> t -> TCM t
  metaOccurs :: MetaId -> t -> TCM ()  -- raise exception if meta occurs in t

-- | When assigning @m xs := v@, check that @m@ does not occur in @v@
--   and that the free variables of @v@ are contained in @xs@.
occursCheck
  :: (Occurs a, InstantiateFull a, PrettyTCM a)
  => MetaId -> Vars -> a -> TCM a
occursCheck m xs v = disableDestructiveUpdate $ Bench.billTo [ Bench.Typing, Bench.OccursCheck ] $ do
  mv <- lookupMeta m
  initOccursCheck mv
      -- TODO: Can we do this in a better way?
  let redo m = m -- disableDestructiveUpdate m >> m
  -- First try without normalising the term
  redo (occurs NoUnfold  Top m xs v) `catchError` \_ -> do
    initOccursCheck mv
    redo (occurs YesUnfold Top m xs v) `catchError` \err -> case err of
                            -- Produce nicer error messages
      TypeError _ cl -> case clValue cl of
        MetaOccursInItself{} ->
          typeError . GenericError . show =<<
            fsep [ text ("Refuse to construct infinite term by instantiating " ++ prettyShow m ++ " to")
                 , prettyTCM =<< instantiateFull v
                 ]
        MetaCannotDependOn _ _ i ->
          ifM (isSortMeta m `and2M` (not <$> hasUniversePolymorphism))
          ( typeError . GenericError . show =<<
            fsep [ text ("Cannot instantiate the metavariable " ++ prettyShow m ++ " to")
                 , prettyTCM v
                 , text "since universe polymorphism is disabled"
                 ]
          ) {- else -}
          ( typeError . GenericError . show =<<
              fsep [ text ("Cannot instantiate the metavariable " ++ prettyShow m ++ " to solution")
                   , prettyTCM v
                   , text "since it contains the variable"
                   , enterClosure cl $ \_ -> prettyTCM (Var i [])
                   , text $ "which is not in scope of the metavariable or irrelevant in the metavariable but relevant in the solution"
                   ]
            )
        _ -> throwError err
      _ -> throwError err

instance Occurs Term where
  occurs red ctx m xs v = do
    v <- unfold red v
    -- occurs' ctx $ ignoreBlocking v  -- fails test/succeed/DontPruneBlocked
    case v of
      -- Don't fail on blocked terms or metas
      NotBlocked _ v      -> occurs' ctx v
      -- Blocked _ v@MetaV{} -> occurs' ctx v  -- does not help with issue 856
      Blocked _ v         -> occurs' Flex v
    where
      occurs' ctx v = do
        reportSDoc "tc.meta.occurs" 45 $
          text ("occursCheck " ++ prettyShow m ++ " (" ++ show ctx ++ ") of ") <+> prettyTCM v
        reportSDoc "tc.meta.occurs" 70 $
          nest 2 $ text $ show v
        case v of
          Var i es   -> do
            if (i `allowedVar` xs) then Var i <$> occ (weakly ctx) es else do
              -- if the offending variable is of singleton type,
              -- eta-expand it away
              isST <- isSingletonType =<< typeOfBV i
              case isST of
                -- cannot decide, blocked by meta-var
                Left mid -> patternViolation' 70 $ "Disallowed var " ++ show i ++ " not obviously singleton"
                -- not a singleton type
                Right Nothing -> -- abort Rigid turns this error into PatternErr
                  abort (strongly ctx) $ MetaCannotDependOn m (takeRelevant xs) i
                -- is a singleton type with unique inhabitant sv
                Right (Just sv) -> return $ sv `applyE` es
          Lam h f     -> Lam h <$> occ (leaveTop ctx) f
          Level l     -> Level <$> occ ctx l  -- stay in Top
          Lit l       -> return v
          DontCare v  -> dontCare <$> occurs red Irrel m (goIrrelevant xs) v
          Def d es    -> Def d <$> occDef d (leaveTop ctx) es
          Con c vs    -> Con c <$> occ (leaveTop ctx) vs  -- if strongly rigid, remain so
          Pi a b      -> uncurry Pi <$> occ (leaveTop ctx) (a,b)
          Sort s      -> Sort <$> occ (leaveTop ctx) s
          v@Shared{}  -> updateSharedTerm (occ ctx) v
          MetaV m' es -> do
              -- Check for loop
              --   don't fail hard on this, since we might still be on the top-level
              --   after some killing (Issue 442)
              --
              -- Andreas, 2013-02-18  Issue 795 demonstrates that a recursive
              -- occurrence of a meta could be solved by the identity.
              --   ? (Q A) = Q (? A)
              -- So, do not throw an error.
              -- I guess the error was there from times when occurrence check
              -- was done after the "lhs=linear variables" check, but now
              -- occurrence check comes first.
              -- WAS:
              -- when (m == m') $ if ctx == Top then patternViolation else
              --   abort ctx $ MetaOccursInItself m'
              when (m == m') $ patternViolation' 50 $ "occursCheck failed: Found " ++ prettyShow m

              -- The arguments of a meta are in a flexible position
              (MetaV m' <$> occurs red Flex m xs es) `catchError` \err -> do
                reportSDoc "tc.meta.kill" 25 $ vcat
                  [ text $ "error during flexible occurs check, we are " ++ show ctx
                  , text $ show err
                  ]
                case err of
                  -- On pattern violations try to remove offending
                  -- flexible occurrences (if not already in a flexible context)
                  PatternErr{} | ctx /= Flex -> do
                    reportSLn "tc.meta.kill" 20 $
                      "oops, pattern violation for " ++ prettyShow m'
                    -- Andreas, 2014-03-02, see issue 1070:
                    -- Do not prune when meta is projected!
                    caseMaybe (allApplyElims es) (throwError err) $ \ vs -> do
                      killResult <- prune m' vs (takeRelevant xs)
                      if (killResult == PrunedEverything)
                        -- after successful pruning, restart occurs check
                        then occurs red ctx m xs =<< instantiate (MetaV m' es)
                        else throwError err
                  _ -> throwError err
          where
            occ ctx v = occurs red ctx m xs v
            -- a data or record type constructor propagates strong occurrences
            -- since e.g. x = List x is unsolvable
            occDef d ctx vs = do
              metaOccurs m d
              ifM (isJust <$> isDataOrRecordType d)
                {-then-} (occ ctx vs)
                {-else-} (occ (defArgs red ctx) vs)

  metaOccurs m v = do
    v <- instantiate v
    case v of
      Var i vs   -> metaOccurs m vs
      Lam h f    -> metaOccurs m f
      Level l    -> metaOccurs m l
      Lit l      -> return ()
      DontCare v -> metaOccurs m v
      Def d vs   -> metaOccurs m d >> metaOccurs m vs
      Con c vs   -> metaOccurs m vs
      Pi a b     -> metaOccurs m (a,b)
      Sort s     -> metaOccurs m s
      Shared p   -> metaOccurs m $ derefPtr p
      MetaV m' vs | m == m' -> patternViolation' 50 $ "Found occurrence of " ++ prettyShow m
                  | otherwise -> metaOccurs m vs

instance Occurs QName where
  occurs red ctx m xs d = __IMPOSSIBLE__

  metaOccurs m d = whenM (defNeedsChecking d) $ do
    tallyDef d
    reportSLn "tc.meta.occurs" 30 $ "Checking for occurrences in " ++ show d
    metaOccurs m . theDef =<< ignoreAbstractMode (getConstInfo d)

instance Occurs Defn where
  occurs red ctx m xs def = __IMPOSSIBLE__

  metaOccurs m Axiom{}                      = return ()
  metaOccurs m Function{ funClauses = cls } = metaOccurs m cls
  -- since a datatype is isomorphic to the sum of its constructor types
  -- we check the constructor types
  metaOccurs m Datatype{ dataCons = cs }    = mapM_ mocc cs
    where mocc c = metaOccurs m . defType =<< getConstInfo c
  metaOccurs m Record{ recConHead = c }     = metaOccurs m . defType =<< getConstInfo (conName c)
  metaOccurs m Constructor{}                = return ()
  metaOccurs m Primitive{}                  = return ()
  metaOccurs m AbstractDefn{}               = __IMPOSSIBLE__

instance Occurs Clause where
  occurs red ctx m xs cl = __IMPOSSIBLE__

  metaOccurs m = metaOccurs m . clauseBody

instance Occurs Level where
  occurs red ctx m xs (Max as) = Max <$> occurs red ctx m xs as

  metaOccurs m (Max as) = metaOccurs m as

instance Occurs PlusLevel where
  occurs red ctx m xs l@ClosedLevel{} = return l
  occurs red ctx m xs (Plus n l) = Plus n <$> occurs red ctx' m xs l
    where ctx' | n == 0    = ctx
               | otherwise = leaveTop ctx  -- we leave Top only if we encounter at least one successor
  metaOccurs m ClosedLevel{} = return ()
  metaOccurs m (Plus n l)    = metaOccurs m l

instance Occurs LevelAtom where
  occurs red ctx m xs l = do
    l <- case red of
           YesUnfold -> reduce l
           NoUnfold  -> instantiate l
    case l of
      MetaLevel m' args -> do
        MetaV m' args <- ignoreSharing <$> occurs red ctx m xs (MetaV m' args)
        return $ MetaLevel m' args
      NeutralLevel r v  -> NeutralLevel r  <$> occurs red ctx m xs v
      BlockedLevel m' v -> BlockedLevel m' <$> occurs red Flex m xs v
      UnreducedLevel v  -> UnreducedLevel  <$> occurs red ctx m xs v

  metaOccurs m l = do
    l <- instantiate l
    case l of
      MetaLevel m' args -> metaOccurs m $ MetaV m' args
      NeutralLevel _ v  -> metaOccurs m v
      BlockedLevel _ v  -> metaOccurs m v
      UnreducedLevel v  -> metaOccurs m v


instance Occurs Type where
  occurs red ctx m xs (El s v) = uncurry El <$> occurs red ctx m xs (s,v)

  metaOccurs m (El s v) = metaOccurs m (s,v)

instance Occurs Sort where
  occurs red ctx m xs s = do
    s' <- case red of
            YesUnfold -> reduce s
            NoUnfold  -> instantiate s
    case s' of
      DLub s1 s2 -> uncurry DLub <$> occurs red (weakly ctx) m xs (s1,s2)
      Type a     -> Type <$> occurs red ctx m xs a
      Prop       -> return s'
      Inf        -> return s'
      SizeUniv   -> return s'

  metaOccurs m s = do
    s <- instantiate s
    case s of
      DLub s1 s2 -> metaOccurs m (s1,s2)
      Type a     -> metaOccurs m a
      Prop       -> return ()
      Inf        -> return ()
      SizeUniv   -> return ()

instance Occurs a => Occurs (Elim' a) where
  occurs red ctx m xs e@Proj{}  = return e
  occurs red ctx m xs (Apply a) = Apply <$> occurs red ctx m xs a

  metaOccurs m (Proj{} ) = return ()
  metaOccurs m (Apply a) = metaOccurs m a

instance (Occurs a, Subst t a) => Occurs (Abs a) where
  occurs red ctx m xs b@(Abs   s x) = Abs   s <$> underAbstraction_ b (occurs red ctx m (liftUnderAbs xs))
  occurs red ctx m xs b@(NoAbs s x) = NoAbs s <$> occurs red ctx m xs x

  metaOccurs m (Abs   s x) = metaOccurs m x
  metaOccurs m (NoAbs s x) = metaOccurs m x

instance Occurs a => Occurs (Arg a) where
  occurs red ctx m xs (Arg info x) | isIrrelevant info = Arg info <$>
    occurs red Irrel m (goIrrelevant xs) x
  occurs red ctx m xs (Arg info x) = Arg info <$>
    occurs red ctx m xs x

  metaOccurs m a = metaOccurs m (unArg a)

instance Occurs a => Occurs (Dom a) where
  occurs red ctx m xs (Dom info x) = Dom info <$> occurs red ctx m xs x
  metaOccurs m = metaOccurs m . unDom

instance (Occurs a, Occurs b) => Occurs (a,b) where
  occurs red ctx m xs (x,y) = (,) <$> occurs red ctx m xs x <*> occurs red ctx m xs y

  metaOccurs m (x,y) = metaOccurs m x >> metaOccurs m y

instance Occurs a => Occurs [a] where
  occurs red ctx m xs ys = mapM (occurs red ctx m xs) ys

  metaOccurs m ys = mapM_ (metaOccurs m) ys

instance Occurs a => Occurs (Maybe a) where
  occurs red ctx m mx my = traverse (occurs red ctx m mx) my

  metaOccurs m = maybe (return ()) (metaOccurs m)

-- * Getting rid of flexible occurrences

-- | @prune m' vs xs@ attempts to remove all arguments from @vs@ whose
--   free variables are not contained in @xs@.
--   If successful, @m'@ is solved by the new, pruned meta variable and we
--   return @True@ else @False@.
--
--   Issue 1147:
--   If any of the meta args @vs@ is matchable, e.g., is a constructor term,
--   we cannot prune, because the offending variables could be removed by
--   reduction for a suitable instantiation of the meta variable.
prune :: MetaId -> Args -> [Nat] -> TCM PruneResult
prune m' vs xs = do
  caseEitherM (runExceptT $ mapM (hasBadRigid xs) $ map unArg vs)
    (const $ return PrunedNothing) $ \ kills -> do
    reportSDoc "tc.meta.kill" 10 $ vcat
      [ text "attempting kills"
      , nest 2 $ vcat
        [ text "m'    =" <+> pretty m'
        -- , text "xs    =" <+> text (show xs)
        , text "xs    =" <+> prettyList (map (prettyTCM . var) xs)
        , text "vs    =" <+> prettyList (map prettyTCM vs)
        , text "kills =" <+> text (show kills)
        ]
      ]
    killArgs kills m'

-- | @hasBadRigid xs v = Just True@ iff one of the rigid variables in @v@ is not in @xs@.
--   Actually we can only prune if a bad variable is in the head. See issue 458.
--   Or in a non-eliminateable position (see succeed/PruningNonMillerPattern).
--
--   @hasBadRigid xs v = Nothing@ means that
--   we cannot prune at all as one of the meta args is matchable.
--   (See issue 1147.)
hasBadRigid :: [Nat] -> Term -> ExceptT () TCM Bool
hasBadRigid xs t = do
  -- We fail if we encounter a matchable argument.
  let failure = throwError ()
  tb <- liftTCM $ reduceB t
  let t = ignoreBlocking tb
  case ignoreSharing t of
    Var x _      -> return $ notElem x xs
    -- Issue 1153: A lambda has to be considered matchable.
    -- Lam _ v    -> hasBadRigid (0 : map (+1) xs) (absBody v)
    Lam _ v      -> failure
    DontCare v   -> hasBadRigid xs v
    -- The following types of arguments cannot be eliminated by a pattern
    -- match: data, record, Pi, levels, sorts
    -- Thus, their offending rigid variables are bad.
    v@(Def f es) -> ifNotM (isNeutral tb f es) failure $ {- else -} do
      es `rigidVarsNotContainedIn` xs
    -- Andreas, 2012-05-03: There is room for further improvement.
    -- We could also consider a defined f which is not blocked by a meta.
    Pi a b       -> (a,b) `rigidVarsNotContainedIn` xs
    Level v      -> v `rigidVarsNotContainedIn` xs
    Sort s       -> s `rigidVarsNotContainedIn` xs
    -- Since constructors can be eliminated by pattern-matching,
    -- offending variables under a constructor could be removed by
    -- the right instantiation of the meta variable.
    -- Thus, they are not rigid.
    Con c args   -> do
      ifM (liftTCM $ isEtaCon (conName c))
        -- in case of a record con, we can in principle prune
        -- (but not this argument; the meta could become a projection!)
        (and <$> mapM (hasBadRigid xs . unArg) args)  -- not andM, we need to force the exceptions!
        failure
    Lit{}        -> failure -- matchable
    MetaV{}      -> failure -- potentially matchable
    Shared p     -> __IMPOSSIBLE__

-- | Check whether a term @Def f es@ is finally stuck.
--   Currently, we give only a crude approximation.
isNeutral :: MonadTCM tcm => Blocked t -> QName -> Elims -> tcm Bool
isNeutral b f es = liftTCM $ do
  let yes = return True
      no  = return False
  def <- getConstInfo f
  if defMatchable def then no else do
  case theDef def of
    AbstractDefn -> yes
    Axiom{}    -> yes
    Datatype{} -> yes
    Record{}   -> yes
    Function{} -> case b of
      NotBlocked StuckOn{}   _ -> yes
      NotBlocked AbsurdMatch _ -> yes
      _                        -> no
    _          -> no

-- | Check whether any of the variables (given as de Bruijn indices)
--   occurs *definitely* in the term in a rigid position.
--   Reduces the term successively to remove variables in dead subterms.
--   This fixes issue 1386.
rigidVarsNotContainedIn :: (MonadTCM tcm, FoldRigid a) => a -> [Nat] -> tcm Bool
rigidVarsNotContainedIn v is = liftTCM $ do
  n0 <- getContextSize
  let -- allowed variables as de Bruijn levels
      levels = Set.fromList $ map (n0-1 -) is
      -- test if index is forbidden by converting it to level
      test i = do
        n <- getContextSize
        -- get de Bruijn level for i
        let l = n-1 - i
            -- If l >= n0 then it is a bound variable and can be
            -- ignored.  Otherwise, it has to be in the allowed levels.
            forbidden = l < n0 && not (l `Set.member` levels)
        when forbidden $
          reportSLn "tc.meta.kill" 20 $
            "found forbidden de Bruijn level " ++ show l
        return $ Any forbidden
  getAny <$> foldRigid test v

-- | Collect the *definitely* rigid variables in a monoid.
--   We need to successively reduce the expression to do this.

class FoldRigid a where
--  foldRigid :: (MonadTCM tcm, Monoid (tcm m)) => (Nat -> tcm m) -> a -> tcm m
  foldRigid :: (Monoid (TCM m)) => (Nat -> TCM m) -> a -> TCM m

instance FoldRigid Term where
  foldRigid f t = do
    b <- liftTCM $ reduceB t
    case ignoreSharing $ ignoreBlocking b of
      Var i es   -> f i `mappend` fold es
      Lam _ t    -> fold t
      Lit{}      -> mempty
      Def _ es   -> case b of
        Blocked{}                   -> mempty
        NotBlocked MissingClauses _ -> mempty
        _        -> fold es
      Con _ ts   -> fold ts
      Pi a b     -> fold (a,b)
      Sort s     -> fold s
      Level l    -> fold l
      MetaV{}    -> mempty
      DontCare{} -> mempty
      Shared{}   -> __IMPOSSIBLE__
    where fold = foldRigid f

instance FoldRigid Type where
  foldRigid f (El s t) = foldRigid f (s,t)

instance FoldRigid Sort where
  foldRigid f s =
    case s of
      Type l     -> fold l
      Prop       -> mempty
      Inf        -> mempty
      SizeUniv   -> mempty
      DLub s1 s2 -> fold (s1, s2)
    where fold = foldRigid f

instance FoldRigid Level where
  foldRigid f (Max ls) = foldRigid f ls

instance FoldRigid PlusLevel where
  foldRigid f ClosedLevel{} = mempty
  foldRigid f (Plus _ l)    = foldRigid f l

instance FoldRigid LevelAtom where
  foldRigid f l =
    case l of
      MetaLevel{} -> mempty
      NeutralLevel MissingClauses _ -> mempty
      NeutralLevel _              l -> fold l
      BlockedLevel _              l -> fold l
      UnreducedLevel              l -> fold l
    where fold = foldRigid f

instance (Subst t a, FoldRigid a) => FoldRigid (Abs a) where
  foldRigid f b = underAbstraction_ b $ foldRigid f

instance FoldRigid a => FoldRigid (Arg a) where
  foldRigid f a =
    case getRelevance a of
      Irrelevant -> mempty
      UnusedArg  -> mempty
      _          -> foldRigid f $ unArg a

instance FoldRigid a => FoldRigid (Dom a) where
  foldRigid f dom = foldRigid f $ unDom dom

instance FoldRigid a => FoldRigid (Elim' a) where
  foldRigid f (Apply a) = foldRigid f a
  foldRigid f Proj{}    = mempty

instance FoldRigid a => FoldRigid [a] where
  foldRigid f = foldMap $ foldRigid f

instance (FoldRigid a, FoldRigid b) => FoldRigid (a,b) where
  foldRigid f (a,b) = foldRigid f a `mappend` foldRigid f b


data PruneResult
  = NothingToPrune   -- ^ the kill list is empty or only @False@s
  | PrunedNothing    -- ^ there is no possible kill (because of type dep.)
  | PrunedSomething  -- ^ managed to kill some args in the list
  | PrunedEverything -- ^ all prescribed kills where performed
    deriving (Eq, Show)

-- | @killArgs [k1,...,kn] X@ prunes argument @i@ from metavar @X@ if @ki==True@.
--   Pruning is carried out whenever > 0 arguments can be pruned.
killArgs :: [Bool] -> MetaId -> TCM PruneResult
killArgs kills _
  | not (or kills) = return NothingToPrune  -- nothing to kill
killArgs kills m = do
  mv <- lookupMeta m
  allowAssign <- asks envAssignMetas
  if mvFrozen mv == Frozen || not allowAssign then return PrunedNothing else do
      -- Andreas 2011-04-26, we allow pruning in MetaV and MetaS
      let a = jMetaType $ mvJudgement mv
      TelV tel b <- telView' <$> instantiateFull a
      let args         = zip (telToList tel) (kills ++ repeat False)
          (kills', a') = killedType args b
      dbg kills' a a'
      -- If there is any prunable argument, perform the pruning
      if not (any unArg kills') then return PrunedNothing else do
        performKill kills' m a'
        -- Only successful if all occurrences were killed
        -- Andreas, 2011-05-09 more precisely, check that at least
        -- the in 'kills' prescribed kills were carried out
        return $ if (and $ zipWith implies kills $ map unArg kills')
                   then PrunedEverything
                   else PrunedSomething
  where
    implies :: Bool -> Bool -> Bool
    implies False _ = True
    implies True  x = x
    dbg kills' a a' =
      reportSDoc "tc.meta.kill" 10 $ vcat
        [ text "after kill analysis"
        , nest 2 $ vcat
          [ text "metavar =" <+> prettyTCM m
          , text "kills   =" <+> text (show kills)
          , text "kills'  =" <+> text (show kills')
          , text "oldType =" <+> prettyTCM a
          , text "newType =" <+> prettyTCM a'
          ]
        ]

-- | @killedType [((x1,a1),k1)..((xn,an),kn)] b = ([k'1..k'n],t')@
--   (ignoring @Dom@).  Let @t' = (xs:as) -> b@.
--   Invariant: @k'i == True@ iff @ki == True@ and pruning the @i@th argument from
--   type @b@ is possible without creating unbound variables.
--   @t'@ is type @t@ after pruning all @k'i==True@.
killedType :: [(Dom (ArgName, Type), Bool)] -> Type -> ([Arg Bool], Type)
killedType [] b = ([], b)
killedType ((arg@(Dom info _), kill) : kills) b
  | dontKill  = (Arg info False : args, mkPi arg b')
  | otherwise = (Arg info True  : args, strengthen __IMPOSSIBLE__ b')
  where
    (args, b') = killedType kills b
    dontKill = not kill || 0 `freeIn` b'

-- | Instantiate a meta variable with a new one that only takes
--   the arguments which are not pruneable.
performKill
  :: [Arg Bool]    -- ^ Arguments to old meta var in left to right order
                   --   with @Bool@ indicating whether they can be pruned.
  -> MetaId        -- ^ The old meta var to receive pruning.
  -> Type          -- ^ The pruned type of the new meta var.
  -> TCM ()
performKill kills m a = do
  mv <- lookupMeta m
  when (mvFrozen mv == Frozen) __IMPOSSIBLE__
  -- Arity of the old meta.
  let n = size kills
  -- The permutation of the new meta picks the arguments
  -- which are not pruned in left to right order
  -- (de Bruijn level order).
  let perm = Perm n
             [ i | (i, Arg _ False) <- zip [0..] kills ]
  m' <- newMeta (mvInfo mv) (mvPriority mv) perm
                (HasType __IMPOSSIBLE__ a)
  -- Andreas, 2010-10-15 eta expand new meta variable if necessary
  etaExpandMetaSafe m'
  let -- Arguments to new meta (de Bruijn indices)
      -- in left to right order.
      vars = [ Arg info (var i)
             | (i, Arg info False) <- zip (downFrom n) kills ]
      u       = MetaV m' $ map Apply vars
      -- Arguments to the old meta (just arg infos and name hints)
      -- in left to right order.
      tel     = map ("v" <$) kills
  dbg m' u
  assignTerm m tel u  -- m tel := u
  where
    dbg m' u = reportSDoc "tc.meta.kill" 10 $ vcat
      [ text "actual killing"
      , nest 2 $ vcat
        [ text "new meta:" <+> pretty m'
        , text "kills   :" <+> text (show kills)
        , text "inst    :" <+> pretty m <+> text ":=" <+> prettyTCM u
        ]
      ]
