{-# LANGUAGE CPP, FlexibleInstances #-}

module Agda.TypeChecking.MetaVars.Occurs where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free hiding (Occurrence(..))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Eliminators
import Agda.TypeChecking.Records
import Agda.TypeChecking.Datatypes (isDataOrRecordType, DataOrRecord(..))
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size
import qualified Agda.Utils.VarSet as Set

import Agda.Utils.Impossible
#include "../../undefined.h"

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
modifyOccursCheckDefs f = modify $ \ st ->
  st { stOccursCheckDefs = f (stOccursCheckDefs st) }

-- | Set the names of definitions to be looked at
--   to the defs in the current mutual block.
initOccursCheck :: MetaVariable -> TCM ()
initOccursCheck mv = modifyOccursCheckDefs . const =<<
  if (miMetaOccursCheck (mvInfo mv) == DontRunMetaOccursCheck)
   then return Data.Set.empty
   else maybe (return Data.Set.empty) lookupMutualBlock =<< asks envMutualBlock

-- | Is a def in the list of stuff to be checked?
defNeedsChecking :: QName -> TCM Bool
defNeedsChecking d = Data.Set.member d <$> gets stOccursCheckDefs

-- | Remove a def from the list of defs to be looked at.
tallyDef :: QName -> TCM ()
tallyDef d = modifyOccursCheckDefs $ \ s -> Data.Set.delete d s

data OccursCtx
  = Flex          -- ^ we are in arguments of a meta
  | Rigid         -- ^ we are not in arguments of a meta but a bound var
  | StronglyRigid -- ^ we are at the start or in the arguments of a constructor
  | Top           -- ^ we are at the term root (this turns into @StronglyRigid@)
  | Irrel         -- ^ we are in an irrelevant argument
  deriving (Eq, Show)

data UnfoldStrategy = YesUnfold | NoUnfold
  deriving (Eq, Show)

defArgs :: UnfoldStrategy -> OccursCtx -> OccursCtx
defArgs NoUnfold  _   = Flex
defArgs YesUnfold ctx = weakly ctx

unfold :: UnfoldStrategy -> Term -> TCM (Blocked Term)
unfold NoUnfold  v = NotBlocked <$> instantiate v
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

abort :: OccursCtx -> TypeError -> TCM a
abort Top           err = typeError err
abort StronglyRigid err = typeError err -- here, throw an uncatchable error (unsolvable constraint)
abort Flex  _ = patternViolation -- throws a PatternErr, which leads to delayed constraint
abort Rigid _ = patternViolation
abort Irrel _ = patternViolation

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
occursCheck :: MetaId -> Vars -> Term -> TCM Term
occursCheck m xs v = liftTCM $ do
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
          fsep [ text ("Refuse to construct infinite term by instantiating " ++ show m ++ " to")
               , prettyTCM =<< instantiateFull v
               ]
      MetaCannotDependOn _ _ i ->
        ifM ((&&) <$> isSortMeta m <*> (not <$> hasUniversePolymorphism))
        ( typeError . GenericError . show =<<
          fsep [ text ("Cannot instantiate the metavariable " ++ show m ++ " to")
               , prettyTCM v
               , text "since universe polymorphism is disabled"
               ]
        )
        ( typeError . GenericError . show =<<
            fsep [ text ("Cannot instantiate the metavariable " ++ show m ++ " to solution")
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
    case v of
      -- Don't fail on blocked terms or metas
      Blocked _ v  -> occurs' Flex v
      NotBlocked v -> occurs' ctx v
    where
      occurs' ctx v = case v of
        Var i vs   -> do
          if (i `allowedVar` xs) then Var i <$> occ (weakly ctx) vs else do
            -- if the offending variable is of singleton type,
            -- eta-expand it away
            isST <- isSingletonType =<< typeOfBV i
            case isST of
              -- cannot decide, blocked by meta-var
              Left mid -> patternViolation
              -- not a singleton type
              Right Nothing -> -- abort Rigid turns this error into PatternErr
                abort (strongly ctx) $ MetaCannotDependOn m (takeRelevant xs) i
              -- is a singleton type with unique inhabitant sv
              Right (Just sv) -> return $ sv `apply` vs
        Lam h f	    -> Lam h <$> occ (leaveTop ctx) f
        Level l     -> Level <$> occ ctx l  -- stay in Top
        Lit l	    -> return v
        DontCare v  -> DontCare <$> occurs red Irrel m (goIrrelevant xs) v
        Def d vs    -> Def d <$> occDef d (leaveTop ctx) vs
        Con c vs    -> Con c <$> occ (leaveTop ctx) vs  -- if strongly rigid, remain so
        Pi a b	    -> uncurry Pi <$> occ (leaveTop ctx) (a,b)
        Sort s	    -> Sort <$> occ (leaveTop ctx) s
        v@Shared{}  -> updateSharedTerm (occ ctx) v
        MetaV m' vs -> do
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
            {-
            when (m == m') $ if ctx == Top then patternViolation else
              abort ctx $ MetaOccursInItself m'
            -}
            when (m == m') patternViolation

            -- The arguments of a meta are in a flexible position
            (MetaV m' <$> occurs red Flex m xs vs) `catchError` \err -> do
              reportSDoc "tc.meta.kill" 25 $ vcat
                [ text $ "error during flexible occurs check, we are " ++ show ctx
                , text $ show err
                ]
              case err of
                -- On pattern violations try to remove offending
                -- flexible occurrences (if not already in a flexible context)
                PatternErr{} | ctx /= Flex -> do
                      reportSLn "tc.meta.kill" 20 $
                        "oops, pattern violation for " ++ show m'
                      killResult <- prune m' vs (takeRelevant xs)
                      if (killResult == PrunedEverything)
                        -- after successful pruning, restart occurs check
                        then occurs red ctx m xs =<< instantiate (MetaV m' vs)
                        else throwError err
                _ -> throwError err
        where
          occ ctx v = occurs red ctx m xs v
          -- a data or record type constructor propagates strong occurrences
          -- since e.g. x = List x is unsolvable
          occDef d ctx vs = do
            def <- theDef <$> getConstInfo d
            whenM (defNeedsChecking d) $ do
              tallyDef d
              metaOccurs m def
            if (defIsDataOrRecord def) then (occ ctx vs) else (occ (defArgs red ctx) vs)

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
      MetaV m' vs | m == m' -> patternViolation
                  | otherwise -> metaOccurs m vs

instance Occurs QName where
  occurs red ctx m xs d = __IMPOSSIBLE__

  metaOccurs m d = whenM (defNeedsChecking d) $ do
    tallyDef d
    metaOccurs m . theDef =<< getConstInfo d

instance Occurs Defn where
  occurs red ctx m xs def = __IMPOSSIBLE__

  metaOccurs m Axiom{}                      = return ()
  metaOccurs m Function{ funClauses = cls } = metaOccurs m cls
  -- since a datatype is isomorphic to the sum of its constructor types
  -- we check the constructor types
  metaOccurs m Datatype{ dataCons = cs }    = mapM_ mocc cs
    where mocc c = metaOccurs m . defType =<< getConstInfo c
  metaOccurs m Record{ recConType = v }     = metaOccurs m v
  metaOccurs m Constructor{}                = return ()
  metaOccurs m Primitive{}                  = return ()

instance Occurs Clause where
  occurs red ctx m xs cl = __IMPOSSIBLE__

  metaOccurs m (Clause { clauseBody = body }) = walk body
    where walk NoBody   = return ()
          walk (Body v) = metaOccurs m v
          walk (Bind b) = underAbstraction_ b walk

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
      NeutralLevel v   -> NeutralLevel   <$> occurs red ctx m xs v
      BlockedLevel m v -> BlockedLevel m <$> occurs red Flex m xs v
      UnreducedLevel v -> UnreducedLevel <$> occurs red ctx m xs v

  metaOccurs m l = do
    l <- instantiate l
    case l of
      MetaLevel m' args -> metaOccurs m (MetaV m' args)
      NeutralLevel v    -> metaOccurs m v
      BlockedLevel m v  -> metaOccurs m v
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

  metaOccurs m s = do
    s <- instantiate s
    case s of
      DLub s1 s2 -> metaOccurs m (s1,s2)
      Type a     -> metaOccurs m a
      Prop       -> return ()
      Inf        -> return ()



instance (Occurs a, Subst a) => Occurs (Abs a) where
  occurs red ctx m xs b@(Abs   s x) = Abs   s <$> underAbstraction_ b (occurs red ctx m (liftUnderAbs xs))
  occurs red ctx m xs b@(NoAbs s x) = NoAbs s <$> occurs red ctx m xs x

  metaOccurs m (Abs   s x) = metaOccurs m x
  metaOccurs m (NoAbs s x) = metaOccurs m x

instance Occurs a => Occurs (I.Arg a) where
  occurs red ctx m xs (Arg info x) | isArgInfoIrrelevant info = Arg info <$>
    occurs red Irrel m (goIrrelevant xs) x
  occurs red ctx m xs (Arg info x) = Arg info <$>
    occurs red ctx m xs x

  metaOccurs m a = metaOccurs m (unArg a)

instance Occurs a => Occurs (I.Dom a) where
  occurs red ctx m xs (Dom info x) = Dom info <$> occurs red ctx m xs x
  metaOccurs m = metaOccurs m . unDom

instance (Occurs a, Occurs b) => Occurs (a,b) where
  occurs red ctx m xs (x,y) = (,) <$> occurs red ctx m xs x <*> occurs red ctx m xs y

  metaOccurs m (x,y) = metaOccurs m x >> metaOccurs m y

instance Occurs a => Occurs [a] where
  occurs red ctx m xs ys = mapM (occurs red ctx m xs) ys

  metaOccurs m ys = mapM_ (metaOccurs m) ys

-- * Getting rid of flexible occurrences

-- | @prune m' vs xs@ attempts to remove all arguments from @vs@ whose
--   free variables are not contained in @xs@.
--   If successful, @m'@ is solved by the new, pruned meta variable and we
--   return @True@ else @False@.
prune :: MetaId -> Args -> [Nat] -> TCM PruneResult
prune m' vs xs = liftTCM $ do
  kills <- mapM (hasBadRigid xs) $ map unArg vs
  reportSDoc "tc.meta.kill" 10 $ vcat
    [ text "attempting kills"
    , nest 2 $ vcat
      [ text "m'    =" <+> text (show m')
      , text "xs    =" <+> text (show xs)
      , text "vs    =" <+> prettyList (map prettyTCM vs)
      , text "kills =" <+> text (show kills)
      ]
    ]
{- Andreas, 2011-05-11 REDUNDANT CODE
  reportSLn "tc.meta.kill" 20 $
    "attempting to prune meta " ++ show m' ++ "\n" ++
    "  kills: " ++ show kills
  if not (or kills)
    then return False -- nothing to kill
    else do
-}
  killArgs kills m'

-- | @hasBadRigid xs v = True@ iff one of the rigid variables in @v@ is not in @xs@.
--   Actually we can only prune if a bad variable is in the head. See issue 458.
--   Or in a non-eliminateable position (see succeed/PruningNonMillerPattern).
hasBadRigid :: [Nat] -> Term -> TCM Bool
hasBadRigid xs (Var x _)    = return $ notElem x xs
hasBadRigid xs (Lam _ v)    = hasBadRigid (0 : map (+1) xs) (absBody v)
hasBadRigid xs (DontCare v) = hasBadRigid xs v
-- The following types of arguments cannot be eliminated by a pattern
-- match: data, record, Pi, levels, sorts
-- Thus, their offending rigid variables are bad.
hasBadRigid xs v@(Def f vs) =
  ifM (isJust <$> isDataOrRecordType f) (return $ vs `rigidVarsNotContainedIn` xs) $ do
    elV <- elimView v
    case elV of
      VarElim x els -> return $ notElem x xs
      _             -> return $ False
  -- Andreas, 2012-05-03: There is room for further improvement.
  -- We could also consider a defined f which is not blocked by a meta.
hasBadRigid xs (Pi a b)     = return $ (a,b) `rigidVarsNotContainedIn` xs
hasBadRigid xs (Level v)    = return $ v `rigidVarsNotContainedIn` xs
hasBadRigid xs (Sort s)     = return $ s `rigidVarsNotContainedIn` xs
-- Since constructors can be eliminated by pattern-matching,
-- offending variables under a constructor could be removed by
-- the right instantiation of the meta variable.
-- Thus, they are not rigid.
hasBadRigid xs Con{}        = return $ False
hasBadRigid xs Lit{}        = return $ False -- no variables in Lit
hasBadRigid xs MetaV{}      = return $ False -- no rigid variables under a meta
hasBadRigid xs (Shared p)   = hasBadRigid xs (derefPtr p)

-- This could be optimized, by not computing the whole variable set
-- at once, but allow early failure
rigidVarsNotContainedIn :: Free a => a -> [Nat] -> Bool
rigidVarsNotContainedIn v xs =
  not $ Set.isSubsetOf
    (rigidVars $ freeVars v)
    (Set.fromList xs)


data PruneResult
  = NothingToPrune   -- ^ the kill list is empty or only @False@s
  | PrunedNothing    -- ^ there is no possible kill (because of type dep.)
  | PrunedSomething  -- ^ managed to kill some args in the list
  | PrunedEverything -- ^ all prescribed kills where performed
    deriving (Eq, Show)

-- | @killArgs [k1,...,kn] X@ prunes argument @i@ from metavar @X@ if @ki==True@.
--   Pruning is carried out whenever > 0 arguments can be pruned.
--   @True@ is only returned if all arguments could be pruned.
killArgs :: [Bool] -> MetaId -> TCM PruneResult
killArgs kills _
  | not (or kills) = return NothingToPrune  -- nothing to kill
killArgs kills m = do
  mv <- lookupMeta m
  if mvFrozen mv == Frozen then return PrunedNothing else do
{- Andreas 2011-04-26, allow pruning in MetaS
  case mvJudgement mv of
    IsSort _    -> return False
    HasType _ a -> do
-}
      let a = jMetaType $ mvJudgement mv
      TelV tel b <- telView' <$> instantiateFull a
      let args         = zip (telToList tel) (kills ++ repeat False)
          (kills', a') = killedType args b
      dbg kills' a a'
      -- If there is any prunable argument, perform the pruning
      if not (any unArg kills') then return PrunedNothing else do
        performKill (reverse kills') m a'
        -- Only successful if all occurrences were killed
        -- Andreas, 2011-05-09 more precisely, check that at least
        -- the in 'kills' prescribed kills were carried out
        -- OLD CODE: return (map unArg kills' == kills)
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
killedType :: [(I.Dom (String, Type), Bool)] -> Type -> ([I.Arg Bool], Type)
killedType [] b = ([], b)
killedType ((arg@(Dom info _), kill) : kills) b
  | dontKill  = (Arg info False : args, mkPi arg b') -- OLD: telePi (telFromList [arg]) b')
  | otherwise = (Arg info True  : args, subst __IMPOSSIBLE__ b')
  where
    (args, b') = killedType kills b
    dontKill = not kill || 0 `freeIn` b'

-- The list starts with the last argument
performKill :: [I.Arg Bool] -> MetaId -> Type -> TCM ()
performKill kills m a = do
  mv <- lookupMeta m
  when (mvFrozen mv == Frozen) __IMPOSSIBLE__
  let perm = Perm (size kills)
             [ i | (i, Arg _ False) <- zip [0..] (reverse kills) ]
  m' <- newMeta (mvInfo mv) (mvPriority mv) perm
                (HasType __IMPOSSIBLE__ a)
  -- Andreas, 2010-10-15 eta expand new meta variable if necessary
  etaExpandMetaSafe m'
  let vars = reverse [ Arg info (var i) | (i, Arg info False) <- zip [0..] kills ]
      lam b a = Lam (argInfo a) (Abs "v" b)
      u       = foldl' lam (MetaV m' vars) kills
{- OLD CODE
      hs   = reverse [ argHiding a | a <- kills ]
      lam h b = Lam h (Abs "v" b)
      u       = foldr lam (MetaV m' vars) hs
-}
  dbg m' u
  assignTerm m u
  where
    dbg m' u = reportSDoc "tc.meta.kill" 10 $ vcat
      [ text "actual killing"
      , nest 2 $ vcat
        [ text "new meta:" <+> text (show m')
        , text "kills   :" <+> text (show kills)
        , text "inst    :" <+> text (show m) <+> text ":=" <+> prettyTCM u
        ]
      ]

{-

  When hitting a meta variable:

  - Compute flex/rigid for its arguments
  - Compare to allowed variables
  - Mark arguments with rigid occurrences of disallowed
    variables for deletion
  - Attempt to delete marked arguments
  - We don't need to check for success, we can just
    continue occurs checking.
-}
