{-# LANGUAGE CPP #-}

module Agda.TypeChecking.MetaVars.Occurs where

import Control.Applicative
import Control.Monad
import Control.Monad.Error

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free hiding (Occurrence(..))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Datatypes (isDataOrRecordType)
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size
import qualified Agda.Utils.VarSet as Set

import Agda.Utils.Impossible
#include "../../undefined.h"

data OccursCtx
  = Flex          -- ^ we are in arguments of a meta
  | Rigid         -- ^ we are not in arguments of a meta but a bound var
  | StronglyRigid -- ^ we are at the start or in the arguments of a constructor
  deriving (Eq, Show)

data UnfoldStrategy = YesUnfold | NoUnfold
  deriving (Eq, Show)

defArgs :: UnfoldStrategy -> OccursCtx -> OccursCtx
defArgs NoUnfold  _   = Flex
defArgs YesUnfold ctx = weakly ctx

unfold :: UnfoldStrategy -> Term -> TCM (Blocked Term)
unfold NoUnfold  v = NotBlocked <$> instantiate v
unfold YesUnfold v = reduceB v

-- | Leave the strongly rigid position.
weakly :: OccursCtx -> OccursCtx
weakly StronglyRigid = Rigid
weakly ctx = ctx

strongly :: OccursCtx -> OccursCtx
strongly Rigid = StronglyRigid
strongly ctx = ctx

abort :: OccursCtx -> TypeError -> TCM ()
abort Flex  _   = patternViolation -- throws a PatternErr, which leads to delayed constraint
abort Rigid err = patternViolation -- typeError err
abort StronglyRigid err = typeError err -- here, throw an uncatchable error (unsolvable constraint)

-- | Extended occurs check.
class Occurs t where
  occurs :: UnfoldStrategy -> OccursCtx -> MetaId -> [Nat] -> t -> TCM t

-- | When assigning @m xs := v@, check that @m@ does not occur in @v@
--   and that the free variables of @v@ are contained in @xs@.
occursCheck :: MetaId -> [Nat] -> Term -> TCM Term
occursCheck m xs v = liftTCM $ do
  let bailOnSelf v = do
        v <- instantiate v
        case v of
          -- Don't fail if trying to instantiate to just itself
          MetaV m' _ | m == m' -> patternViolation
          Level (Max [Plus 0 (MetaLevel m' _)])
                     | m == m' -> patternViolation
          _ -> return v

  v <- bailOnSelf v
  -- First try without normalising the term
  occurs NoUnfold  StronglyRigid m xs v `catchError` \_ -> do
  occurs YesUnfold StronglyRigid m xs v `catchError` \err -> case errError err of
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
               , text "since universe polymorphism is not enabled"
               , text "(use the --universe-polymorphism flag to enable)"
               ]
        )
        ( typeError . GenericError . show =<<
            fsep [ text ("Cannot instantiate the metavariable " ++ show m ++ " to")
                 , prettyTCM v
                 , text "since it contains the variable"
                 , enterClosure cl $ \_ -> prettyTCM (Var i [])
                 , text $ "which is not in scope of the metavariable"
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
        Var i vs   -> do         -- abort Rigid turns this error into PatternErr
          unless (i `elem` xs) $ abort (strongly ctx) $ MetaCannotDependOn m xs i
          Var i <$> occ (weakly ctx) vs
        Lam h f	    -> Lam h <$> occ ctx f
        Level l     -> Level <$> occ ctx l
        Lit l	    -> return v
        DontCare _  -> return v
        Def d vs    -> Def d <$> occDef d ctx vs
        Con c vs    -> Con c <$> occ ctx vs  -- if strongly rigid, remain so
        Pi a b	    -> uncurry Pi <$> occ ctx (a,b)
        Fun a b	    -> uncurry Fun <$> occ ctx (a,b)
        Sort s	    -> Sort <$> occ ctx s
        MetaV m' vs -> do
            -- Check for loop
            --   don't fail hard on this, since we might still be on the top-level
            --   after some killing (Issue 442)
            when (m == m') $ patternViolation

            -- The arguments of a meta are in a flexible position
            (MetaV m' <$> occurs red Flex m xs vs) `catchError` \err -> do
              reportSDoc "tc.meta.kill" 25 $ vcat
                [ text $ "error during flexible occurs check, we are " ++ show ctx
                , text $ show (errError err)
                ]
              case errError err of
                -- On pattern violations try to remove offending
                -- flexible occurrences (if not already in a flexible context)
                PatternErr{} | ctx /= Flex -> do
                      reportSLn "tc.meta.kill" 20 $
                        "oops, pattern violation for " ++ show m'
{-
                  let kills = map (hasBadRigid xs) $ map unArg vs
                  reportSLn "tc.meta.kill" 20 $
                    "oops, pattern violation for " ++ show m' ++ "\n" ++
                    "  kills: " ++ show kills
                  if not (or kills)
                    then throwError err
                    else do
                      reportSDoc "tc.meta.kill" 10 $ vcat
                        [ text "attempting kills"
                        , nest 2 $ vcat
                          [ text "m'    =" <+> text (show m')
                          , text "xs    =" <+> text (show xs)
                          , text "vs    =" <+> prettyList (map prettyTCM vs)
                          , text "kills =" <+> text (show kills)
                          ]
                        ]
                      ok <- killArgs kills m'
-}
                      killResult <- prune m' vs xs
                      if (killResult == PrunedEverything)
                        -- after successful pruning, restart occurs check
                        then occurs red ctx m xs =<< instantiate (MetaV m' vs)
                        else throwError err
                _ -> throwError err
        where
          occ ctx v = occurs red ctx m xs v
          -- a data or record type constructor propagates strong occurrences
          -- since e.g. x = List x is unsolvable
          occDef d ctx v = ifM (isDataOrRecordType d) (occ ctx v)
                                 (occ (defArgs red ctx) v)

instance Occurs Level where
  occurs red ctx m xs (Max as) = Max <$> occurs red ctx m xs as

instance Occurs PlusLevel where
  occurs red ctx m xs l@ClosedLevel{} = return l
  occurs red ctx m xs (Plus n l) = Plus n <$> occurs red ctx m xs l

instance Occurs LevelAtom where
  occurs red ctx m xs l = do
    l <- case red of
           YesUnfold -> reduce l
           NoUnfold  -> instantiate l
    case l of
      MetaLevel m' args -> do
        MetaV m' args <- occurs red ctx m xs (MetaV m' args)
        return $ MetaLevel m' args
      NeutralLevel v   -> NeutralLevel   <$> occurs red ctx m xs v
      BlockedLevel m v -> BlockedLevel m <$> occurs red Flex m xs v
      UnreducedLevel v -> UnreducedLevel <$> occurs red ctx m xs v

instance Occurs Type where
  occurs red ctx m xs (El s v) = uncurry El <$> occurs red ctx m xs (s,v)

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

instance Occurs a => Occurs (Abs a) where
  occurs red ctx m xs (Abs s x) = Abs s <$> occurs red ctx m (0 : map (1+) xs) x
  occurs red ctx m xs (NoAbs x) = NoAbs <$> occurs red ctx m xs x

instance Occurs a => Occurs (Arg a) where
  occurs red ctx m xs (Arg h r x) = Arg h r <$> occurs red ctx m xs x

instance (Occurs a, Occurs b) => Occurs (a,b) where
  occurs red ctx m xs (x,y) = (,) <$> occurs red ctx m xs x <*> occurs red ctx m xs y

instance Occurs a => Occurs [a] where
  occurs red ctx m xs ys = mapM (occurs red ctx m xs) ys

-- * Getting rid of flexible occurrences

-- | @prune m' vs xs@ attempts to remove all arguments from @vs@ whose
--   free variables are not contained in @xs@.
--   If successful, @m'@ is solved by the new, pruned meta variable and we
--   return @True@ else @False@.
prune :: MetaId -> Args -> [Nat] -> TCM PruneResult
prune m' vs xs = liftTCM $ do
  let kills = map (hasBadRigid xs) $ map unArg vs
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
hasBadRigid :: [Nat] -> Term -> Bool
hasBadRigid xs (Var v _) = notElem v xs
hasBadRigid xs _         = False
  -- not $ Set.isSubsetOf
  --   (rigidVars $ freeVars v)
  --   (Set.fromList xs)

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

-- | @killedType [((x1,a1),k1),...,((xn,an),kn)] b = ([k'1,...k'n],t')@
--   (ignoring @Arg@).  Let @t' = (xs:as) -> b@.
--   Invariant: @k'i==True@ iff $ki==True@ and pruning the @i@th argument form
--   type @@ is possible without creating unbound variables.
--   @t'@ is type @t@ after pruning all @k'i==True@.
killedType :: [(Arg (String, Type), Bool)] -> Type -> ([Arg Bool], Type)
killedType [] b = ([], b)
killedType ((arg, kill) : kills) b
  | dontKill  = (killed False : args, telePi (telFromList [arg]) b')
  | otherwise = (killed True  : args, subst __IMPOSSIBLE__ b')
  where
    (args, b') = killedType kills b
    killed k = fmap (const k) arg
    dontKill = not kill || 0 `freeIn` b'

-- The list starts with the last argument
performKill :: [Arg Bool] -> MetaId -> Type -> TCM ()
performKill kills m a = do
  mv <- lookupMeta m
  when (mvFrozen mv == Frozen) __IMPOSSIBLE__
  let perm = Perm (size kills)
             [ i | (i, Arg _ _ False) <- zip [0..] (reverse kills) ]
  m' <- newMeta (mvInfo mv) (mvPriority mv) perm
                (HasType __IMPOSSIBLE__ a)
  -- Andreas, 2010-10-15 eta expand new meta variable if necessary
  etaExpandMetaSafe m'
  let vars = reverse [ Arg h r (Var i []) | (i, Arg h r False) <- zip [0..] kills ]
      hs   = reverse [ argHiding a | a <- kills ]
      lam h b = Lam h (Abs "v" b)
      u       = foldr lam (MetaV m' vars) hs
  dbg m' u
  assignTerm m u
  return ()
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
