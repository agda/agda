
module Agda.TypeChecking.MetaVars.Occurs where

import Control.Applicative
import Control.Monad
import Control.Monad.Error
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.EtaContract
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size

import Agda.Utils.Impossible
#include "../../undefined.h"

data OccursCtx = Flex | Rigid
  deriving (Eq)

abort :: OccursCtx -> TypeError -> TCM ()
abort Flex  _   = patternViolation
abort Rigid err = typeError err

-- | Extended occurs check.
class Occurs t where
  occurs :: OccursCtx -> MetaId -> [Nat] -> t -> TCM t

occursCheck :: MonadTCM tcm => MetaId -> [Nat] -> Term -> tcm Term
occursCheck m xs v = liftTCM $ do
  v <- instantiate v
  case v of
    -- Don't fail if trying to instantiate to just itself
    MetaV m' _        | m == m' -> patternViolation
    Sort (MetaS m' _) | m == m' -> patternViolation
    _                           ->
                              -- Produce nicer error messages
      occurs Rigid m xs v `catchError` \err -> case errError err of
        TypeError _ cl -> case clValue cl of
          MetaOccursInItself{} ->
            typeError . GenericError . show =<<
              fsep [ text ("Refuse to construct infinite term by instantiating " ++ show m ++ " to")
                   , prettyTCM v
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
                   , text $ "which " ++ show m ++ " cannot depend on"
                   ]
            )
          _ -> throwError err
        _ -> throwError err

instance Occurs Term where
  occurs ctx m xs v = do
    v <- reduceB v
    case v of
      -- Don't fail on blocked terms or metas
      Blocked _ v  -> occurs' Flex v
      NotBlocked v -> occurs' ctx v
    where
      occurs' ctx v = case v of
        Var i vs   -> do
          unless (i `elem` xs) $ abort ctx $ MetaCannotDependOn m xs i
          Var i <$> occ vs
        Lam h f	    -> Lam h <$> occ f
        Lit l	    -> return v
        Def c vs    -> Def c <$> occ vs
        Con c vs    -> Con c <$> occ vs
        Pi a b	    -> uncurry Pi <$> occ (a,b)
        Fun a b	    -> uncurry Fun <$> occ (a,b)
        Sort s	    -> Sort <$> occ s
        MetaV m' vs -> do
            -- Check for loop
            when (m == m') $ abort ctx $ MetaOccursInItself m

            -- The arguments are in a flexible position
            (MetaV m' <$> occurs Flex m xs vs) `catchError` \err -> do
              case errError err of
                -- On pattern violations try to remove offending
                -- flexible occurrences (if in a rigid context)
                PatternErr{} | ctx == Rigid -> do
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
                      if ok
                        then occurs Rigid m xs =<< instantiate (MetaV m' vs)
                        else throwError err
                _ -> throwError err
        where
          occ x = occurs ctx m xs x

instance Occurs Type where
  occurs ctx m xs (El s v) = uncurry El <$> occurs ctx m xs (s,v)

instance Occurs Sort where
  occurs ctx m xs s = do
    s' <- reduce s
    case s' of
      MetaS m' args -> do
        when (m == m') $ abort ctx $ MetaOccursInItself m
        MetaS m' <$> occurs Flex m xs args
      Lub s1 s2  -> uncurry Lub <$> occurs ctx m xs (s1,s2)
      DLub s1 s2 -> uncurry DLub <$> occurs ctx m xs (s1, s2)
      Suc s      -> Suc <$> occurs ctx m xs s
      Type a     -> Type <$> occurs ctx m xs a
      Prop       -> return s'
      Inf        -> return s'

instance Occurs a => Occurs (Abs a) where
  occurs ctx m xs (Abs s x) = Abs s <$> occurs ctx m (0 : map (1+) xs) x

instance Occurs a => Occurs (Arg a) where
  occurs ctx m xs (Arg h r x) = Arg h r <$> occurs ctx m xs x

instance (Occurs a, Occurs b) => Occurs (a,b) where
  occurs ctx m xs (x,y) = (,) <$> occurs ctx m xs x <*> occurs ctx m xs y

instance Occurs a => Occurs [a] where
  occurs ctx m xs ys = mapM (occurs ctx m xs) ys

-- Getting rid of flexible occurrences --

hasBadRigid :: [Nat] -> Term -> Bool
hasBadRigid xs v =
  not $ Set.isSubsetOf
    (rigidVars $ freeVars v)
    (Set.fromList xs)

killArgs :: [Bool] -> MetaId -> TCM Bool
killArgs kills _
  | not (or kills) = return False  -- nothing to kill
killArgs kills m = do
  mv <- lookupMeta m
  case mvJudgement mv of
    IsSort _    -> return False
    HasType _ a -> do
      TelV tel b <- telView' <$> instantiateFull a
      let args         = zip (telToList tel) (kills ++ repeat False)
          (kills', a') = killedType args b
      dbg kills' a a'
      when (any unArg kills') $ performKill (reverse kills') m a'
      -- Only successful if all occurrences were killed
      return (map unArg kills' == kills)
  where
    dbg kills' a a' =
      reportSDoc "tc.meta.kill" 10 $ vcat
        [ text "after kill analysis"
        , nest 2 $ vcat
          [ text "kills'  =" <+> text (show kills')
          , text "oldType =" <+> prettyTCM a
          , text "newType =" <+> prettyTCM a'
          ]
        ]

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
  let perm = Perm (size kills)
             [ i | (i, Arg _ _ False) <- zip [0..] (reverse kills) ]
  m' <- newMeta (mvInfo mv) (mvPriority mv) perm (HasType undefined a)
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

