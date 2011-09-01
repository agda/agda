{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Telescope where

import Control.Applicative
import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

#include "../undefined.h"
import Agda.Utils.Impossible

-- TODO: use rename instead of substs
-- | The permutation should permute the corresponding telescope. (left-to-right list)
renameP :: Subst t => Permutation -> t -> t
renameP p = substs (renaming p)

-- | If @permute π : [a]Γ -> [a]Δ@, then @substs (renaming π) : Term Γ -> Term Δ@
renaming :: Permutation -> [Term]
renaming p = gamma'
  where
    n	   = size p
    gamma  = permute (reverseP $ invertP $ reverseP p) $ map var [0..]
    gamma' = gamma ++ map var [n..]
    var i  = Var i []

-- | If @permute π : [a]Γ -> [a]Δ@, then @substs (renamingR π) : Term Δ -> Term Γ@
renamingR :: Permutation -> [Term]
renamingR p@(Perm n _) = permute (reverseP p) (map var [0..]) ++ map var [n..]
  where
    var i  = Var (fromIntegral i) []

-- | Flatten telescope: (Γ : Tel) -> [Type Γ]
flattenTel :: Telescope -> [Arg Type]
flattenTel EmptyTel	     = []
flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

-- | Order a flattened telescope in the correct dependeny order: Γ ->
--   Permutation (Γ -> Γ~)
reorderTel :: [Arg Type] -> Maybe Permutation
reorderTel tel = topoSort comesBefore tel'
  where
    tel' = reverse $ zip [0..] $ reverse tel
    (i, _) `comesBefore` (_, a) = i `freeIn` unEl (unArg a) -- a tiny bit unsafe

reorderTel_ :: [Arg Type] -> Permutation
reorderTel_ tel = case reorderTel tel of
  Nothing -> __IMPOSSIBLE__
  Just p  -> p

-- | Unflatten: turns a flattened telescope into a proper telescope. Must be
--   properly ordered.
unflattenTel :: [String] -> [Arg Type] -> Telescope
unflattenTel []	  []	        = EmptyTel
unflattenTel (x : xs) (a : tel) = ExtendTel a' (Abs x tel')
  where
    tel' = unflattenTel xs tel
    a'   = substs rho a
    rho  = replicate (size tel + 1) __IMPOSSIBLE_TERM__ ++ map var [0..]
      where var i = Var i []
unflattenTel [] (_ : _) = __IMPOSSIBLE__
unflattenTel (_ : _) [] = __IMPOSSIBLE__

-- | Get the suggested names from a telescope
teleNames :: Telescope -> [String]
teleNames = map (fst . unArg) . telToList

teleArgNames :: Telescope -> [Arg String]
teleArgNames = map (fmap fst) . telToList

teleArgs :: Telescope -> Args
teleArgs tel =
  reverse [ Arg h r (Var i []) | (i, Arg h r _) <- zip [0..] $ reverse (telToList tel) ]

-- | A telescope split in two.
data SplitTel = SplitTel
      { firstPart  :: Telescope
      , secondPart :: Telescope
      , splitPerm  :: Permutation
      }

-- | Split a telescope into the part that defines the given variables and the
--   part that doesn't.
splitTelescope :: VarSet -> Telescope -> SplitTel
splitTelescope fv tel = SplitTel tel1 tel2 perm
  where
    names = teleNames tel
    ts0   = flattenTel tel

    n     = size tel

    -- We start with a rough split into fv and the rest. This will most likely
    -- not be correct so we patch it up later with reorderTel.
    is    = map (n - 1 -) $ filter (< n) $ reverse $ Set.toList fv
    isC   = [0..n - 1] \\ is
    perm0 = Perm n $ is ++ isC

    permuteTel p ts = renameP (reverseP p) (permute p ts)

    ts1   = permuteTel perm0 ts0

    perm1 = reorderTel_ ts1

    ts2   = permuteTel perm1 ts1

    perm  = composeP perm1 perm0

    tel'  = unflattenTel (permute perm names) ts2

    Perm _ js = perm
    m         = genericLength $ takeWhile (`notElem` is) (reverse js)
    (tel1, tel2) = telFromList -*- telFromList $ genericSplitAt (n - m) $ telToList tel'

{- Andreas 2010-10-01: this comment seems stale.  Where is the unsafe variant?
-- | A safe variant of telView.

OLD CODE:
telView :: MonadTCM tcm => Type -> tcm TelView
telView t = do
  t <- reduce t
  case unEl t of
    Pi a (Abs x b) -> absV a x   <$> telView b
    Fun a b	   -> absV a "_" <$> telView (raise 1 b)
    _		   -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t
-}
telView :: MonadTCM tcm => Type -> tcm TelView
telView = telViewUpTo (-1)

-- | @telViewUpTo n t@ takes off the first @n@ function types of @t@.
-- Takes off all if $n < 0$.
telViewUpTo :: MonadTCM tcm => Int -> Type -> tcm TelView
telViewUpTo 0 t = return $ TelV EmptyTel t
telViewUpTo n t = do
  t <- reduce t
  case unEl t of
    Pi a (Abs x b) -> absV a x   <$> telViewUpTo (n-1) b
    Fun a b	   -> absV a "_" <$> telViewUpTo (n-1) (raise 1 b)
    _		   -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

-- | A safe variant of piApply.

piApplyM :: MonadTCM tcm => Type -> Args -> tcm Type
piApplyM t []           = return t
piApplyM t (arg : args) = do
  t <- reduce t
  case (t, arg) of
    (El _ (Pi  _ b), arg) -> absApp b (unArg arg) `piApplyM` args
    (El _ (Fun _ b), _  ) -> b `piApplyM` args
    _                     -> __IMPOSSIBLE__
