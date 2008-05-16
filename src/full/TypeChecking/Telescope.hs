{-# OPTIONS -cpp #-}

module TypeChecking.Telescope where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List ((\\))

import Syntax.Common
import Syntax.Internal

import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.Free

import Utils.Permutation
import Utils.Size
import Utils.Tuple

#include "../undefined.h"
import Utils.Impossible

-- | The permutation should permute the corresponding telescope. (left-to-right list)
rename :: Subst t => Permutation -> t -> t
rename p = substs (renaming p)

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
    var i  = Var i []

-- | Flatten telescope: (Γ : Tel) -> [Type Γ]
flattenTel :: Telescope -> [Arg Type]
flattenTel EmptyTel	     = []
flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

-- | Order a flattened telescope in the correct dependeny order: Γ ->
--   Permutation (Γ -> Γ~)
reorderTel :: [Arg Type] -> Permutation
reorderTel tel = case topoSort comesBefore tel' of
  Nothing -> __IMPOSSIBLE__
  Just p  -> p
  where
    tel' = reverse $ zip [0..] $ reverse tel
    (i, _) `comesBefore` (_, a) = i `freeIn` a

-- | Unflatten: turns a flattened telescope into a proper telescope. Must be
--   properly ordered.
unflattenTel :: [String] -> [Arg Type] -> Telescope
unflattenTel []	  []	        = EmptyTel
unflattenTel (x : xs) (a : tel) = ExtendTel a' (Abs x tel')
  where
    tel' = unflattenTel xs tel
    a'   = substs rho a
    rho  = replicate (size tel + 1) __IMPOSSIBLE__ ++ map var [0..]
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
  reverse [ Arg h (Var i []) | (i, Arg h _) <- zip [0..] $ reverse (telToList tel) ]

-- | A telescope split in two.
data SplitTel = SplitTel
      { firstPart  :: Telescope
      , secondPart :: Telescope
      , splitPerm  :: Permutation
      }

-- | Split a telescope into the part that defines the given variables and the
--   part that doesn't.
splitTelescope :: Set Nat -> Telescope -> SplitTel
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

    permuteTel p ts = rename (reverseP p) (permute p ts)

    ts1   = permuteTel perm0 ts0

    perm1 = reorderTel ts1

    ts2   = permuteTel perm1 ts1

    perm  = composeP perm1 perm0

    tel'  = unflattenTel (permute perm names) ts2

    Perm _ js = perm
    m         = length $ takeWhile (`notElem` is) (reverse js)
    (tel1, tel2) = telFromList -*- telFromList $ splitAt (n - m) $ telToList tel'

