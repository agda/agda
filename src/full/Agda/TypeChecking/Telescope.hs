{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Telescope where

import Control.Applicative
import Data.List

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free

import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

#include "../undefined.h"
import Agda.Utils.Impossible

-- | The permutation should permute the corresponding telescope. (left-to-right list)
renameP :: Subst t => Permutation -> t -> t
renameP p = applySubst (renaming p)

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renaming π) : Term Γ -> Term Δ@
renaming :: Permutation -> Substitution
renaming p = gamma'
  where
    n	   = size p
    gamma  = permute (reverseP $ invertP $ reverseP p) $ map var [0..]
    gamma' = gamma ++# raiseS n

-- | If @permute π : [a]Γ -> [a]Δ@, then @substs (renamingR π) : Term Δ -> Term Γ@
renamingR :: Permutation -> Substitution
renamingR p@(Perm n _) = permute (reverseP p) (map var [0..]) ++# raiseS n

-- | Flatten telescope: (Γ : Tel) -> [Type Γ]
flattenTel :: Telescope -> [Dom Type]
flattenTel EmptyTel	     = []
flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

-- | Order a flattened telescope in the correct dependeny order: Γ ->
--   Permutation (Γ -> Γ~)
reorderTel :: [Dom Type] -> Maybe Permutation
reorderTel tel = topoSort comesBefore tel'
  where
    tel' = zip (downFrom $ size tel) tel
    (i, _) `comesBefore` (_, a) = i `freeIn` unEl (unDom a) -- a tiny bit unsafe

reorderTel_ :: [Dom Type] -> Permutation
reorderTel_ tel = case reorderTel tel of
  Nothing -> __IMPOSSIBLE__
  Just p  -> p

-- | Unflatten: turns a flattened telescope into a proper telescope. Must be
--   properly ordered.
unflattenTel :: [String] -> [Dom Type] -> Telescope
unflattenTel []	  []	        = EmptyTel
unflattenTel (x : xs) (a : tel) = ExtendTel a' (Abs x tel')
  where
    tel' = unflattenTel xs tel
    a'   = applySubst rho a
    rho  = parallelS (replicate (size tel + 1) __IMPOSSIBLE_TERM__)
unflattenTel [] (_ : _) = __IMPOSSIBLE__
unflattenTel (_ : _) [] = __IMPOSSIBLE__

-- | Get the suggested names from a telescope
teleNames :: Telescope -> [String]
teleNames = map (fst . unDom) . telToList

teleArgNames :: Telescope -> [Arg String]
teleArgNames = map (argFromDom . fmap fst) . telToList

teleArgs :: Telescope -> Args
teleArgs tel = [ Common.Arg info (var i) | (i, Common.Dom info _) <- zip (downFrom $ size l) l ]
  where l = telToList tel

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

telView :: Type -> TCM TelView
telView = telViewUpTo (-1)

-- | @telViewUpTo n t@ takes off the first @n@ function types of @t@.
-- Takes off all if @n < 0@.
telViewUpTo :: Int -> Type -> TCM TelView
telViewUpTo n t = telViewUpTo' n (const True) t

-- | @telViewUpTo' n p t@ takes off $t$
--   the first @n@ (or arbitrary many if @n < 0@) function domains
--   as long as they satify @p@.
telViewUpTo' :: Int -> (Dom Type -> Bool) -> Type -> TCM TelView
telViewUpTo' 0 p t = return $ TelV EmptyTel t
telViewUpTo' n p t = do
  t <- reduce t
  case ignoreSharing $ unEl t of
    Pi a b | p a -> absV a (absName b) <$> telViewUpTo' (n - 1) p (absBody b)
    _            -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

-- | A safe variant of piApply.

piApplyM :: Type -> Args -> TCM Type
piApplyM t []           = return t
piApplyM t (arg : args) = do
  t <- reduce t
  case ignoreSharing $ unEl t of
    Pi  _ b -> absApp b (unArg arg) `piApplyM` args
    _       -> __IMPOSSIBLE__
