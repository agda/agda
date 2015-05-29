{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

module Agda.TypeChecking.Telescope where

import Control.Applicative
import Control.Monad (forM_, unless)
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
import qualified Agda.Utils.VarSet as VarSet

#include "undefined.h"
import Agda.Utils.Impossible

data OutputTypeName
  = OutputTypeName QName
  | OutputTypeNameNotYetKnown
  | NoOutputTypeName

-- | Strips all Pi's and return the head definition name, if possible.
getOutputTypeName :: Type -> TCM OutputTypeName
getOutputTypeName t = do
  TelV tel t' <- telView t
  ifBlocked (unEl t') (\ _ _ -> return OutputTypeNameNotYetKnown) $ \ v ->
    case ignoreSharing v of
      -- Possible base types:
      Def n _  -> return $ OutputTypeName n
      Sort{}   -> return NoOutputTypeName
      Var{}    -> return NoOutputTypeName
      -- Not base types:
      Con{}    -> __IMPOSSIBLE__
      ExtLam{} -> __IMPOSSIBLE__
      Lam{}    -> __IMPOSSIBLE__
      Lit{}    -> __IMPOSSIBLE__
      Level{}  -> __IMPOSSIBLE__
      MetaV{}  -> __IMPOSSIBLE__
      Pi{}     -> __IMPOSSIBLE__
      Shared{} -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__

-- | The permutation should permute the corresponding telescope. (left-to-right list)
renameP :: Subst t => Permutation -> t -> t
renameP p = applySubst (renaming p)

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renaming π) : Term Γ -> Term Δ@
renaming :: Permutation -> Substitution
renaming p = prependS __IMPOSSIBLE__ gamma $ raiseS $ size p
  where
    gamma = safePermute (invertP (-1) p) $ map var [0..]

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renamingR π) : Term Δ -> Term Γ@
renamingR :: Permutation -> Substitution
renamingR p@(Perm n _) = permute (reverseP p) (map var [0..]) ++# raiseS n

-- | Flatten telescope: (Γ : Tel) -> [Type Γ]
flattenTel :: Telescope -> [Dom Type]
flattenTel EmptyTel          = []
flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

-- | Order a flattened telescope in the correct dependeny order: Γ ->
--   Permutation (Γ -> Γ~)
--
--   Since @reorderTel tel@ uses free variable analysis of type in @tel@,
--   the telescope should be 'normalise'd.
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
unflattenTel :: [ArgName] -> [Dom Type] -> Telescope
unflattenTel []   []            = EmptyTel
unflattenTel (x : xs) (a : tel) = ExtendTel a' (Abs x tel')
  where
    tel' = unflattenTel xs tel
    a'   = applySubst rho a
    rho  = parallelS (replicate (size tel + 1) __IMPOSSIBLE_TERM__)
unflattenTel [] (_ : _) = __IMPOSSIBLE__
unflattenTel (_ : _) [] = __IMPOSSIBLE__

-- | Get the suggested names from a telescope
teleNames :: Telescope -> [ArgName]
teleNames = map (fst . unDom) . telToList

teleArgNames :: Telescope -> [Arg ArgName]
teleArgNames = map (argFromDom . fmap fst) . telToList

teleArgs :: Telescope -> Args
teleArgs tel = [ Common.Arg info (var i) | (i, Common.Dom info _) <- zip (downFrom $ size l) l ]
  where l = telToList tel

-- | A telescope split in two.
data SplitTel = SplitTel
  { firstPart  :: Telescope
  , secondPart :: Telescope
  , splitPerm  :: Permutation
    -- ^ The permutation takes us from the original telescope to
    --   @firstPart ++ secondPart@.
  }

-- | Split a telescope into the part that defines the given variables and the
--   part that doesn't.
--
--   See 'Agda.TypeChecking.Tests.prop_splitTelescope'.
splitTelescope
  :: VarSet     -- ^ A set of de Bruijn indices.
  -> Telescope  -- ^ Original telescope.
  -> SplitTel   -- ^ @firstPart@ mentions the given variables, @secondPart@ not.
splitTelescope fv tel = SplitTel tel1 tel2 perm
  where
    names = teleNames tel
    ts0   = flattenTel tel
    n     = size tel

    -- We start with a rough split into fv and the rest. This will most likely
    -- not be correct so we patch it up later with reorderTel.

    -- Convert given de Bruijn indices into ascending list of de Bruijn levels.
    is    = map (n - 1 -) $ dropWhile (>= n) $ VarSet.toDescList fv
    -- Compute the complement (de Bruijn levels not mentioned in @fv@).
    isC   = [0..n - 1] \\ is
    perm0 = Perm n $ is ++ isC

    permuteTel p ts = renameP (reverseP p) (permute p ts)

    ts1   = permuteTel perm0 ts0

    perm1 = reorderTel_ ts1

    ts2   = permuteTel perm1 ts1

    perm  = composeP perm1 perm0

    tel'  = unflattenTel (permute perm names) ts2

    m            = length $ takeWhile (`notElem` is) $ reverse $ permPicks perm
    (tel1, tel2) = telFromList -*- telFromList $ splitAt (n - m) $ telToList tel'

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

-- | Decomposing a function type.

mustBePi :: MonadTCM tcm => Type -> tcm (Dom Type, Abs Type)
mustBePi t = liftTCM $ do
  t <- reduce t
  case ignoreSharing $ unEl t of
    Pi a b -> return (a, b)
    _      -> __IMPOSSIBLE__

-- | A safe variant of piApply.

piApplyM :: Type -> Args -> TCM Type
piApplyM t []           = return t
piApplyM t (arg : args) = do
  (_, b) <- mustBePi t
  absApp b (unArg arg) `piApplyM` args

piApply1 :: MonadTCM tcm => Type -> Term -> tcm Type
piApply1 t v = do
  (_, b) <- mustBePi t
  return $ absApp b v

-- | Given a function type, introduce its domain into
--   the context and continue with its codomain.

intro1 :: (MonadTCM tcm) => Type -> (Type -> tcm a) -> tcm a
intro1 t cont = do
  (a, b) <- mustBePi t
  underAbstraction a b cont

---------------------------------------------------------------------------
-- * Instance definitions
---------------------------------------------------------------------------

addTypedInstance :: QName -> Type -> TCM ()
addTypedInstance x t = do
  n <- getOutputTypeName t
  case n of
    OutputTypeName n -> addNamedInstance x n
    OutputTypeNameNotYetKnown -> addUnknownInstance x
    NoOutputTypeName -> typeError $ GenericError $ "Terms marked as eligible for instance search should end with a name"

resolveUnknownInstanceDefs :: TCM ()
resolveUnknownInstanceDefs = do
  anonInstanceDefs <- getAnonInstanceDefs
  clearAnonInstanceDefs
  forM_ anonInstanceDefs $ \ n -> addTypedInstance n =<< typeOfConst n

-- | Try to solve the instance definitions whose type is not yet known, report
--   an error if it doesn't work and return the instance table otherwise.
getInstanceDefs :: TCM InstanceTable
getInstanceDefs = do
  resolveUnknownInstanceDefs
  insts <- getAllInstanceDefs
  unless (null $ snd insts) $
    typeError $ GenericError $ "There are instances whose type is still unsolved"
  return $ fst insts
