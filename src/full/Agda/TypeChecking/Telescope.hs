{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

module Agda.TypeChecking.Telescope where

import Control.Applicative
import Control.Monad (forM_, unless)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

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
  | OutputTypeVar
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
      Var n _  -> return OutputTypeVar
      -- Not base types:
      Con{}    -> __IMPOSSIBLE__
      Lam{}    -> __IMPOSSIBLE__
      Lit{}    -> __IMPOSSIBLE__
      Level{}  -> __IMPOSSIBLE__
      MetaV{}  -> __IMPOSSIBLE__
      Pi{}     -> __IMPOSSIBLE__
      Shared{} -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__

-- | The permutation should permute the corresponding telescope. (left-to-right list)
renameP :: Subst t a => Permutation -> a -> a
renameP p = applySubst (renaming p)

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renaming π) : Term Γ -> Term Δ@
renaming :: forall a. DeBruijn a => Permutation -> Substitution' a
renaming p = prependS __IMPOSSIBLE__ gamma $ raiseS $ size p
  where
    gamma :: [Maybe a]
    gamma = inversePermute p (debruijnVar :: Int -> a)
    -- gamma = safePermute (invertP (-1) p) $ map deBruijnVar [0..]

-- | If @permute π : [a]Γ -> [a]Δ@, then @applySubst (renamingR π) : Term Δ -> Term Γ@
renamingR :: DeBruijn a => Permutation -> Substitution' a
renamingR p@(Perm n _) = permute (reverseP p) (map debruijnVar [0..]) ++# raiseS n

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

-- | Recursively computes dependencies of a set of variables in a given
--   telescope. Any dependencies outside of the telescope are ignored.
varDependencies :: Telescope -> IntSet -> IntSet
varDependencies tel = allDependencies IntSet.empty
  where
    n  = size tel
    ts = flattenTel tel

    directDependencies :: Int -> IntSet
    directDependencies i = allFreeVars $ ts !! (n-1-i)

    allDependencies :: IntSet -> IntSet -> IntSet
    allDependencies =
      IntSet.foldr $ \j soFar ->
        if j >= n || j `IntSet.member` soFar
        then soFar
        else IntSet.insert j $ allDependencies soFar $ directDependencies j

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

    is    = varDependencies tel fv
    isC   = IntSet.fromList [0..(n-1)] `IntSet.difference` is

    perm  = Perm n $ map (n-1-) $ VarSet.toDescList is ++ VarSet.toDescList isC

    ts1   = renameP (reverseP perm) (permute perm ts0)

    tel'  = unflattenTel (permute perm names) ts1

    m     = size is
    (tel1, tel2) = telFromList -*- telFromList $ splitAt m $ telToList tel'

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
mustBePi t = ifNotPiType t __IMPOSSIBLE__ $ \ a b -> return (a,b)

-- | If the given type is a @Pi@, pass its parts to the first continuation.
--   If not (or blocked), pass the reduced type to the second continuation.
ifPi :: MonadTCM tcm => Term -> (Dom Type -> Abs Type -> tcm a) -> (Term -> tcm a) -> tcm a
ifPi t yes no = do
  t <- liftTCM $ reduce t
  case ignoreSharing t of
    Pi a b -> yes a b
    _      -> no t

-- | If the given type is a @Pi@, pass its parts to the first continuation.
--   If not (or blocked), pass the reduced type to the second continuation.
ifPiType :: MonadTCM tcm => Type -> (Dom Type -> Abs Type -> tcm a) -> (Type -> tcm a) -> tcm a
ifPiType (El s t) yes no = ifPi t yes (no . El s)

-- | If the given type is blocked or not a @Pi@, pass it reduced to the first continuation.
--   If it is a @Pi@, pass its parts to the second continuation.
ifNotPi :: MonadTCM tcm => Term -> (Term -> tcm a) -> (Dom Type -> Abs Type -> tcm a) -> tcm a
ifNotPi = flip . ifPi

-- | If the given type is blocked or not a @Pi@, pass it reduced to the first continuation.
--   If it is a @Pi@, pass its parts to the second continuation.
ifNotPiType :: MonadTCM tcm => Type -> (Type -> tcm a) -> (Dom Type -> Abs Type -> tcm a) -> tcm a
ifNotPiType = flip . ifPiType

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
    NoOutputTypeName -> typeError $ WrongInstanceDeclaration
    OutputTypeVar -> typeError $ WrongInstanceDeclaration

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
