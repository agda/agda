{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Telescope where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad (unless, guard)

import Data.Foldable (forM_)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position

import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

#include "undefined.h"
import Agda.Utils.Impossible

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

teleArgs :: (DeBruijn a) => Telescope -> [Arg a]
teleArgs tel =
  [ Arg info (deBruijnVar i)
  | (i, Dom {domInfo = info, unDom = (n,_)}) <- zip (downFrom $ size l) l ]
  where l = telToList tel

withNamedArgsFromTel :: [a] -> Telescope -> [NamedArg a]
xs `withNamedArgsFromTel` tel =
  [ Arg info (Named (Just $ Ranged noRange $ argNameToString name) x)
  | (x, Dom {domInfo = info, unDom = (name,_)}) <- zip xs l ]
  where l = telToList tel

teleNamedArgs :: (DeBruijn a) => Telescope -> [NamedArg a]
teleNamedArgs tel =
  [ Arg info (Named (Just $ Ranged noRange $ argNameToString name) (deBruijnVar i))
  | (i, Dom {domInfo = info, unDom = (name,_)}) <- zip (downFrom $ size l) l ]
  where l = telToList tel

-- | A variant of `teleNamedArgs` which takes the argument names (and the argument info)
--   from the first telescope and the variable names from the second telescope.
--
--   Precondition: the two telescopes have the same length.
tele2NamedArgs :: (DeBruijn a) => Telescope -> Telescope -> [NamedArg a]
tele2NamedArgs tel0 tel =
  [ Arg info (Named (Just $ Ranged noRange $ argNameToString argName) (debruijnNamedVar varName i))
  | (i, Dom{domInfo = info, unDom = (argName,_)}, Dom{unDom = (varName,_)}) <- zip3 (downFrom $ size l) l0 l ]
  where
  l  = telToList tel
  l0 = telToList tel0

-- | Split the telescope at the specified position.
splitTelescopeAt :: Int -> Telescope -> (Telescope,Telescope)
splitTelescopeAt n tel
  | n <= 0    = (EmptyTel, tel)
  | otherwise = splitTelescopeAt' n tel
    where
      splitTelescopeAt' _ EmptyTel          = (EmptyTel,EmptyTel)
      splitTelescopeAt' 1 (ExtendTel a tel) = (ExtendTel a (tel $> EmptyTel), absBody tel)
      splitTelescopeAt' m (ExtendTel a tel) = (ExtendTel a (tel $> tel'), tel'')
        where
          (tel', tel'') = splitTelescopeAt (m - 1) $ absBody tel

-- | Permute telescope: permutes or drops the types in the telescope according
--   to the given permutation. Assumes that the permutation preserves the
--   dependencies in the telescope.
--
--   For example (Andreas, 2016-12-18, issue #2344):
--   @
--     tel                     = (A : Set) (X : _18 A) (i : Fin (_m_23 A X))
--     tel (de Bruijn)         = 2:Set, 1:_18 @0, 0:Fin(_m_23 @1 @0)
--     flattenTel tel          = 2:Set, 1:_18 @0, 0:Fin(_m_23 @1 @0) |- [ Set, _18 @2, Fin (_m_23 @2 @1) ]
--     perm                    = 0,1,2 -> 0,1  (picks the first two)
--     renaming _ perm         = [var 0, var 1, error]  -- THE WRONG RENAMING!
--     renaming _ (flipP perm) = [error, var 1, var 0]  -- The correct renaming!
--     apply to flattened tel  = ... |- [ Set, _18 @1, Fin (_m_23 @1 @0) ]
--     permute perm it         = ... |- [ Set, _18 @1 ]
--     unflatten (de Bruijn)   = 1:Set, 0: _18 @0
--     unflatten               = (A : Set) (X : _18 A)
--  @
permuteTel :: Permutation -> Telescope -> Telescope
permuteTel perm tel =
  let names = permute perm $ teleNames tel
      types = permute perm $ renameP __IMPOSSIBLE__ (flipP perm) $ flattenTel tel
  in  unflattenTel names types

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

    ts1   = renameP __IMPOSSIBLE__ (reverseP perm) (permute perm ts0)

    tel'  = unflattenTel (permute perm names) ts1

    m     = size is
    (tel1, tel2) = telFromList -*- telFromList $ splitAt m $ telToList tel'

-- | As splitTelescope, but fails if any additional variables or reordering
--   would be needed to make the first part well-typed.
splitTelescopeExact
  :: [Int]          -- ^ A list of de Bruijn indices
  -> Telescope      -- ^ The telescope to split
  -> Maybe SplitTel -- ^ @firstPart@ mentions the given variables in the given order,
                    --   @secondPart@ contains all other variables
splitTelescopeExact is tel = guard ok $> SplitTel tel1 tel2 perm
  where
    names = teleNames tel
    ts0   = flattenTel tel
    n     = size tel

    checkDependencies :: IntSet -> [Int] -> Bool
    checkDependencies soFar []     = True
    checkDependencies soFar (j:js) = ok && checkDependencies (IntSet.insert j soFar) js
      where
        fv' = allFreeVars $ ts0 !! (n-1-j)
        fv  = fv' `IntSet.intersection` IntSet.fromAscList [ 0 .. n-1 ]
        ok  = fv `IntSet.isSubsetOf` soFar

    ok    = all (<n) is && checkDependencies IntSet.empty is

    isC   = downFrom n List.\\ is

    perm  = Perm n $ map (n-1-) $ is ++ isC

    ts1   = renameP __IMPOSSIBLE__ (reverseP perm) (permute perm ts0)

    tel'  = unflattenTel (permute perm names) ts1

    m     = size is
    (tel1, tel2) = telFromList -*- telFromList $ splitAt m $ telToList tel'

instantiateTelescopeN
  :: Telescope    -- ^ ⊢ Γ
  -> [(Int,Term)] -- ^ Γ ⊢ var k_i : A_i ascending order, Γ ⊢ u_i : A_i
  -> Maybe (Telescope,    -- ⊢ Γ'
            Substitution) -- Γ' ⊢ σ : Γ
instantiateTelescopeN tel []         = return (tel, IdS)
instantiateTelescopeN tel ((k,t):xs) = do
  (tel', sigma, _) <- instantiateTelescope tel k t
  (tel'', sigma')  <- instantiateTelescopeN tel' (map (subtract 1 -*- applyPatSubst sigma) xs)
  return (tel'', applyPatSubst sigma sigma')

-- | Try to instantiate one variable in the telescope (given by its de Bruijn
--   level) with the given value, returning the new telescope and a
--   substitution to the old one. Returns Nothing if the given value depends
--   (directly or indirectly) on the variable.
instantiateTelescope
  :: Telescope -- ^ ⊢ Γ
  -> Int       -- ^ Γ ⊢ var k : A
  -> Term      -- ^ Γ ⊢ u : A
  -> Maybe (Telescope,           -- ⊢ Γ'
            PatternSubstitution, -- Γ' ⊢ σ : Γ
            Permutation)         -- Γ  ⊢ flipP ρ : Γ'
instantiateTelescope tel k u = guard ok $> (tel', sigma, rho)
  where
    names = teleNames tel
    ts0   = flattenTel tel
    n     = size tel
    j     = n-1-k

    -- is0 is the part of Γ that is needed to type u
    is0   = varDependencies tel $ allFreeVars u
    -- is1 is the rest of Γ (minus the variable we are instantiating)
    is1   = IntSet.delete j $
              IntSet.fromAscList [ 0 .. n-1 ] `IntSet.difference` is0
    -- we work on de Bruijn indices, so later parts come first
    is    = IntSet.toAscList is1 ++ IntSet.toAscList is0

    -- if u depends on var j, we cannot instantiate
    ok    = not $ j `IntSet.member` is0

    perm  = Perm n $ is    -- works on de Bruijn indices
    rho   = reverseP perm  -- works on de Bruijn levels

    u1    = renameP __IMPOSSIBLE__ perm u -- Γ' ⊢ u1 : A'
    us    = map (\i -> fromMaybe (dotP u1) (deBruijnVar <$> List.findIndex (i ==) is)) [ 0 .. n-1 ]
    sigma = us ++# raiseS (n-1)

    ts1   = permute rho $ applyPatSubst sigma ts0
    tel'  = unflattenTel (permute rho names) ts1

-- | Try to eta-expand one variable in the telescope (given by its de Bruijn
--   level)
expandTelescopeVar
  :: Telescope  -- Γ = Γ₁(x : D pars)Γ₂
  -> Int        -- k = size Γ₁
  -> Telescope  -- Γ₁ ⊢ Δ
  -> ConHead    -- Γ₁ ⊢ c : Δ → D pars
  -> ( Telescope            -- Γ' = Γ₁ΔΓ₂[x ↦ c Δ]
     , PatternSubstitution) -- Γ' ⊢ ρ : Γ
expandTelescopeVar gamma k delta c = (tel', rho)
  where
    (ts1,a:ts2) = fromMaybe __IMPOSSIBLE__ $
                    splitExactlyAt k $ telToList gamma

    cpi         = noConPatternInfo
      { conPRecord = Just PatOSystem
      , conPType   = Just $ snd <$> argFromDom a
      , conPLazy   = True
      }
    cargs       = map (setOrigin Inserted) $ teleNamedArgs delta
    cdelta      = ConP c cpi cargs                    -- Γ₁Δ ⊢ c Δ : D pars
    rho0        = consS cdelta $ raiseS (size delta)  -- Γ₁Δ ⊢ ρ₀ : Γ₁(x : D pars)
    rho         = liftS (size ts2) rho0               -- Γ₁ΔΓ₂ρ₀ ⊢ ρ : Γ₁(x : D pars)Γ₂

    gamma1      = telFromList ts1
    gamma2'     = applyPatSubst rho0 $ telFromList ts2

    tel'        = gamma1 `abstract` (delta `abstract` gamma2')

-- | Gather leading Πs of a type in a telescope.
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
  case unEl t of
    Pi a b | p a -> absV a (absName b) <$> telViewUpTo' (n - 1) p (absBody b)
    _            -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

telViewPath :: Type -> TCM TelView
telViewPath = telViewUpToPath (-1)

-- | @telViewUpToPath n t@ takes off $t$
--   the first @n@ (or arbitrary many if @n < 0@) function domains or Path types.
telViewUpToPath :: Int -> Type -> TCM TelView
telViewUpToPath 0 t = return $ TelV EmptyTel t
telViewUpToPath n t = do
  vt <- pathViewAsPi $ t
  case vt of
    Left (a,b)     -> absV a (absName b) <$> telViewUpToPath (n - 1) (absBody b)
    Right (El _ t) | Pi a b <- t
                   -> absV a (absName b) <$> telViewUpToPath (n - 1) (absBody b)
    Right t        -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

-- | [[ (i,(x,y)) ]] = [(i=0) -> x, (i=1) -> y]
type Boundary = [(Term,(Term,Term))]

-- | Like @telViewUpToPath@ but also returns the @Boundary@ expected
-- by the Path types encountered. The boundary terms live in the
-- telescope given by the @TelView@.
telViewUpToPathBoundary :: Int -> Type -> TCM (TelView,Boundary)
telViewUpToPathBoundary 0 t = return $ (TelV EmptyTel t,[])
telViewUpToPathBoundary n t = do
  vt <- pathViewAsPi' $ t
  case vt of
    Left ((a,b),xy) -> addEndPoints xy . absV a (absName b) <$> telViewUpToPathBoundary (n - 1) (absBody b)
    Right (El _ t) | Pi a b <- t
                   -> absV a (absName b) <$> telViewUpToPathBoundary (n - 1) (absBody b)
    _              -> return $ (TelV EmptyTel t,[])
  where
    absV a x (TelV tel t, cs) = (TelV (ExtendTel a (Abs x tel)) t, cs)
    addEndPoints xy (telv@(TelV tel _),cs) = (telv, (var $ size tel - 1, xyInTel):cs)
      where
       xyInTel = raise (size tel) xy `apply` drop 1 (teleArgs tel)

pathViewAsPi :: Type -> TCM (Either (Dom Type, Abs Type) Type)
pathViewAsPi t = either (Left . fst) Right <$> pathViewAsPi' t

pathViewAsPi' :: Type -> TCM (Either ((Dom Type, Abs Type), (Term,Term)) Type)
pathViewAsPi' t = do
  pathViewAsPi'whnf =<< reduce t

pathViewAsPi'whnf :: Type -> TCM (Either ((Dom Type, Abs Type), (Term,Term)) Type)
pathViewAsPi'whnf t = do
  t <- pathView t
  case t of
    PathType s l p a x y -> do
      let name | Lam _ (Abs n _) <- unArg a = n
               | otherwise = "i"
      i <- El Inf <$> primInterval
      return $ Left $ ((defaultDom $ i, Abs name $ El (raise 1 s) $ raise 1 (unArg a) `apply` [defaultArg $ var 0]), (unArg x, unArg y))

    OType t    -> return $ Right t

-- | returns Left (a,b) in case the type is @Pi a b@ or @PathP b _ _@
--   assumes the type is in whnf.
piOrPath :: Type -> TCM (Either (Dom Type, Abs Type) Type)
piOrPath t = do
  t <- pathViewAsPi'whnf t
  case t of
    Left (p,_) -> return $ Left p
    Right (El _ (Pi a b)) -> return $ Left (a,b)
    Right t -> return $ Right t

isPath :: Type -> TCM (Maybe (Dom Type, Abs Type))
isPath t = either Just (const Nothing) <$> pathViewAsPi t

-- | Decomposing a function type.

mustBePi :: MonadReduce m => Type -> m (Dom Type, Abs Type)
mustBePi t = ifNotPiType t __IMPOSSIBLE__ $ \ a b -> return (a,b)

-- | If the given type is a @Pi@, pass its parts to the first continuation.
--   If not (or blocked), pass the reduced type to the second continuation.
ifPi :: MonadReduce m => Term -> (Dom Type -> Abs Type -> m a) -> (Term -> m a) -> m a
ifPi t yes no = do
  t <- reduce t
  case t of
    Pi a b -> yes a b
    _      -> no t

-- | If the given type is a @Pi@, pass its parts to the first continuation.
--   If not (or blocked), pass the reduced type to the second continuation.
ifPiType :: MonadReduce m => Type -> (Dom Type -> Abs Type -> m a) -> (Type -> m a) -> m a
ifPiType (El s t) yes no = ifPi t yes (no . El s)

-- | If the given type is blocked or not a @Pi@, pass it reduced to the first continuation.
--   If it is a @Pi@, pass its parts to the second continuation.
ifNotPi :: MonadReduce m => Term -> (Term -> m a) -> (Dom Type -> Abs Type -> m a) -> m a
ifNotPi = flip . ifPi

-- | If the given type is blocked or not a @Pi@, pass it reduced to the first continuation.
--   If it is a @Pi@, pass its parts to the second continuation.
ifNotPiType :: MonadReduce m => Type -> (Type -> m a) -> (Dom Type -> Abs Type -> m a) -> m a
ifNotPiType = flip . ifPiType

ifNotPiOrPathType :: (MonadReduce tcm, MonadTCM tcm) => Type -> (Type -> tcm a) -> (Dom Type -> Abs Type -> tcm a) -> tcm a
ifNotPiOrPathType t no yes = do
  ifPiType t yes (\ t -> either (uncurry yes . fst) (const $ no t) =<< liftTCM (pathViewAsPi'whnf t))


-- | A safe variant of 'piApply'.

class PiApplyM a where
  piApplyM :: MonadReduce m => Type -> a -> m Type

instance PiApplyM Term where
  piApplyM t v = ifNotPiType t __IMPOSSIBLE__ {-else-} $ \ _ b -> return $ absApp b v

instance PiApplyM a => PiApplyM (Arg a) where
  piApplyM t = piApplyM t . unArg

instance PiApplyM a => PiApplyM (Named n a) where
  piApplyM t = piApplyM t . namedThing

instance PiApplyM a => PiApplyM [a] where
  piApplyM t = foldl (\ mt v -> mt >>= (`piApplyM` v)) (return t)


-- | Compute type arity

typeArity :: Type -> TCM Nat
typeArity t = do
  TelV tel _ <- telView t
  return (size tel)

---------------------------------------------------------------------------
-- * Instance definitions
---------------------------------------------------------------------------

data OutputTypeName
  = OutputTypeName QName
  | OutputTypeVar
  | OutputTypeNameNotYetKnown
  | NoOutputTypeName

-- | Strips all Pi's and return the head definition name, if possible.
getOutputTypeName :: Type -> TCM OutputTypeName
getOutputTypeName t = do
  TelV tel t' <- telView t
  ifBlocked (unEl t') (\ _ _ -> return OutputTypeNameNotYetKnown) $ \ _ v ->
    case v of
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
      DontCare{} -> __IMPOSSIBLE__
      Dummy s    -> __IMPOSSIBLE_VERBOSE__ s

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
