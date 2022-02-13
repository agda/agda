
module Agda.TypeChecking.Telescope where

import Prelude hiding (null)

import Control.Monad

import Data.Foldable (find)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Warnings

import Agda.Utils.CallStack ( withCallerCallStack )
import Agda.Utils.Empty
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Agda.Utils.Impossible

-- | Flatten telescope: (Γ : Tel) -> [Type Γ]
flattenTel :: TermSubst a => Tele (Dom a) -> [Dom a]
flattenTel EmptyTel          = []
flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

{-# SPECIALIZE flattenTel :: Telescope -> [Dom Type] #-}

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
reorderTel_ tel = fromMaybe __IMPOSSIBLE__ (reorderTel tel)

-- | Unflatten: turns a flattened telescope into a proper telescope. Must be
--   properly ordered.
unflattenTel :: [ArgName] -> [Dom Type] -> Telescope
unflattenTel []   []            = EmptyTel
unflattenTel (x : xs) (a : tel) = ExtendTel a' (Abs x tel')
  where
    tel' = unflattenTel xs tel
    a'   = applySubst rho a
    rho  = parallelS (replicate (size tel + 1) (withCallerCallStack impossibleTerm))
unflattenTel [] (_ : _) = __IMPOSSIBLE__
unflattenTel (_ : _) [] = __IMPOSSIBLE__

-- | Rename the variables in the telescope to the given names
--   Precondition: @size xs == size tel@.
renameTel :: [Maybe ArgName] -> Telescope -> Telescope
renameTel []           EmptyTel           = EmptyTel
renameTel (Nothing:xs) (ExtendTel a tel') = ExtendTel a $ renameTel xs <$> tel'
renameTel (Just x :xs) (ExtendTel a tel') = ExtendTel a $ renameTel xs <$> (tel' { absName = x })
renameTel []           (ExtendTel _ _   ) = __IMPOSSIBLE__
renameTel (_      :_ ) EmptyTel           = __IMPOSSIBLE__

-- | Get the suggested names from a telescope
teleNames :: Telescope -> [ArgName]
teleNames = map (fst . unDom) . telToList

teleArgNames :: Telescope -> [Arg ArgName]
teleArgNames = map (argFromDom . fmap fst) . telToList

teleArgs :: (DeBruijn a) => Tele (Dom t) -> [Arg a]
teleArgs = map argFromDom . teleDoms

teleDoms :: (DeBruijn a) => Tele (Dom t) -> [Dom a]
teleDoms tel = zipWith (\ i dom -> deBruijnVar i <$ dom) (downFrom $ size l) l
  where l = telToList tel

-- UNUSED
-- withNamedArgsFromTel :: [a] -> Telescope -> [NamedArg a]
-- xs `withNamedArgsFromTel` tel =
--   [ Arg info (Named (Just $ Ranged empty $ argNameToString name) x)
--   | (x, Dom {domInfo = info, unDom = (name,_)}) <- zip xs l ]
--   where l = telToList tel

teleNamedArgs :: (DeBruijn a) => Tele (Dom t) -> [NamedArg a]
teleNamedArgs = map namedArgFromDom . teleDoms

-- | A variant of `teleNamedArgs` which takes the argument names (and the argument info)
--   from the first telescope and the variable names from the second telescope.
--
--   Precondition: the two telescopes have the same length.
tele2NamedArgs :: (DeBruijn a) => Telescope -> Telescope -> [NamedArg a]
tele2NamedArgs tel0 tel =
  [ Arg info (Named (Just $ WithOrigin Inserted $ unranged $ argNameToString argName) (debruijnNamedVar varName i))
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
      types = permute perm $ renameP impossible (flipP perm) $ flattenTel tel
  in  unflattenTel names types

-- | Recursively computes dependencies of a set of variables in a given
--   telescope. Any dependencies outside of the telescope are ignored.
varDependencies :: Telescope -> IntSet -> IntSet
varDependencies tel = addLocks . allDependencies IntSet.empty
  where
    addLocks s | IntSet.null s = s
               | otherwise = IntSet.union s $ IntSet.fromList $ filter (>= m) locks
      where
        locks = catMaybes [ deBruijnView (unArg a) | (a :: Arg Term) <- teleArgs tel, getLock a == IsLock]
        m = IntSet.findMin s
    n  = size tel
    ts = flattenTel tel

    directDependencies :: Int -> IntSet
    directDependencies i = allFreeVars $ indexWithDefault __IMPOSSIBLE__ ts (n-1-i)

    allDependencies :: IntSet -> IntSet -> IntSet
    allDependencies =
      IntSet.foldr $ \j soFar ->
        if j >= n || j `IntSet.member` soFar
        then soFar
        else IntSet.insert j $ allDependencies soFar $ directDependencies j

-- | Computes the set of variables in a telescope whose type depend on
--   one of the variables in the given set (including recursive
--   dependencies). Any dependencies outside of the telescope are
--   ignored.
varDependents :: Telescope -> IntSet -> IntSet
varDependents tel = allDependents
  where
    n  = size tel
    ts = flattenTel tel

    directDependents :: IntSet -> IntSet
    directDependents is = IntSet.fromList
      [ j | j <- downFrom n
          , let tj = indexWithDefault __IMPOSSIBLE__ ts (n-1-j)
          , getAny $ runFree (Any . (`IntSet.member` is)) IgnoreNot tj
          ]

    allDependents :: IntSet -> IntSet
    allDependents is
     | null new  = empty
     | otherwise = new `IntSet.union` allDependents new
      where new = directDependents is

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

    ts1   = renameP impossible (reverseP perm) (permute perm ts0)

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
        t   = indexWithDefault __IMPOSSIBLE__ ts0 (n-1-j)  -- ts0[n-1-j]
        -- Skip the construction of intermediate @IntSet@s in the check @ok@.
        -- ok  = (allFreeVars t `IntSet.intersection` IntSet.fromAscList [ 0 .. n-1 ])
        --       `IntSet.isSubsetOf` soFar
        good i = All $ (i < n) `implies` (i `IntSet.member` soFar) where implies = (<=)
        ok = getAll $ runFree good IgnoreNot t

    ok    = all (<n) is && checkDependencies IntSet.empty is

    isC   = downFrom n List.\\ is

    perm  = Perm n $ map (n-1-) $ is ++ isC

    ts1   = renameP impossible (reverseP perm) (permute perm ts0)

    tel'  = unflattenTel (permute perm names) ts1

    m     = size is
    (tel1, tel2) = telFromList -*- telFromList $ splitAt m $ telToList tel'

-- | Try to instantiate one variable in the telescope (given by its de Bruijn
--   level) with the given value, returning the new telescope and a
--   substitution to the old one. Returns Nothing if the given value depends
--   (directly or indirectly) on the variable.
instantiateTelescope
  :: Telescope -- ^ ⊢ Γ
  -> Int       -- ^ Γ ⊢ var k : A   de Bruijn _level_
  -> DeBruijnPattern -- ^ Γ ⊢ u : A
  -> Maybe (Telescope,           -- ⊢ Γ'
            PatternSubstitution, -- Γ' ⊢ σ : Γ
            Permutation)         -- Γ  ⊢ flipP ρ : Γ'
instantiateTelescope tel k p = guard ok $> (tel', sigma, rho)
  where
    names = teleNames tel
    ts0   = flattenTel tel
    n     = size tel
    j     = n-1-k
    u     = patternToTerm p

    -- Jesper, 2019-12-31: Previous implementation that does some
    -- unneccessary reordering but is otherwise correct (keep!)
    -- -- is0 is the part of Γ that is needed to type u
    -- is0   = varDependencies tel $ allFreeVars u
    -- -- is1 is the rest of Γ (minus the variable we are instantiating)
    -- is1   = IntSet.delete j $
    --           IntSet.fromAscList [ 0 .. n-1 ] `IntSet.difference` is0
    -- -- we work on de Bruijn indices, so later parts come first
    -- is    = IntSet.toAscList is1 ++ IntSet.toAscList is0

    -- -- if u depends on var j, we cannot instantiate
    -- ok    = not $ j `IntSet.member` is0

    -- is0 is the part of Γ that is needed to type u
    is0   = varDependencies tel $ allFreeVars u
    -- is1 is the part of Γ that depends on variable j
    is1   = varDependents tel $ singleton j
    -- lasti is the last (rightmost) variable of is0
    lasti = if null is0 then n else IntSet.findMin is0
    -- we move each variable in is1 to the right until it comes after
    -- all variables in is0 (i.e. after lasti)
    (as,bs) = List.partition (`IntSet.member` is1) [ n-1 , n-2 .. lasti ]
    is    = reverse $ List.delete j $ bs ++ as ++ downFrom lasti

    -- if u depends on var j, we cannot instantiate
    ok    = not $ j `IntSet.member` is0

    perm  = Perm n $ is    -- works on de Bruijn indices
    rho   = reverseP perm  -- works on de Bruijn levels

    p1    = renameP impossible perm p -- Γ' ⊢ p1 : A'
    us    = map (\i -> maybe p1 deBruijnVar (List.elemIndex i is)) [ 0 .. n-1 ]
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
    (ts1,xa:ts2) = fromMaybe __IMPOSSIBLE__ $
                    splitExactlyAt k $ telToList gamma
    a = raise (size delta) (snd <$> xa) -- Γ₁Δ ⊢ D pars

    cpi         = ConPatternInfo
      { conPInfo   = defaultPatternInfo
      , conPRecord = True
      , conPFallThrough
                   = False
      , conPType   = Just $ argFromDom a
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
telView :: (MonadReduce m, MonadAddContext m) => Type -> m TelView
telView = telViewUpTo (-1)

-- | @telViewUpTo n t@ takes off the first @n@ function types of @t@.
-- Takes off all if @n < 0@.
telViewUpTo :: (MonadReduce m, MonadAddContext m) => Int -> Type -> m TelView
telViewUpTo n t = telViewUpTo' n (const True) t

-- | @telViewUpTo' n p t@ takes off $t$
--   the first @n@ (or arbitrary many if @n < 0@) function domains
--   as long as they satify @p@.
telViewUpTo' :: (MonadReduce m, MonadAddContext m) => Int -> (Dom Type -> Bool) -> Type -> m TelView
telViewUpTo' 0 p t = return $ TelV EmptyTel t
telViewUpTo' n p t = do
  t <- reduce t
  case unEl t of
    Pi a b | p a -> absV a (absName b) <$> do
                      underAbstractionAbs a b $ \b -> telViewUpTo' (n - 1) p b
    _            -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

telViewPath :: PureTCM m => Type -> m TelView
telViewPath = telViewUpToPath (-1)

-- | @telViewUpToPath n t@ takes off $t$
--   the first @n@ (or arbitrary many if @n < 0@) function domains or Path types.
telViewUpToPath :: PureTCM m => Int -> Type -> m TelView
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
type Boundary = Boundary' (Term,Term)
type Boundary' a = [(Term,a)]

-- | Like @telViewUpToPath@ but also returns the @Boundary@ expected
-- by the Path types encountered. The boundary terms live in the
-- telescope given by the @TelView@.
-- Each point of the boundary has the type of the codomain of the Path type it got taken from, see @fullBoundary@.
telViewUpToPathBoundary' :: PureTCM m => Int -> Type -> m (TelView,Boundary)
telViewUpToPathBoundary' 0 t = return $ (TelV EmptyTel t,[])
telViewUpToPathBoundary' n t = do
  vt <- pathViewAsPi' $ t
  case vt of
    Left ((a,b),xy) -> addEndPoints xy . absV a (absName b) <$> telViewUpToPathBoundary' (n - 1) (absBody b)
    Right (El _ t) | Pi a b <- t
                   -> absV a (absName b) <$> telViewUpToPathBoundary' (n - 1) (absBody b)
    Right t        -> return $ (TelV EmptyTel t,[])
  where
    absV a x (TelV tel t, cs) = (TelV (ExtendTel a (Abs x tel)) t, cs)
    addEndPoints xy (telv@(TelV tel _),cs) = (telv, (var $ size tel - 1, xyInTel):cs)
      where
       xyInTel = raise (size tel) xy


fullBoundary :: Telescope -> Boundary -> Boundary
fullBoundary tel bs =
      -- tel = Γ
      -- ΔΓ ⊢ b
      -- Δ ⊢ a = PiPath Γ bs b
      -- Δ.Γ ⊢ T is the codomain of the PathP at variable i
      -- Δ.Γ ⊢ i : I
      -- Δ.Γ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : T
      -- Δ.Γ | PiPath Γ bs A ⊢ teleElims tel bs : b
   let es = teleElims tel bs
       l  = size tel
   in map (\ (t@(Var i []), xy) -> (t, xy `applyE` (drop (l - i) es))) bs

-- | @(TelV Γ b, [(i,t_i,u_i)]) <- telViewUpToPathBoundary n a@
--  Input:  Δ ⊢ a
--  Output: ΔΓ ⊢ b
--          ΔΓ ⊢ i : I
--          ΔΓ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : b
telViewUpToPathBoundary :: PureTCM m => Int -> Type -> m (TelView,Boundary)
telViewUpToPathBoundary i a = do
   (telv@(TelV tel b), bs) <- telViewUpToPathBoundary' i a
   return $ (telv, fullBoundary tel bs)

-- | @(TelV Γ b, [(i,t_i,u_i)]) <- telViewUpToPathBoundaryP n a@
--  Input:  Δ ⊢ a
--  Output: Δ.Γ ⊢ b
--          Δ.Γ ⊢ T is the codomain of the PathP at variable i
--          Δ.Γ ⊢ i : I
--          Δ.Γ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : T
-- Useful to reconstruct IApplyP patterns after teleNamedArgs Γ.
telViewUpToPathBoundaryP :: PureTCM m => Int -> Type -> m (TelView,Boundary)
telViewUpToPathBoundaryP = telViewUpToPathBoundary'

telViewPathBoundaryP :: PureTCM m => Type -> m (TelView,Boundary)
telViewPathBoundaryP = telViewUpToPathBoundaryP (-1)


-- | @teleElimsB args bs = es@
--  Input:  Δ.Γ ⊢ args : Γ
--          Δ.Γ ⊢ T is the codomain of the PathP at variable i
--          Δ.Γ ⊢ i : I
--          Δ.Γ ⊢ bs = [ (i=0) -> t_i; (i=1) -> u_i ] : T
--  Output: Δ.Γ | PiPath Γ bs A ⊢ es : A
teleElims :: DeBruijn a => Telescope -> Boundary' (a,a) -> [Elim' a]
teleElims tel [] = map Apply $ teleArgs tel
teleElims tel boundary = recurse (teleArgs tel)
  where
    recurse = fmap updateArg
    matchVar x =
      snd <$> find (\case
        (Var i [],_) -> i == x
        _            -> __IMPOSSIBLE__) boundary
    updateArg a@(Arg info p) =
      case deBruijnView p of
        Just i | Just (t,u) <- matchVar i -> IApply t u p
        _                                 -> Apply a

pathViewAsPi
  :: PureTCM m => Type -> m (Either (Dom Type, Abs Type) Type)
pathViewAsPi t = either (Left . fst) Right <$> pathViewAsPi' t

pathViewAsPi'
  :: PureTCM m => Type -> m (Either ((Dom Type, Abs Type), (Term,Term)) Type)
pathViewAsPi' t = do
  pathViewAsPi'whnf <*> reduce t

pathViewAsPi'whnf
  :: (HasBuiltins m)
  => m (Type -> Either ((Dom Type, Abs Type), (Term,Term)) Type)
pathViewAsPi'whnf = do
  view <- pathView'
  minterval  <- getTerm' builtinInterval
  return $ \ t -> case view t of
    PathType s l p a x y | Just interval <- minterval ->
      let name | Lam _ (Abs n _) <- unArg a = n
               | otherwise = "i"
          i = El intervalSort interval
      in
        Left $ ((defaultDom $ i, Abs name $ El (raise 1 s) $ raise 1 (unArg a) `apply` [defaultArg $ var 0]), (unArg x, unArg y))

    _    -> Right t

-- | returns Left (a,b) in case the type is @Pi a b@ or @PathP b _ _@
--   assumes the type is in whnf.
piOrPath :: HasBuiltins m => Type -> m (Either (Dom Type, Abs Type) Type)
piOrPath t = do
  t <- pathViewAsPi'whnf <*> pure t
  case t of
    Left (p,_) -> return $ Left p
    Right (El _ (Pi a b)) -> return $ Left (a,b)
    Right t -> return $ Right t

telView'UpToPath :: Int -> Type -> TCM TelView
telView'UpToPath 0 t = return $ TelV EmptyTel t
telView'UpToPath n t = do
  vt <- pathViewAsPi'whnf <*> pure t
  case vt of
    Left ((a,b),_)     -> absV a (absName b) <$> telViewUpToPath (n - 1) (absBody b)
    Right (El _ t) | Pi a b <- t
                   -> absV a (absName b) <$> telViewUpToPath (n - 1) (absBody b)
    Right t        -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

telView'Path :: Type -> TCM TelView
telView'Path = telView'UpToPath (-1)

isPath
  :: PureTCM m => Type -> m (Maybe (Dom Type, Abs Type))
isPath t = either Just (const Nothing) <$> pathViewAsPi t

telePatterns :: DeBruijn a => Telescope -> Boundary -> [NamedArg (Pattern' a)]
telePatterns = telePatterns' teleNamedArgs

telePatterns' :: DeBruijn a =>
                (forall a. (DeBruijn a) => Telescope -> [NamedArg a]) -> Telescope -> Boundary -> [NamedArg (Pattern' a)]
telePatterns' f tel [] = f tel
telePatterns' f tel boundary = recurse $ f tel
  where
    recurse = (fmap . fmap . fmap) updateVar
    matchVar x =
      snd <$> find (\case
        (Var i [],_) -> i == x
        _            -> __IMPOSSIBLE__) boundary
    updateVar x =
      case deBruijnView x of
        Just i | Just (t,u) <- matchVar i -> IApplyP defaultPatternInfo t u x
        _                                 -> VarP defaultPatternInfo x

-- | Decomposing a function type.

mustBePi :: MonadReduce m => Type -> m (Dom Type, Abs Type)
mustBePi t = ifNotPiType t __IMPOSSIBLE__ $ curry return

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

ifNotPiOrPathType :: (MonadReduce tcm, HasBuiltins tcm) => Type -> (Type -> tcm a) -> (Dom Type -> Abs Type -> tcm a) -> tcm a
ifNotPiOrPathType t no yes = do
  ifPiType t yes (\ t -> either (uncurry yes . fst) (const $ no t) =<< (pathViewAsPi'whnf <*> pure t))


-- | A safe variant of 'piApply'.

class PiApplyM a where
  piApplyM' :: (MonadReduce m, HasBuiltins m) => m Empty -> Type -> a -> m Type

  piApplyM :: (MonadReduce m, HasBuiltins m) => Type -> a -> m Type
  piApplyM = piApplyM' __IMPOSSIBLE__

instance PiApplyM Term where
  piApplyM' err t v = ifNotPiOrPathType t (\_ -> absurd <$> err) {-else-} $ \ _ b -> return $ absApp b v

instance PiApplyM a => PiApplyM (Arg a) where
  piApplyM' err t = piApplyM' err t . unArg

instance PiApplyM a => PiApplyM (Named n a) where
  piApplyM' err t = piApplyM' err t . namedThing

instance PiApplyM a => PiApplyM [a] where
  piApplyM' err t = foldl (\ mt v -> mt >>= \t -> (piApplyM' err t v)) (return t)


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
  | OutputTypeVisiblePi
  | OutputTypeNameNotYetKnown Blocker
  | NoOutputTypeName

-- | Strips all hidden and instance Pi's and return the argument
--   telescope and head definition name, if possible.
getOutputTypeName :: Type -> TCM (Telescope, OutputTypeName)
getOutputTypeName t = do
  TelV tel t' <- telViewUpTo' (-1) notVisible t
  ifBlocked (unEl t') (\ b _ -> return (tel , OutputTypeNameNotYetKnown b)) $ \ _ v ->
    case v of
      -- Possible base types:
      Def n _  -> return (tel , OutputTypeName n)
      Sort{}   -> return (tel , NoOutputTypeName)
      Var n _  -> return (tel , OutputTypeVar)
      Pi{}     -> return (tel , OutputTypeVisiblePi)
      -- Not base types:
      Con{}    -> __IMPOSSIBLE__
      Lam{}    -> __IMPOSSIBLE__
      Lit{}    -> __IMPOSSIBLE__
      Level{}  -> __IMPOSSIBLE__
      MetaV{}  -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__
      Dummy s _ -> __IMPOSSIBLE_VERBOSE__ s

-- | Register the definition with the given type as an instance
addTypedInstance :: QName -> Type -> TCM ()
addTypedInstance x t = do
  (tel , n) <- getOutputTypeName t
  case n of
    OutputTypeName n -> addNamedInstance x n
    OutputTypeNameNotYetKnown{} -> addUnknownInstance x
    NoOutputTypeName -> warning $ WrongInstanceDeclaration
    OutputTypeVar -> warning $ WrongInstanceDeclaration
    OutputTypeVisiblePi -> warning $ InstanceWithExplicitArg x

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
