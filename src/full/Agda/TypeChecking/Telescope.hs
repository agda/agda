{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE ViewPatterns #-}

module Agda.TypeChecking.Telescope where

import Prelude hiding (null)

import Control.Monad

import Data.Bifunctor (first)
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

import Agda.Utils.CallStack ( withCallerCallStack )
import Agda.Utils.Either
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

-- | Flatten telescope: @(Γ : Tel) -> [Type Γ]@
flattenTel :: TermSubst a => Tele (Dom a) -> [Dom a]
flattenTel EmptyTel          = []
flattenTel (ExtendTel a tel) = raise (size tel + 1) a : flattenTel (absBody tel)

{-# SPECIALIZE flattenTel :: Telescope -> [Dom Type] #-}

-- | Turn a context into a flat telescope: all entries live in the whole context.
-- @
--    (Γ : Context) -> [Type Γ]
-- @
flattenContext :: Context -> [ContextEntry]
flattenContext = loop 1 []
  where
    loop n tel []       = tel
    loop n tel (ce:ctx) = loop (n + 1) (raise n ce : tel) ctx

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
unflattenTel xs tel = unflattenTel' (size tel) xs tel

-- | A variant of 'unflattenTel' which takes the size of the last
-- argument as an argument.
unflattenTel' :: Int -> [ArgName] -> [Dom Type] -> Telescope
unflattenTel' !n xs tel = case (xs, tel) of
  ([],     [])      -> EmptyTel
  (x : xs, a : tel) -> ExtendTel a' (Abs x tel')
    where
    tel' = unflattenTel' (n - 1) xs tel
    a'   = applySubst rho a
    rho  = parallelS $
           replicate n (withCallerCallStack impossibleTerm)
  ([],    _ : _) -> __IMPOSSIBLE__
  (_ : _, [])    -> __IMPOSSIBLE__

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

{-# INLINABLE tele2NamedArgs #-}
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

-- | Like 'permuteTel', but start with a context.
--
permuteContext :: Permutation -> Context -> Telescope
permuteContext perm ctx = permuteTel perm $ contextToTel ctx

-- | Recursively computes dependencies of a set of variables in a given
--   telescope. Any dependencies outside of the telescope are ignored.
varDependencies :: Telescope -> IntSet -> IntSet
varDependencies tel = addLocks . allDependencies IntSet.empty
  where
    addLocks s | IntSet.null s = s
               | otherwise = IntSet.union s $ IntSet.fromList $ filter (>= m) locks
      where
        locks = catMaybes [ deBruijnView (unArg a) | (a :: Arg Term) <- teleArgs tel, IsLock{} <- pure (getLock a)]
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

    ok    = all (< n) is && checkDependencies IntSet.empty is

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


{-# INLINE telView #-}
-- | Gather leading Πs of a type in a telescope.
telView :: (MonadReduce m, MonadAddContext m) => Type -> m TelView
telView = telViewUpTo (-1)

{-# INLINE telViewUpTo #-}
-- | @telViewUpTo n t@ takes off the first @n@ function types of @t@.
-- Takes off all if @n < 0@.
telViewUpTo :: (MonadReduce m, MonadAddContext m) => Int -> Type -> m TelView
telViewUpTo n t = telViewUpTo' n (const True) t

{-# SPECIALIZE telViewUpTo' :: Int -> (Dom Type -> Bool) -> Type -> TCM TelView #-}
-- | @telViewUpTo' n p t@ takes off $t$
--   the first @n@ (or arbitrary many if @n < 0@) function domains
--   as long as they satify @p@.
telViewUpTo' :: (MonadReduce m, MonadAddContext m) => Int -> (Dom Type -> Bool) -> Type -> m TelView
telViewUpTo' 0 p t = return $ TelV EmptyTel t
telViewUpTo' n p t = do
  t <- reduce t
  case unEl t of
    Pi a b | p a ->
          -- Force the name to avoid retaining the rest of b.
      let !bn = absName b in
      absV a bn <$> do
        underAbstractionAbs a b $ \b -> telViewUpTo' (n - 1) p b
    _ -> return $ TelV EmptyTel t

{-# INLINE telViewPath #-}
telViewPath :: PureTCM m => Type -> m TelView
telViewPath = telViewUpToPath (-1)

{-# SPECIALIZE telViewUpToPath :: Int -> Type -> TCM TelView #-}
-- | @telViewUpToPath n t@ takes off $t$
--   the first @n@ (or arbitrary many if @n < 0@) function domains or Path types.
--
-- @telViewUpToPath n t = fst <$> telViewUpToPathBoundary'n t@
telViewUpToPath :: PureTCM m => Int -> Type -> m TelView
telViewUpToPath n t = if n == 0 then done t else do
  pathViewAsPi t >>= \case
    Left  (a, b)          -> recurse a b
    Right (El _ (Pi a b)) -> recurse a b
    Right t               -> done t
  where
    done t      = return $ TelV EmptyTel t
    recurse a b = absV a (absName b) <$> telViewUpToPath (n - 1) (absBody b)

-- | [[ (i,(x,y)) ]] = [(i=0) -> x, (i=1) -> y]
type Boundary = Boundary' (Term,Term)
type Boundary' a = [(Term,a)]


{-# SPECIALIZE telViewUpToPathBoundary' :: Int -> Type -> TCM (TelView, Boundary) #-}
-- | Like @telViewUpToPath@ but also returns the @Boundary@ expected
-- by the Path types encountered. The boundary terms live in the
-- telescope given by the @TelView@.
-- Each point of the boundary has the type of the codomain of the Path type it got taken from, see @fullBoundary@.
telViewUpToPathBoundary' :: PureTCM m => Int -> Type -> m (TelView, Boundary)
telViewUpToPathBoundary' n t = if n == 0 then done t else do
  pathViewAsPi' t >>= \case
    Left ((a, b), xy)     -> addEndPoints xy <$> recurse a b
    Right (El _ (Pi a b)) -> recurse a b
    Right t               -> done t
  where
    done t      = return (TelV EmptyTel t, [])
    recurse a b = first (absV a (absName b)) <$> do
      underAbstractionAbs a b $ \b -> telViewUpToPathBoundary' (n - 1) b
    addEndPoints xy (telv@(TelV tel _), cs) =
      (telv, (var $ size tel - 1, raise (size tel) xy) : cs)


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

{-# SPECIALIZE telViewUpToPathBoundary :: Int -> Type -> TCM (TelView, Boundary) #-}
-- | @(TelV Γ b, [(i,t_i,u_i)]) <- telViewUpToPathBoundary n a@
--  Input:  Δ ⊢ a
--  Output: ΔΓ ⊢ b
--          ΔΓ ⊢ i : I
--          ΔΓ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : b
telViewUpToPathBoundary :: PureTCM m => Int -> Type -> m (TelView,Boundary)
telViewUpToPathBoundary i a = do
   (telv@(TelV tel b), bs) <- telViewUpToPathBoundary' i a
   return $ (telv, fullBoundary tel bs)

{-# INLINE telViewUpToPathBoundaryP #-}
-- | @(TelV Γ b, [(i,t_i,u_i)]) <- telViewUpToPathBoundaryP n a@
--  Input:  Δ ⊢ a
--  Output: Δ.Γ ⊢ b
--          Δ.Γ ⊢ T is the codomain of the PathP at variable i
--          Δ.Γ ⊢ i : I
--          Δ.Γ ⊢ [ (i=0) -> t_i; (i=1) -> u_i ] : T
-- Useful to reconstruct IApplyP patterns after teleNamedArgs Γ.
telViewUpToPathBoundaryP :: PureTCM m => Int -> Type -> m (TelView,Boundary)
telViewUpToPathBoundaryP = telViewUpToPathBoundary'

{-# INLINE telViewPathBoundaryP #-}
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

{-# SPECIALIZE pathViewAsPi :: Type -> TCM (Either (Dom Type, Abs Type) Type) #-}
-- | Reduces 'Type'.
pathViewAsPi
  :: PureTCM m => Type -> m (Either (Dom Type, Abs Type) Type)
pathViewAsPi t = either (Left . fst) Right <$> pathViewAsPi' t

{-# SPECIALIZE pathViewAsPi' :: Type -> TCM (Either ((Dom Type, Abs Type), (Term,Term)) Type) #-}
-- | Reduces 'Type'.
pathViewAsPi'
  :: PureTCM m => Type -> m (Either ((Dom Type, Abs Type), (Term,Term)) Type)
pathViewAsPi' t = do
  pathViewAsPi'whnf <*> reduce t

{-# SPECIALIZE pathViewAsPi'whnf :: TCM (Type -> Either ((Dom Type, Abs Type), (Term,Term)) Type) #-}
pathViewAsPi'whnf
  :: (HasBuiltins m)
  => m (Type -> Either ((Dom Type, Abs Type), (Term,Term)) Type)
pathViewAsPi'whnf = do
  view <- pathView'
  minterval  <- getTerm' builtinInterval
  return $ \case
    (view -> PathType s l p a x y) | Just interval <- minterval ->
      let name | Lam _ (Abs n _) <- unArg a = n
               | otherwise = "i"
      in
        Left ( ( defaultDom $ El intervalSort interval
               , Abs name $ El (raise 1 s) $ raise 1 (unArg a) `apply` [defaultArg $ var 0]
               )
             , (unArg x, unArg y)
             )

    t    -> Right t

-- | Returns @Left (a,b)@ in case the type is @Pi a b@ or @PathP b _ _@.
--   Assumes the 'Type' is in whnf.
piOrPath :: HasBuiltins m => Type -> m (Either (Dom Type, Abs Type) Type)
piOrPath t = do
  (pathViewAsPi'whnf <*> pure t) <&> \case
    Left (p, _)           -> Left p
    Right (El _ (Pi a b)) -> Left (a,b)
    Right _               -> Right t

-- | Assumes 'Type' is in whnf.
telView'UpToPath :: Int -> Type -> TCM TelView
telView'UpToPath n t = if n == 0 then done else do
  piOrPath t >>= \case
    Left (a, b) -> absV a (absName b) <$> telViewUpToPath (n - 1) (absBody b)
    Right _     -> done
  where
    done = return $ TelV EmptyTel t

telView'Path :: Type -> TCM TelView
telView'Path = telView'UpToPath (-1)

isPath :: PureTCM m => Type -> m (Maybe (Dom Type, Abs Type))
isPath t = ifPath t (\a b -> return $ Just (a,b)) (const $ return Nothing)

ifPath :: PureTCM m => Type -> (Dom Type -> Abs Type -> m a) -> (Type -> m a) -> m a
ifPath t yes no = ifPathB t yes $ no . ignoreBlocking

{-# SPECIALIZE ifPathB :: Type -> (Dom Type -> Abs Type -> TCM a) -> (Blocked Type -> TCM a) -> TCM a #-}
ifPathB :: PureTCM m => Type -> (Dom Type -> Abs Type -> m a) -> (Blocked Type -> m a) -> m a
ifPathB t yes no = ifBlocked t
  (\b t -> no $ Blocked b t)
  (\nb t -> caseEitherM (pathViewAsPi'whnf <*> pure t)
    (uncurry yes . fst)
    (no . NotBlocked nb))

ifNotPathB :: PureTCM m => Type -> (Blocked Type -> m a) -> (Dom Type -> Abs Type -> m a) -> m a
ifNotPathB = flip . ifPathB

ifPiOrPathB :: PureTCM m => Type -> (Dom Type -> Abs Type -> m a) -> (Blocked Type -> m a) -> m a
ifPiOrPathB t yes no = ifPiTypeB t
  (\a b -> yes a b)
  (\bt -> caseEitherM (pathViewAsPi'whnf <*> pure (ignoreBlocking bt))
    (uncurry yes . fst)
    (no . (bt $>)))

ifNotPiOrPathB :: PureTCM m => Type -> (Blocked Type -> m a) -> (Dom Type -> Abs Type -> m a) -> m a
ifNotPiOrPathB = flip . ifPiOrPathB

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
ifPi t yes no = ifPiB t yes (no . ignoreBlocking)

ifPiB :: (MonadReduce m) => Term -> (Dom Type -> Abs Type -> m a) -> (Blocked Term -> m a) -> m a
ifPiB t yes no = ifBlocked t
  (\b t -> no $ Blocked b t) -- Pi type is never blocked
  (\nb t -> case t of
    Pi a b -> yes a b
    _      -> no $ NotBlocked nb t)

ifPiTypeB :: (MonadReduce m) => Type -> (Dom Type -> Abs Type -> m a) -> (Blocked Type -> m a) -> m a
ifPiTypeB (El s t) yes no = ifPiB t yes (\bt -> no $ El s <$> bt)

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

shouldBePath :: (PureTCM m, MonadBlock m, MonadTCError m) => Type -> m (Dom Type, Abs Type)
shouldBePath t = ifPathB t
  (curry return)
  (fromBlocked >=> \case
    El _ Dummy{} -> return (__DUMMY_DOM__, Abs "x" __DUMMY_TYPE__)
    t -> typeError $ ShouldBePath t)

shouldBePi :: (PureTCM m, MonadBlock m, MonadTCError m) => Type -> m (Dom Type, Abs Type)
shouldBePi t = ifPiTypeB t
  (curry return)
  (fromBlocked >=> \case
    El _ Dummy{} -> return (__DUMMY_DOM__, Abs "x" __DUMMY_TYPE__)
    t -> typeError $ ShouldBePi t)

shouldBePiOrPath :: (PureTCM m, MonadBlock m, MonadTCError m) => Type -> m (Dom Type, Abs Type)
shouldBePiOrPath t = ifPiOrPathB t
  (curry return)
  (fromBlocked >=> \case
    El _ Dummy{} -> return (__DUMMY_DOM__, Abs "x" __DUMMY_TYPE__)
    t -> typeError $ ShouldBePi t) -- TODO: separate error

-- | A safe variant of 'piApply'.

class PiApplyM a where
  piApplyM' :: (MonadReduce m, HasBuiltins m) => m Empty -> Type -> a -> m Type

  piApplyM :: (MonadReduce m, HasBuiltins m) => Type -> a -> m Type
  piApplyM = piApplyM' __IMPOSSIBLE__
  {-# INLINE piApplyM #-}

instance PiApplyM Term where
  piApplyM' err t v = ifNotPiOrPathType t (\_ -> absurd <$> err) {-else-} $ \ _ b -> return $ absApp b v
  {-# INLINABLE piApplyM' #-}

{-# SPECIALIZE piApplyM' :: TCM Empty -> Type -> Term -> TCM Type #-}

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
