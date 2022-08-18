-- | Implementations of the basic primitives of Cubical Agda: The
-- interval and its operations.
module Agda.TypeChecking.Primitive.Cubical.Base
  ( requireCubical
  , primIntervalType
  , primIMin', primIMax', primDepIMin', primINeg'
  , imax, imin, ineg

  , Command(..), KanOperation(..), kanOpName, TermPosition(..), headStop
  , FamilyOrNot(..), familyOrNot

    -- * Helper functions for building terms
  , combineSys, combineSys'
  , fiber, hfill
  , decomposeInterval', decomposeInterval
  , reduce2Lam
  )
  where

import Control.Arrow (second)
import Control.Monad.Except

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.String (IsString (fromString))
import Data.Either (partitionEithers)
import Data.Maybe (fromMaybe, maybeToList)

import qualified Agda.Utils.BoolSet as BoolSet
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.BoolSet (BoolSet)
import Agda.Utils.Functor

import Agda.TypeChecking.Monad.Signature (HasConstInfo)
import Agda.TypeChecking.Monad.Debug (__IMPOSSIBLE_VERBOSE__)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env

import Agda.TypeChecking.Substitute.Class (absBody, raise, apply)

import Agda.TypeChecking.Reduce (Reduce(..), reduceB', reduce', reduce)
import Agda.TypeChecking.Names (NamesT, runNamesT, ilam, lam)

import Agda.Interaction.Options.Base (optCubical)

import Agda.Syntax.Common
  (Cubical(..), Arg(..), Relevance(..), setRelevance, defaultArgInfo, hasQuantity0)

import Agda.TypeChecking.Primitive.Base
  (SigmaKit(..), (-->), nPi', pPi', (<@>), (<#>), (<..>), argN, getSigmaKit)

import Agda.Syntax.Internal


-- | Checks that the correct variant of Cubical Agda is activated.
-- Note that @--erased-cubical@ \"counts as\" @--cubical@ in erased
-- contexts.
requireCubical
  :: Cubical -- ^ Which variant of Cubical Agda is required?
  -> String  -- ^ Why, exactly, do we need Cubical to be enabled?
  -> TCM ()
requireCubical wanted s = do
  cubical         <- optCubical <$> pragmaOptions
  inErasedContext <- hasQuantity0 <$> getEnv
  case cubical of
    Just CFull -> return ()
    Just CErased | wanted == CErased || inErasedContext -> return ()
    _ -> typeError $ GenericError $ "Missing option " ++ opt ++ s
  where
  opt = case wanted of
    CFull   -> "--cubical"
    CErased -> "--cubical or --erased-cubical"

-- | Our good friend the interval type.
primIntervalType :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Type
primIntervalType = El intervalSort <$> primInterval

-- | Negation on the interval. Negation satisfies De Morgan's laws, and
-- their implementation is handled here.
primINeg' :: TCM PrimitiveImpl
primINeg' = do
  requireCubical CErased ""
  t <- primIntervalType --> primIntervalType
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \case
    [x] -> do
      unview <- intervalUnview'
      view <- intervalView'
      sx <- reduceB' x
      ix <- intervalView (unArg $ ignoreBlocking sx)

      -- Apply De Morgan's laws.
      let
        ineg :: Arg Term -> Arg Term
        ineg = fmap (unview . f . view)

        f ix = case ix of
          IZero    -> IOne
          IOne     -> IZero
          IMin x y -> IMax (ineg x) (ineg y)
          IMax x y -> IMin (ineg x) (ineg y)
          INeg x   -> OTerm (unArg x)
          OTerm t  -> INeg (Arg defaultArgInfo t)

      -- We force the argument in case it happens to be an interval
      -- expression, but it's quite possible that it's _not_. In those
      -- cases, negation is stuck.
      case ix of
        OTerm t -> return $ NoReduction [reduced sx]
        _       -> redReturn (unview $ f ix)
    _ -> __IMPOSSIBLE_VERBOSE__ "implementation of primINeg called with wrong arity"

-- | 'primDepIMin' expresses that cofibrations are closed under @Σ@.
-- Thus, it serves as a dependent version of 'primIMin' (which, recall,
-- implements @_∧_@). This is required for the construction of the Kan
-- operations in @Id@.
primDepIMin' :: TCM PrimitiveImpl
primDepIMin' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       nPi' "φ" primIntervalType $ \ φ ->
       pPi' "o" φ (\ o -> primIntervalType) --> primIntervalType
  -- Note that the type here is @(φ : I) → (.(IsOne φ) → I) → I@, since
  -- @Partial φ I@ is not well-sorted.
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 2 $ \case
    [x,y] -> do
      sx <- reduceB' x
      ix <- intervalView (unArg $ ignoreBlocking sx)
      itisone <- getTerm "primDepIMin" builtinItIsOne
      case ix of
        -- Σ 0 iy is 0, and additionally P is def.eq. to isOneEmpty.
        IZero -> redReturn =<< intervalUnview IZero
        -- Σ 1 iy is (iy 1=1).
        IOne  -> redReturn =<< (pure (unArg y) <@> pure itisone)
        _     -> do
          -- Hack: We cross our fingers and really hope that eventually
          -- ix may turn out to be i1. Regardless we evaluate iy 1=1, to
          -- short-circuit evaluate a couple of cases:
          sy <- reduceB' y
          iy <- intervalView =<< reduce' =<< (pure (unArg $ ignoreBlocking sy) <@> pure itisone)
          case iy of
            -- Σ _ (λ _ → 0) is always 0
            IZero -> redReturn =<< intervalUnview IZero
            -- Σ ix (λ _ → 1) only depends on ix
            IOne  -> redReturn (unArg $ ignoreBlocking sx)
            -- Otherwise we're well and truly blocked.
            _     -> return $ NoReduction [reduced sx, reduced sy]
    _ -> __IMPOSSIBLE_VERBOSE__ "implementation of primDepIMin called with wrong arity"

-- | Internal helper for constructing binary operations on the interval,
-- parameterised by their unit and absorbing elements.
primIBin :: IntervalView -> IntervalView -> TCM PrimitiveImpl
primIBin unit absorber = do
  requireCubical CErased ""
  t <- primIntervalType --> primIntervalType --> primIntervalType
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 2 $ \case
    [x,y] -> do
      -- Evaluation here is short-circuiting: If the LHS is either the
      -- absorbing or unit element, then the RHS does not matter.
      sx <- reduceB' x
      ix <- intervalView (unArg $ ignoreBlocking sx)
      case ix of
        ix | ix ==% absorber -> redReturn =<< intervalUnview absorber
        ix | ix ==% unit     -> return $ YesReduction YesSimplification (unArg y)
        _ -> do
          -- And in the case where the LHS is stuck, we can make
          -- progress by comparing the LHS to the absorbing/unit
          -- elements.
          sy <- reduceB' y
          iy <- intervalView (unArg $ ignoreBlocking sy)
          case iy of
            iy | iy ==% absorber -> redReturn =<< intervalUnview absorber
            iy | iy ==% unit     -> return $ YesReduction YesSimplification (unArg x)
            _                    -> return $ NoReduction [reduced sx,reduced sy]
    _ -> __IMPOSSIBLE_VERBOSE__ "binary operation on the interval called with incorrect arity"
  where
    (==%) IZero IZero = True
    (==%) IOne IOne = True
    (==%) _ _ = False
{-# INLINE primIBin #-}

-- | Implements both the @min@ connection /and/ conjunction on the
-- cofibration classifier.
primIMin' :: TCM PrimitiveImpl
primIMin' = do
  requireCubical CErased ""
  primIBin IOne IZero

-- | Implements both the @max@ connection /and/ disjunction on the
-- cofibration classifier.
primIMax' :: TCM PrimitiveImpl
primIMax' = do
  requireCubical CErased ""
  primIBin IZero IOne

-- | A helper for evaluating @max@ on the interval in TCM&co.
imax :: HasBuiltins m => m Term -> m Term -> m Term
imax x y = do
  x' <- x
  y' <- y
  intervalUnview (IMax (argN x') (argN y'))

-- | A helper for evaluating @min@ on the interval in TCM&co.
imin :: HasBuiltins m => m Term -> m Term -> m Term
imin x y = do
  x' <- x
  y' <- y
  intervalUnview (IMin (argN x') (argN y'))

-- | A helper for evaluating @neg@ on the interval in TCM&co.
ineg :: HasBuiltins m => m Term -> m Term
ineg x = do
  x' <- x
  intervalUnview (INeg (argN x'))

data Command = DoTransp | DoHComp
  deriving (Eq, Show)

-- | The built-in name associated with a particular Kan operation.
kanOpName :: KanOperation -> String
kanOpName TranspOp{} = builtinTrans
kanOpName HCompOp{}  = builtinHComp

-- | Our Kan operations are @transp@ and @hcomp@. The KanOperation
-- record stores the data associated with a Kan operation on arbitrary
-- types: A cofibration and an element of that type.
data KanOperation
  -- | A transport problem consists of a cofibration, marking where the
  -- transport is constant, and a term to move from the fibre over i0 to
  -- the fibre over i1.
  = TranspOp
    { kanOpCofib :: Blocked (Arg Term)
      -- ^ When this cofibration holds, the transport must
      -- definitionally be the identity. This is handled generically by
      -- 'primTransHComp' but specific Kan operations may still need it.
    , kanOpBase :: Arg Term
      -- ^ This is the term in @A i0@ which we are transporting.
    }
  -- | A composition problem consists of a partial element and a base.
  -- Semantically, this is justified by the types being Kan fibrations,
  -- i.e., having the lifting property against trivial cofibrations.
  -- While the specified cofibration may not be trivial, (φ ∨ ~ r) for r
  -- ∉ φ is *always* a trivial cofibration.
  | HCompOp
    { kanOpCofib :: Blocked (Arg Term)
      -- ^ Extent of definition of the partial element we are lifting
      -- against.
    , kanOpSides :: Arg Term
      -- ^ The partial element itself
    , kanOpBase  :: Arg Term
      -- ^ The base.
    }

-- | Are we looking at a family of things, or at a single thing?
data FamilyOrNot a
  = IsFam { famThing :: a }
  | IsNot { famThing :: a }
  deriving (Eq,Show,Functor,Foldable,Traversable)

familyOrNot :: IsString p => FamilyOrNot a -> p
familyOrNot (IsFam x) = "IsFam"
familyOrNot (IsNot x) = "IsNot"

instance Reduce a => Reduce (FamilyOrNot a) where
  reduceB' x = traverse id <$> traverse reduceB' x
  reduce' x = traverse reduce' x

-- | For the Kan operations in @Glue@ and @hcomp {Type}@, we optimise
-- evaluation a tiny bit by differentiating the term produced when
-- evaluating a Kan operation by itself vs evaluating it under @unglue@.
data TermPosition
  = Head
  | Eliminated
  deriving (Eq,Show)

-- | If we're computing a Kan operation for one of the "unstable" type
-- formers (@Glue@, @hcomp {Type}@), this tells us whether the type will
-- reduce further, and whether we should care.
--
-- When should we care? When we're in the 'Head' 'TermPosition'. When
-- will the type reduce further? When @φ@, its formula, is not i1.
headStop :: PureTCM m => TermPosition -> m Term -> m Bool
headStop tpos phi
  | Head <- tpos = do
    phi <- intervalView =<< (reduce =<< phi)
    return $ not $ isIOne phi
  | otherwise = return False

-- | Build a partial element. The type of the resulting partial element
-- can depend on the computed extent, which we denote by @φ@ here. Note
-- that @φ@ is the n-ary disjunction of all the @ψ@s.
combineSys
  :: HasBuiltins m
  => NamesT m Term -- The level @l : Level@
  -> NamesT m Term -- The type @A : Partial φ (Type l)@.
  -> [(NamesT m Term, NamesT m Term)]
  -- ^ A list of @(ψ, PartialP ψ λ o → A (... o ...))@ mappings. Note
  -- that by definitional proof-irrelevance of @IsOne@, the actual
  -- injection can not matter here.
  -> NamesT m Term
combineSys l ty xs = snd <$> combineSys' l ty xs

-- | Build a partial element, and compute its extent. See 'combineSys'
-- for the details.
combineSys'
  :: forall m. HasBuiltins m
  => NamesT m Term -- The level @l@
  -> NamesT m Term -- The type @A@
  -> [(NamesT m Term, NamesT m Term)]
  -> NamesT m (Term,Term)
combineSys' l ty xs = do
  tPOr <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPOr
  tMax <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIMax
  iz <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIZero
  tEmpty <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinIsOneEmpty

  let
    pOr l ty phi psi u0 u1 = pure tPOr
      <#> l <@> phi <@> psi <#> (ilam "o" $ \ _ -> ty)
      <@> u0 <@> u1

    -- In one pass, compute the disjunction of all the cofibrations and
    -- compute the primPOr expression.
    combine :: [(NamesT m Term, NamesT m Term)] -> NamesT m (Term, Term)
    combine [] = (iz,) <$> (pure tEmpty <#> l <#> (ilam "o" $ \ _ -> ty))
    combine [(psi, u)] = (,) <$> psi <*> u
    combine ((psi, u):xs) = do
      (phi, c) <- combine xs
      (,) <$> imax psi (pure phi) <*> pOr l ty psi (pure phi) u (pure c)
  combine xs

-- | Helper function for constructing the type of fibres of a function
-- over a given point.
fiber
  :: (HasBuiltins m, HasConstInfo m)
  => NamesT m Term -- @la : Level@
  -> NamesT m Term -- @lb : Level@
  -> NamesT m Term -- @A : Type la@
  -> NamesT m Term -- @B : Type lb@
  -> NamesT m Term -- @f : A → B@
  -> NamesT m Term -- @x : B@
  -> NamesT m Term -- @Σ[ x ∈ A ] (f a ≡ x)@
fiber la lb bA bB f b = do
  tPath <- getTerm "fiber" builtinPath
  kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
  pure (Def (sigmaName kit) [])
    <#> la <#> lb
    <@> bA
    <@> lam "a" (\ a -> pure tPath <#> lb <#> bB <@> (f <@> a) <@> b)

-- | Helper function for constructing the filler of a given composition
-- problem.
hfill
  :: (HasBuiltins m, HasConstInfo m)
  => NamesT m Term -- @la : Level@
  -> NamesT m Term -- @A : Type la@
  -> NamesT m Term -- @φ : I@. Cofibration
  -> NamesT m Term -- @u : Partial φ A@.
  -> NamesT m Term -- @u0 : A@. Must agree with @u@ on @φ@
  -> NamesT m Term -- @i : I@. Position along the cube.
  -> NamesT m Term
hfill la bA phi u u0 i = do
  tHComp <- getTerm "hfill" builtinHComp
  pure tHComp <#> la <#> bA <#> (imax phi (ineg i))
    <@> lam "j" (\ j -> combineSys la bA
        [ (phi,    ilam "o" (\o -> u <@> (imin i j) <..> o))
        , (ineg i, ilam "o" (\_ -> u0))
        ])
    <@> u0

-- | Decompose an interval expression @i : I@ as in
-- 'decomposeInterval'', but discard any inconsistent mappings.
decomposeInterval :: HasBuiltins m => Term -> m [(IntMap Bool, [Term])]
decomposeInterval t = do
  decomposeInterval' t <&> \xs ->
    [ (bm, ts) | (bsm, ts) <- xs, bm <- maybeToList $ traverse BoolSet.toSingleton bsm ]

-- | Decompose an interval expression @φ : I@ into a set of possible
-- assignments for the variables mentioned in @φ@, together any leftover
-- neutral terms that could not be put into 'IntervalView' form.
decomposeInterval' :: HasBuiltins m => Term -> m [(IntMap BoolSet, [Term])]
decomposeInterval' t = do
  view   <- intervalView'
  unview <- intervalUnview'
  let
    f :: IntervalView -> [[Either (Int,Bool) Term]]
    -- TODO handle primIMinDep
    -- TODO? handle forall
    f IZero = mzero     -- No assignments are possible
    f IOne  = return [] -- No assignments are necessary
    -- Take the cartesian product
    f (IMin x y) = do
      xs <- (f . view . unArg) x
      ys <- (f . view . unArg) y
      return (xs ++ ys)
    -- Take the union
    f (IMax x y) = msum $ map (f . view . unArg) [x,y]
    -- Invert the possible assignments and negate the neutrals
    f (INeg x) =
      map (either (\ (x,y) -> Left (x,not y)) (Right . unview . INeg . argN))
        <$> (f . view . unArg) x
    f (OTerm (Var i [])) = return [Left (i,True)]
    f (OTerm t)          = return [Right t]

  return [ (bsm, ts)
         | xs <- f (view t)
         , let (bs,ts) = partitionEithers xs
         , let bsm     = IntMap.fromListWith BoolSet.union $ map (second BoolSet.singleton) bs
         ]

reduce2Lam :: Term -> ReduceM (Blocked Term)
reduce2Lam t = do
  t <- reduce' t
  case lam2Abs Relevant t of
    t -> underAbstraction_ t $ \ t -> do
      t <- reduce' t
      case lam2Abs Irrelevant t of
        t -> underAbstraction_ t reduceB'
  where
    lam2Abs rel (Lam _ t) = absBody t <$ t
    lam2Abs rel t         = Abs "y" (raise 1 t `apply` [setRelevance rel $ argN $ var 0])
