{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}

module Agda.TypeChecking.Primitive.Cubical
  ( module Agda.TypeChecking.Primitive.Cubical
  , module Agda.TypeChecking.Primitive.Cubical.Id
  , module Agda.TypeChecking.Primitive.Cubical.Base
  , module Agda.TypeChecking.Primitive.Cubical.Glue
  , module Agda.TypeChecking.Primitive.Cubical.HCompU
  )
  where

import Prelude hiding (null, (!!))

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans ( lift )
import Control.Exception

import Data.String

import Data.Bifunctor ( second )
import Data.Either ( partitionEithers )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Foldable hiding (null)

import Agda.Interaction.Options ( optCubical )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Monad

import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor

import Agda.Utils.Impossible
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Tuple
import Agda.Utils.Size
import Agda.Utils.BoolSet (BoolSet)
import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.BoolSet as BoolSet

import Agda.TypeChecking.Primitive.Cubical.HCompU
import Agda.TypeChecking.Primitive.Cubical.Glue
import Agda.TypeChecking.Primitive.Cubical.Base
import Agda.TypeChecking.Primitive.Cubical.Id

primPOr :: TCM PrimitiveImpl
primPOr = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (els (pure LevelUniv) (cl primLevel))    $ \ a  ->
          nPi' "i" primIntervalType $ \ i  ->
          nPi' "j" primIntervalType $ \ j  ->
          hPi' "A" (pPi' "o" (imax i j) $ \o -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          ((pPi' "i1" i $ \ i1 -> el' a $ bA <..> (cl primIsOne1 <@> i <@> j <@> i1))) -->
          ((pPi' "j1" j $ \ j1 -> el' a $ bA <..> (cl primIsOne2 <@> i <@> j <@> j1))) -->
          pPi' "o" (imax i j) (\ o -> el' a $ bA <..> o)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ ts -> do
    case ts of
     [l,i,j,a,u,v] -> do
       si <- reduceB' i
       vi <- intervalView $ unArg $ ignoreBlocking si
       case vi of
        IOne -> redReturn (unArg u)
        IZero -> redReturn (unArg v)
        _ -> do
          sj <- reduceB' j
          vj <- intervalView $ unArg $ ignoreBlocking sj
          case vj of
            IOne -> redReturn (unArg v)
            IZero -> redReturn (unArg u)
            _ -> return $ NoReduction [notReduced l,reduced si,reduced sj,notReduced a,notReduced u,notReduced v]


     _ -> __IMPOSSIBLE__

primPartial' :: TCM PrimitiveImpl
primPartial' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (els (pure LevelUniv) (cl primLevel)) (\ a ->
        nPi' "φ" primIntervalType $ \ _ ->
        nPi' "A" (sort . tmSort <$> a) $ \ bA ->
        (sort . tmSSort <$> a))
  isOne <- primIsOne
  v <- runNamesT [] $
        lam "a" $ \ l ->
        lam "φ" $ \ phi ->
        lam "A" $ \ a ->
        unEl <$> pPi' "p" phi (\_ -> el' l a)
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \ _ -> redReturn v

primPartialP' :: TCM PrimitiveImpl
primPartialP' = do
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "a" (els (pure LevelUniv) (cl primLevel)) (\ a ->
        nPi' "φ" primIntervalType $ \ phi ->
        nPi' "A" (pPi' "o" phi $ \ _ -> el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
        (sort . tmSSort <$> a))
  v <- runNamesT [] $
        lam "a" $ \ l ->
        lam "φ" $ \ phi ->
        lam "A" $ \ a ->
        unEl <$> pPi' "p" phi (\ p -> el' l (a <@> p))
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 0 $ \ _ -> redReturn v

primSubOut' :: TCM PrimitiveImpl
primSubOut' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (els (pure LevelUniv) (cl primLevel)) $ \ a ->
          hPi' "A" (el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          hPi' "u" (el's a $ cl primPartial <#> a <@> phi <@> bA) $ \ u ->
          el's a (cl primSub <#> a <@> bA <@> phi <@> u) --> el' a bA
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \ ts -> do
    case ts of
      [a,bA,phi,u,x] -> do
        view <- intervalView'
        sphi <- reduceB' phi
        case view $ unArg $ ignoreBlocking sphi of
          IOne -> redReturn =<< (return (unArg u) <..> getTerm (getBuiltinId PrimSubOut) BuiltinItIsOne)
          _ -> do
            sx <- reduceB' x
            mSubIn <- getBuiltinName' builtinSubIn
            case unArg $ ignoreBlocking $ sx of
              Def q [_,_,_, Apply t] | Just q == mSubIn -> redReturn (unArg t)
              _ -> return $ NoReduction $ map notReduced [a,bA] ++ [reduced sphi, notReduced u, reduced sx]
      _ -> __IMPOSSIBLE__

primTrans' :: TCM PrimitiveImpl
primTrans' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (primIntervalType --> els (pure LevelUniv) (cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" primIntervalType $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          nPi' "φ" primIntervalType $ \ phi ->
          (el' (a <@> cl primIZero) (bA <@> cl primIZero) --> el' (a <@> cl primIOne) (bA <@> cl primIOne))
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 4 $ \ ts nelims -> do
    primTransHComp DoTransp ts nelims

primHComp' :: TCM PrimitiveImpl
primHComp' = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (els (pure LevelUniv) (cl primLevel)) $ \ a ->
          hPi' "A" (sort . tmSort <$> a) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          nPi' "i" primIntervalType (\ i -> pPi' "o" phi $ \ _ -> el' a bA) -->
          (el' a bA --> el' a bA)
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts nelims -> do
    primTransHComp DoHComp ts nelims

-- | Construct a helper for CCHM composition, with a string indicating
-- what function uses it.
mkComp :: forall m. HasBuiltins m
       => String
       -> NamesT m (NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term)
mkComp s = do
  let getTermLocal :: IsBuiltin a => a -> NamesT m Term
      getTermLocal = getTerm s
  tIMax  <- getTermLocal builtinIMax
  tINeg  <- getTermLocal builtinINeg
  tHComp <- getTermLocal builtinHComp
  tTrans <- getTermLocal builtinTrans
  iz     <- getTermLocal builtinIZero
  io     <- getTermLocal builtinIOne

  let
    forward la bA r u = pure tTrans
      <#> (lam "i" $ \i -> la <@> (i `imax` r))
      <@> (lam "i" $ \i -> bA <@> (i `imax` r))
      <@> r
      <@> u

  pure $ \la bA phi u u0 ->
    pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io) <#> phi
                <@> lam "i" (\i -> ilam "o" $ \o ->
                        forward la bA i (u <@> i <..> o))
                <@> forward la bA (pure iz) u0

-- | Construct an application of buitlinComp. Use instead of 'mkComp' if
-- reducing directly to hcomp + transport would be problematic.
mkCompLazy
  :: HasBuiltins m
  => String
  -> NamesT m (NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term)
mkCompLazy s = do
  let getTermLocal = getTerm s
  tComp <- getTermLocal builtinComp
  pure $ \la bA phi u u0 -> pure tComp <#> la <#> bA <#> phi <@> u <@> u0

-- | Implementation of Kan operations for Pi types. The implementation
-- of @transp@ and @hcomp@ for Pi types has many commonalities, so most
-- of it is shared between the two cases.
doPiKanOp
  :: KanOperation -- ^ Are we composing or transporting?
  -> ArgName      -- ^ Name of the binder
  -> FamilyOrNot (Dom Type, Abs Type)
  -- ^ The domain and codomain of the Pi type.
  -> ReduceM (Maybe Term)
doPiKanOp cmd t ab = do
  let getTermLocal :: IsBuiltin a => a -> ReduceM Term
      getTermLocal = getTerm $ kanOpName cmd ++ " for function types"
  tTrans <- getTermLocal builtinTrans
  tHComp <- getTermLocal builtinHComp
  tINeg <- getTermLocal builtinINeg
  tIMax <- getTermLocal builtinIMax
  iz    <- getTermLocal builtinIZero

  -- We must guarantee that the codomain is a fibrant type, i.e. one
  -- that supports hcomp and transp. Otherwise, what are we even doing!
  let
    toLevel' t = do
      s <- reduce $ getSort t
      case s of
        Type l -> return (Just l)
        _      -> return Nothing
    -- But this case is actually impossible:
    toLevel t = fromMaybe __IMPOSSIBLE__ <$> toLevel' t

  caseMaybeM (toLevel' . absBody . snd . famThing $ ab) (return Nothing) $ \ _ -> do
  runNamesT [] $ do

    -- When doing transport in Pi types, we need to distinguish a couple
    -- of different cases depending on the sort of the domain, since
    -- there are a couple of different possibilities for how we end up
    -- with a fibrant Pi type:
    trFibrantDomain <- do
      let
        (x, f) = case ab of
          IsFam (a, _) -> (a, \ a -> runNames [] $ lam "i" (const (pure a)))
          IsNot (a, _) -> (a, id)
      s <- reduce $ getSort x
      case s of
        -- We're looking at a fibrant Pi with fibrant domain: Transport
        -- backwards along the domain.
        Type lx -> do
          [la, bA] <- mapM (open . f) [Level lx, unEl . unDom $ x]
          pure $ Just $ \iOrNot phi a0 ->
            pure tTrans <#> lam "j" (\j -> la <@> iOrNot j)
              <@> lam "j" (\ j -> bA <@> iOrNot j)
              <@> phi
              <@> a0

        -- We're looking a fibrant Pi whose domain is a lock: No need to do anything.
        LockUniv -> return $ Just $ \_ _ a0 -> a0

        -- We're looking at an unmarked path type. Make sure that the
        -- domain is actually the interval before continuing without an
        -- adjustment, though!
        IntervalUniv -> do
          x' <- reduceB $ unDom x
          mInterval <- getBuiltinName' builtinInterval
          case unEl $ ignoreBlocking x' of
            Def q [] | Just q == mInterval -> return $ Just $ \_ _ a0 -> a0
            _ -> return Nothing

        _ -> return Nothing

    caseMaybe trFibrantDomain (return Nothing) $ \trA -> Just <$> do
    [phi, u0] <- mapM (open . unArg) [ignoreBlocking (kanOpCofib cmd), kanOpBase cmd]

    glam (getArgInfo (fst $ famThing ab)) (absName $ snd $ famThing ab) $ \u1 -> do
      case (cmd, ab) of

        -- hcomp u u0 x = hcomp (λ i o → u i o x) (u0 x). Short and sweet :)
        (HCompOp _ u _, IsNot (a , b)) -> do
          bT <- (raise 1 b `absApp`) <$> u1
          u <- open (raise 1 (unArg u))
          pure tHComp
            <#> (Level <$> toLevel bT)
            <#> pure (unEl bT)
            <#> phi
            <@> lam "i" (\ i -> ilam "o" $ \ o -> gApply (getHiding a) (u <@> i <..> o) u1)
            <@> gApply (getHiding a) u0 u1

        -- transp (λ i → (a : A i) → B i x) φ f u1 =
        --  transp (λ i → B i (transp (λ j → A (i ∨ ~ j)) (φ ∨ i) x)) φ
        --    (f (transp (λ j → A (~ j) φ x)))
        (TranspOp _ _, IsFam (a , b)) -> do
          -- trA is a function of three arguments which builds the
          -- transport fillers in the opposite direction, hence its
          -- first argument is called "iOrNot" where it's relevant.
          let
            -- Γ , u1 : A[i1] , i : I
            v i = trA (imax i . ineg) (imax phi i) u1
            bB v = consS v (liftS 1 $ raiseS 1) `applySubst`
              (absBody b {- Γ , i : I , x : A[i] -})

            -- Compute B @0 v, in the right scope
            tLam = Lam defaultArgInfo

          -- We know how to substitute v into B, but it's open in a
          -- variable, so we close over it here:
          bT <- bind "i" $ \ x -> fmap bB . v $ x

          pure tTrans
            <#> (tLam <$> traverse (fmap Level . toLevel) bT)
            <@> (pure . tLam $ unEl <$> bT)
            <@> phi
            <@> gApply (getHiding a) u0 (v (pure iz))

        (_, _) -> __IMPOSSIBLE_VERBOSE__ "Invalid Kan operation in doPiKanOp"

-- | Compute Kan operations in a type of dependent paths.
doPathPKanOp
  :: KanOperation
  -> FamilyOrNot (Arg Term)
  -> FamilyOrNot (Arg Term, Arg Term, Arg Term)
  -> ReduceM (Reduced MaybeReducedArgs Term)
doPathPKanOp (HCompOp phi u u0) (IsNot l) (IsNot (bA,x,y)) = do
  let getTermLocal = getTerm "primHComp for path types"
  tHComp <- getTermLocal builtinHComp

  redReturn <=< runNamesT [] $ do
    [l, u, u0, phi, bA, x, y] <- mapM (open . unArg) [l, u, u0, ignoreBlocking phi, bA, x, y]

    -- hcomp in path spaces is simply hcomp in the underlying space, but
    -- fixing the endpoints at (j ∨ ~ j) in the new direction to those
    -- in the Path type.
    lam "j" $ \ j ->
      pure tHComp <#> l <#> (bA <@> j) <#> (phi `imax` (ineg j `imax` j))
        <@> lam "i'" (\i -> combineSys l (bA <@> i)
          [ (phi,    ilam "o" (\ o -> u <@> i <..> o <@@> (x, y, j)))
          , (j,      ilam "o" (const y))
          , (ineg j, ilam "o" (const x)) ])
        <@> (u0 <@@> (x, y, j))

doPathPKanOp (TranspOp phi u0) (IsFam l) (IsFam (bA,x,y)) = do
  let getTermLocal = getTerm "transport for path types"
  iz <- getTermLocal builtinIZero
  io <- getTermLocal builtinIOne

  -- Transport in path types becomes /CCHM/ composition in the
  -- underlying line of spaces. The intuition is that not only do we
  -- have to fix the endpoints (using composition) but also actually
  -- transport. CCHM composition conveniently does that for us!
  --
  -- Γ ⊢ l : I → Level
  --     l is already a function "coming in"
  -- Γ, i ⊢ bA   : Type (l i)
  -- Γ, i ⊢ x, y : bA
  -- Γ ⊢ u0 : PathP (A/i0) (x/i0) (y/i0)
  -- Γ, φ ⊢ bA constant
  --
  --   transp {l} (λ i → PathP A x y) φ p = λ j →
  --      comp {λ i → l j} (λ i → A i j) (φ ∨ j ∨ ~ j) λ i where
  --        (φ = i1 ∨ i = i0) → p j
  --        (j = i0)          → x i
  --        (j = i1)          → y i
  --   : PathP A/i1 x/i1 y/i1

  redReturn <=< runNamesT [] $ do
    -- In reality to avoid a round-trip between primComp we use mkComp
    -- here.
    comp <- mkComp $ "transport for path types"
    [l, u0, phi] <- traverse (open . unArg) [l, u0, ignoreBlocking phi]
    [bA, x, y] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [bA, x, y]
    -- Γ ⊢ bA : (i : I) → Type (l i)
    -- Γ ⊢ x, y : (i : I) → bA i

    lam "j" $ \ j ->
      comp l (lam "i" $ \ i -> bA <@> i <@> j) (phi `imax` (ineg j `imax` j))
        (lam "i'" $ \i -> combineSys (l <@> i) (bA <@> i <@> j)
          [ (phi, ilam "o" (\o -> u0 <@@> (x <@> pure iz, y <@> pure iz, j)))
          -- Note that here we have lines of endpoints, which we must
          -- apply to fix the endpoints:
          , (j,      ilam "_" (const (y <@> i)))
          , (ineg j, ilam "_" (const (x <@> i)))
          ])
        (u0 <@@> (x <@> pure iz, y <@> pure iz, j))
doPathPKanOp a0 _ _ = __IMPOSSIBLE__

redReturnNoSimpl :: a -> ReduceM (Reduced a' a)
redReturnNoSimpl = pure . YesReduction NoSimplification

primTransHComp :: Command -> [Arg Term] -> Int -> ReduceM (Reduced MaybeReducedArgs Term)
primTransHComp cmd ts nelims = do
  (l,bA,phi,u,u0) <- pure $ case (cmd,ts) of
    (DoTransp, [l, bA, phi, u0]) -> (IsFam l, IsFam bA, phi, Nothing, u0)
    (DoHComp, [l, bA, phi, u, u0]) -> (IsNot l, IsNot bA, phi, Just u, u0)
    _ -> __IMPOSSIBLE__
  sphi <- reduceB' phi
  vphi <- intervalView $ unArg $ ignoreBlocking sphi
  let clP s = getTerm "primTransHComp" s

  -- WORK
  case vphi of
    -- When φ = i1, we know what to do! These cases are counted as
    -- simplifications.
    IOne -> redReturn =<< case cmd of
      DoHComp -> runNamesT [] $ do
        -- If we're composing, then we definitely had a partial element
        -- to extend. But now it's just a total element, so we can
        -- just.. return it:
        u <- open $ unArg $ fromMaybe __IMPOSSIBLE__ u
        u <@> clP builtinIOne <..> clP builtinItIsOne
      DoTransp ->
        -- Otherwise we're in the constant part of the line to transport
        -- over, so we must return the argument unchanged.
        pure $ unArg u0

    _ -> do
    let
      fallback' sc = do
        -- Possibly optimise the partial element to reduce the size of
        -- hcomps:
        u' <- case cmd of
          DoHComp -> (:[]) <$> case vphi of
            -- If φ=i0 then tabulating equality for Partial φ A
            -- guarantees that u = is constantly isOneEmpty,
            -- regardless of how big the original term is, and
            -- isOneEmpty is *tiny*, so let's use that:
            IZero -> fmap (reduced . notBlocked . argN) . runNamesT [] $ do
                [l,c] <- mapM (open . unArg) [famThing l, ignoreBlocking sc]
                lam "i" $ \ i -> clP builtinIsOneEmpty <#> l <#> ilam "o" (\ _ -> c)

            -- Otherwise we have some interesting formula (though
            -- definitely not IOne!) and we have to keep the partial
            -- element as-is.
            _ -> pure $ notReduced $ fromMaybe __IMPOSSIBLE__ u
          DoTransp -> return []

        pure . NoReduction $ [notReduced (famThing l), reduced sc, reduced sphi] ++ u' ++ [notReduced u0]

    -- Reduce the type whose Kan operations we're composing over:
    sbA <- reduceB' bA
    t <- case unArg <$> ignoreBlocking sbA of
      IsFam (Lam _ t) -> Just . fmap IsFam <$> reduceB' (absBody t)
      IsFam _         -> pure Nothing
      IsNot t         -> pure . Just . fmap IsNot $ (t <$ sbA)

    case t of
      -- If we don't have a grasp of the Kan operations then at least we
      -- can reuse the work we did for reducing the type later.
      Nothing -> fallback' (famThing <$> sbA)
      Just st  -> do
        -- Similarly, if we're stuck for another reason, we can reuse
        -- the work for reducing the family.
        let
          fallback = fallback' (fmap famThing $ st *> sbA)
          t = ignoreBlocking st
          operation = case cmd of
            DoTransp -> TranspOp { kanOpCofib = sphi, kanOpBase = u0 }
            DoHComp -> HCompOp
              { kanOpCofib = sphi, kanOpSides = fromMaybe __IMPOSSIBLE__ u, kanOpBase = u0 }

        mHComp <- getPrimitiveName' builtinHComp
        mGlue <- getPrimitiveName' builtinGlue
        mId   <- getBuiltinName' builtinId
        pathV <- pathView'

        -- By cases on the family, determine what Kan operation we defer
        -- to:
        case famThing t of
          -- Metavariables are stuck
          MetaV m _ -> fallback' (fmap famThing $ blocked_ m *> sbA)

          -- TODO: absName t instead of "i"
          Pi a b
            -- For Π types, we prefer to keep the Kan operations around,
            -- so only actually reduce if we applied them to a nonzero
            -- positive of eliminations
            | nelims > 0 -> maybe fallback redReturn =<< doPiKanOp operation "i" ((a, b) <$ t)
            | otherwise -> fallback

          -- For Type, we have two possibilities:
          Sort (Type l)
            -- transp (λ i → Type _) φ is always the identity function.
            | DoTransp <- cmd -> redReturn $ unArg u0
            -- hcomp {Type} is actually a normal form! This is the
            -- "HCompU" optimisation; We do not use Glue for hcomp in
            -- the universe.
            | DoHComp <- cmd -> fallback

          -- Glue types have their own implementation of Kan operations
          -- which are implemented in a different module:
          Def q [Apply la, Apply lb, Apply bA, Apply phi', Apply bT, Apply e] | Just q == mGlue -> do
            maybe fallback redReturn =<< doGlueKanOp
              operation ((la, lb, bA, phi', bT, e) <$ t) Head

          -- Formal homogeneous compositions in the universe: Our family
          -- is @hcomp {A = Type l}@, so we defer to the implementation
          -- of Kan operations for HCompU implemented above.
          Def q [Apply _, Apply s, Apply phi', Apply bT, Apply bA]
            | Just q == mHComp, Sort (Type la) <- unArg s  -> do
            maybe fallback redReturn =<< doHCompUKanOp
              operation ((Level la <$ s, phi', bT, bA) <$ t) Head

          -- PathP types have the same optimisation as for Pi types:
          -- Only compute the Kan operation if there's >0 eliminations.
          d | PathType _ _ _ bA x y <- pathV (El __DUMMY_SORT__ d) -> do
            if nelims > 0 then doPathPKanOp operation l ((bA, x, y) <$ t) else fallback

          -- Identity types:
          Def q [Apply _ , Apply bA , Apply x , Apply y] | Just q == mId -> do
            maybe fallback return =<< doIdKanOp operation l ((bA, x, y) <$ t)

          Def q es -> do
            info <- getConstInfo q
            let
              lam_i = Lam defaultArgInfo . Abs "i"

              -- When should Kan operations on a record value reduce?
              doR r@Record{recEtaEquality' = eta} = case theEtaEquality eta of
                -- If it's a no-eta, pattern-matching record, then the
                -- Kan operations behave as they do for data types; Only
                -- reduce when the base is a constructor
                NoEta PatternMatching -> case unArg u0 of
                  Con{} -> True
                  _ -> False
                -- For every other case, we can reduce into a value
                -- defined by copatterns; However, this would expose the
                -- internal name of transp/hcomp when printed, so hold
                -- off until there are projections.
                _ -> nelims > 0
              doR _ = False

            -- Record and data types have their own implementations of
            -- the Kan operations, which get generated as part of their
            -- definition.
            case theDef info of
              r@Record{recComp = kit, recEtaEquality' = eta}
                | doR r, Just as <- allApplyElims es, DoTransp <- cmd, Just transpR <- nameOfTransp kit ->
                  -- Optimisation: If the record has no parameters then we can ditch the transport.
                  if recPars r == 0
                     then redReturn $ unArg u0
                     else redReturn $ Def transpR [] `apply` (map (fmap lam_i) as ++ [ignoreBlocking sphi, u0])

                -- Records know how to hcomp themselves:
                | doR r, Just as <- allApplyElims es, DoHComp <- cmd, Just hCompR <- nameOfHComp kit ->
                  redReturn $ Def hCompR [] `apply` (as ++ [ignoreBlocking sphi, fromMaybe __IMPOSSIBLE__ u,u0])

                -- If this is a record with no fields, then compData
                -- will know what to do with it:
                | Just as <- allApplyElims es, [] <- recFields r -> compData Nothing False (recPars r) cmd l (as <$ t) sbA sphi u u0

              -- For data types, if this data type is indexed and/or a
              -- higher inductive type, then hcomp is normal; But
              -- compData knows what to do for the general cases.
              Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons, dataTransp = mtrD}
                | and [null pcons && ixs == 0 | DoHComp  <- [cmd]], Just as <- allApplyElims es ->
                  compData mtrD ((not $ null $ pcons) || ixs > 0) (pars+ixs) cmd l (as <$ t) sbA sphi u u0

              -- Is this an axiom with constrant transport? Then. Well. Transport is constant.
              Axiom constTransp | constTransp, [] <- es, DoTransp <- cmd -> redReturn $ unArg u0

              _          -> fallback

          _ -> fallback
  where
    allComponentsBack unview phi u p = do
            let
              boolToI b = if b then unview IOne else unview IZero
              lamlam t = Lam defaultArgInfo (Abs "i" (Lam (setRelevance Irrelevant defaultArgInfo) (Abs "o" t)))
            as <- decomposeInterval phi
            (flags,t_alphas) <- fmap unzip . forM as $ \ (bs,ts) -> do
                 let u' = listS bs' `applySubst` u
                     bs' = IntMap.toAscList $ IntMap.map boolToI bs
                     -- Γ₁, i : I, Γ₂, j : I, Γ₃  ⊢ weaken : Γ₁, Γ₂, Γ₃   for bs' = [(j,_),(i,_)]
                     -- ordering of "j,i,.." matters.
                 let weaken = foldr (\ j s -> s `composeS` raiseFromS j 1) idS (map fst bs')
                 t <- reduce2Lam u'
                 return $ (p $ ignoreBlocking t, listToMaybe [ (weaken `applySubst` (lamlam <$> t),bs) | null ts ])
            return $ (flags,t_alphas)
    compData mtrD False _ cmd@DoHComp (IsNot l) (IsNot ps) fsc sphi (Just u) a0 = do
      let getTermLocal :: IsBuiltin a => a -> ReduceM Term
          getTermLocal = getTerm $ "builtinHComp for data types"

      let sc = famThing <$> fsc
      tEmpty <- getTermLocal builtinIsOneEmpty
      tPOr   <- getTermLocal builtinPOr
      iO   <- getTermLocal builtinIOne
      iZ   <- getTermLocal builtinIZero
      tMin <- getTermLocal builtinIMin
      tNeg <- getTermLocal builtinINeg
      let iNeg t = tNeg `apply` [argN t]
          iMin t u = tMin `apply` [argN t, argN u]
          iz = pure iZ
      constrForm <- do
        mz <- getTerm' builtinZero
        ms <- getTerm' builtinSuc
        return $ \ t -> fromMaybe t (constructorForm' mz ms t)
      su  <- reduceB' u
      sa0 <- reduceB' a0
      view   <- intervalView'
      unview <- intervalUnview'
      let f = unArg . ignoreBlocking
          phi = f sphi
          a0 = f sa0
          isLit t@(Lit lt) = Just t
          isLit _ = Nothing
          isCon (Con h _ _) = Just h
          isCon _           = Nothing
          combine l ty d [] = d
          combine l ty d [(psi,u)] = u
          combine l ty d ((psi,u):xs)
            = pure tPOr <#> l <@> psi <@> foldr (imax . fst) iz xs
                        <#> ilam "o" (\ _ -> ty) -- the type
                        <@> u <@> (combine l ty d xs)
          noRed' su = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced su', reduced sa0]
            where
              su' = case view phi of
                     IZero -> notBlocked $ argN $ runNames [] $ do
                                 [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                                 lam "i" $ \ i -> pure tEmpty <#> l
                                                              <#> ilam "o" (\ _ -> c)
                     _     -> su
          sameConHeadBack Nothing Nothing su k = noRed' su
          sameConHeadBack lt h su k = do
            let u = unArg . ignoreBlocking $ su
            (b, ts) <- allComponentsBack unview phi u $ \ t ->
                        (isLit t == lt, isCon (constrForm t) == h)
            let
              (lit,hd) = unzip b

            if isJust lt && and lit then redReturn a0 else do
            su <- caseMaybe (sequence ts) (return su) $ \ ts -> do
              let (us,bools) = unzip ts
              fmap ((sequenceA_ us $>) . argN) $ do
              let
                phis :: [Term]
                phis = for bools $ \ m ->
                            foldr (iMin . (\(i,b) -> applyUnless b iNeg $ var i)) iO (IntMap.toList m)
              runNamesT [] $ do
                u <- open u
                [l,c] <- mapM (open . unArg) [l,ignoreBlocking sc]
                phis <- mapM open phis
                us   <- mapM (open . ignoreBlocking) us
                lam "i" $ \ i -> do
                  combine l c (u <@> i) $ zip phis (map (\ t -> t <@> i) us)

            if isJust h && and hd then k (fromMaybe __IMPOSSIBLE__ h) su
                      else noRed' su

      sameConHeadBack (isLit a0) (isCon a0) su $ \ h su -> do
            let u = unArg . ignoreBlocking $ su
            Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
            case nameOfHComp cm of
              Just hcompD -> redReturn $ Def hcompD [] `apply`
                                          (ps ++ map argN [phi,u,a0])
              Nothing        -> noRed' su

    compData mtrD        _     0     DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = redReturn $ unArg a0
    compData (Just trD) isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
      let sc = famThing <$> fsc
      let f = unArg . ignoreBlocking
          phi :: Term
          phi = f $ sphi
      let lam_i = Lam defaultArgInfo . Abs "i"
      redReturn $ Def trD [] `apply` (map (fmap lam_i) ps ++ map argN [phi,unArg a0])

    compData mtrD isHIT _ cmd@DoTransp (IsFam l) (IsFam ps) fsc sphi Nothing a0 = do
      let getTermLocal :: IsBuiltin a => a -> ReduceM Term
          getTermLocal = getTerm $ getBuiltinId builtinTrans ++ " for data types"
      let sc = famThing <$> fsc
      mhcompName <- getName' builtinHComp
      constrForm <- do
        mz <- getTerm' builtinZero
        ms <- getTerm' builtinSuc
        return $ \ t -> fromMaybe t (constructorForm' mz ms t)
      sa0 <- reduceB' a0
      let f = unArg . ignoreBlocking
          phi = f sphi
          a0 = f sa0
          noRed = return $ NoReduction [notReduced l,reduced sc, reduced sphi, reduced sa0]
      let lam_i = Lam defaultArgInfo . Abs "i"
      case constrForm a0 of
        Con h _ args -> do
          Constructor{ conComp = cm } <- theDef <$> getConstInfo (conName h)
          case nameOfTransp cm of
              Just transpD -> redReturn $ Def transpD [] `apply`
                                          (map (fmap lam_i) ps ++ map argN [phi,a0])
              Nothing        -> noRed
        Def q es | isHIT, Just q == mhcompName, Just [_l0,_c0,psi,u,u0] <- allApplyElims es -> do
           let bC = ignoreBlocking sc
           hcomp <- getTermLocal builtinHComp
           transp <- getTermLocal builtinTrans
           io <- getTermLocal builtinIOne
           iz <- getTermLocal builtinIZero
           redReturn <=< runNamesT [] $ do
             [l,bC,phi,psi,u,u0] <- mapM (open . unArg) [l,bC,ignoreBlocking sphi,psi,u,u0]
             -- hcomp (sc 1) [psi |-> transp sc phi u] (transp sc phi u0)
             pure hcomp <#> (l <@> pure io) <#> (bC <@> pure io) <#> psi
                   <@> lam "j" (\ j -> ilam "o" $ \ o ->
                        pure transp <#> l <@> bC <@> phi <@> (u <@> j <..> o))
                   <@> (pure transp <#> l <@> bC <@> phi <@> u0)
        _ -> noRed
    compData mtrX isHITorIx nargs cmd l t sbA sphi u u0 = do
      () <- reportSDoc "impossible" 10 $ "compData" <+> (nest 2 . vcat)
       [ "mtrX:       " <+> pretty mtrX
       , "isHITorIx:  " <+> pretty isHITorIx
       , "nargs:      " <+> pretty nargs
       , "cmd:        " <+> text (show cmd)
       , "l:          " <+> familyOrNot l
       , "t:          " <+> familyOrNot t <+> pretty (famThing t)
       , "sbA:          " <+> familyOrNot (ignoreBlocking $ sbA)
       , "sphi:       " <+> pretty (ignoreBlocking sphi)
       , "isJust u:   " <+> pretty (isJust u)
       , "u0:         " <+> pretty u0
       ]
      __IMPOSSIBLE__

--    compData _ _ _ _ _ _ _ _ _ _ = __IMPOSSIBLE__

-- | CCHM 'primComp' is implemented in terms of 'hcomp' and 'transport'.
-- The definition of it comes from 'mkComp'.
primComp :: TCM PrimitiveImpl
primComp = do
  requireCubical CErased ""
  t    <- runNamesT [] $
          hPi' "a" (primIntervalType --> els (pure LevelUniv) (cl primLevel)) $ \ a ->
          nPi' "A" (nPi' "i" primIntervalType $ \ i -> (sort . tmSort <$> (a <@> i))) $ \ bA ->
          hPi' "φ" primIntervalType $ \ phi ->
          nPi' "i" primIntervalType (\ i -> pPi' "o" phi $ \ _ -> el' (a <@> i) (bA <@> i)) -->
          (el' (a <@> cl primIZero) (bA <@> cl primIZero) --> el' (a <@> cl primIOne) (bA <@> cl primIOne))
  one <- primItIsOne
  io  <- primIOne
  return $ PrimImpl t $ PrimFun __IMPOSSIBLE__ 5 $ \ ts nelims -> do
    case ts of
      [l,c,phi,u,a0] -> do
        sphi <- reduceB' phi
        vphi <- intervalView $ unArg $ ignoreBlocking sphi
        case vphi of
          -- Though we short-circuit evaluation for the rule
          --    comp A i1 (λ _ .1=1 → u) u ==> u
          -- rather than going through the motions of hcomp and transp.
          IOne -> redReturn (unArg u `apply` [argN io, argN one])
          _    -> do
            redReturnNoSimpl <=< runNamesT [] $ do
              comp <- mkComp (getBuiltinId PrimComp)
              [l,c,phi,u,a0] <- mapM (open . unArg) [l,c,phi,u,a0]
              comp l c phi u a0

      _ -> __IMPOSSIBLE__


-- TODO Andrea: keep reductions that happen under foralls?
primFaceForall' :: TCM PrimitiveImpl
primFaceForall' = do
  requireCubical CErased ""
  t <- (primIntervalType --> primIntervalType) --> primIntervalType
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 1 $ \case
    [phi] -> do
      sphi <- reduceB' phi
      case unArg $ ignoreBlocking $ sphi of
        Lam _ t -> do
          t <- reduce' t
          case t of
            NoAbs _ t -> redReturn t
            Abs _ t ->
              maybe (return $ NoReduction [reduced sphi]) redReturn
                =<< toFaceMapsPrim t
        _ -> return (NoReduction [reduced sphi])
    _ -> __IMPOSSIBLE__
  where
    toFaceMapsPrim t = do
      view <- intervalView'
      unview <- intervalUnview'
      us' <- decomposeInterval t
      fr <- getTerm (getBuiltinId PrimFaceForall) PrimFaceForall
      let
        v = view t
        -- We decomposed the interval expression, without regard for
        -- inconsistent mappings, and now we keep only those which are
        -- stuck (the ts) and those which do not mention the 0th variable.
        us :: [[Either (Int, Bool) Term]]
        us = [ map Left (IntMap.toList bsm) ++ map Right ts
             | (bsm, ts) <- us', 0 `IntMap.notMember` bsm
             ]

        -- Turn a face mapping back into an interval expression:
        fm (i, b) = if b then var (i - 1) else unview (INeg (argN (var $ i - 1)))
        -- Apply ∀ to any indecomposable expressions we have encountered
        ffr t = fr `apply` [argN $ Lam defaultArgInfo $ Abs "i" t]

        -- Unfold one step of the foldr to avoid generation of the last
        -- ∧ i1. Marginal savings at best but it's cleaner.
        conjuncts :: [Either (Int, Bool) Term] -> Term
        conjuncts [] = unview IOne
        conjuncts [x] = either fm ffr x
        conjuncts (x:xs) =
          foldr (\x r -> unview (IMin (argN (either fm ffr x)) (argN r)))
            (either fm ffr x)
            xs

        disjuncts = foldr
          (\conj rest -> unview (IMax (argN (conjuncts conj)) (argN rest)))
          (unview IZero)
          us
      --   traceSLn "cube.forall" 20 (unlines [show v, show us', show us, show r]) $
      return $ case us' of
        [(m, [_])] | null m -> Nothing
        _ -> Just disjuncts

-- | Tries to @primTransp@ a whole telescope of arguments, following the rule for Σ types.
--   If a type in the telescope does not support transp, @transpTel@ throws it as an exception.
transpTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[1]
transpTel = transpTel' False


transpTel' :: (PureTCM m, MonadError TCErr m) =>
          Bool -> Abs Telescope -- Γ ⊢ i.Δ
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) m Args      -- Γ ⊢ Δ[1]
transpTel' flag delta phi args = transpSysTel' flag delta [] phi args

type LM m a = NamesT (ExceptT (Closure (Abs Type)) m) a
-- transporting with an extra system/partial element
-- or composing when some of the system is known to be constant.
transpSysTel' :: forall m. (PureTCM m, MonadError TCErr m) =>
          Bool
          -> Abs Telescope -- Γ ⊢ i.Δ
          -> [(Term,Abs [Term])] -- [(ψ,i.δ)] with  Γ,ψ ⊢ i.δ : [i : I]. Δ[i]  -- the proof of [ψ] is not in scope.
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ and all i.δ const on φ ∧ ψ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) m Args      -- Γ ⊢ Δ[1]
transpSysTel' flag delta us phi args = do
  reportSDoc "cubical.prim.transpTel" 20 $
      sep [ text "transpSysTel'"
          , (text "delta  =" <+>) $ nest 2 $ addContext ("i" :: String, __DUMMY_DOM__) $ prettyTCM (unAbs delta)
--          , (text "us =" <+>) $ nest 2 $ prettyList $ map prettyTCM us
          , (text "phi    =" <+>) $ nest 2 $ prettyTCM phi
          , (text "args   =" <+>) $ nest 2 $ prettyList $ map prettyTCM args
          ]
  let getTermLocal :: IsBuiltin a => a -> ExceptT e m Term
      getTermLocal = getTerm "transpSys"
  tTransp <- lift primTrans
  tComp <- getTermLocal builtinComp
  tPOr <- getTermLocal builtinPOr
  iz <- lift primIZero
  imin <- lift primIMin
  imax <- lift primIMax
  ineg <- lift primINeg
  let
    noTranspError t = do
      reportSDoc "cubical.prim.transpTel" 20 $ nest 2 $ (text "error type =" <+>) $
        addContext ("i" :: String, __DUMMY_DOM__) $ prettyTCM $ unAbs t
      lift . throwError =<< buildClosure t
    bapp :: forall m a. (Applicative m, Subst a) => m (Abs a) -> m (SubstArg a) -> m a
    bapp t u = lazyAbsApp <$> t <*> u
    doGTransp l t us phi a | null us = pure tTransp <#> l <@> (Lam defaultArgInfo . fmap unEl <$> t) <@> phi <@> a
                           | otherwise = pure tComp <#> l <@> (Lam defaultArgInfo . fmap unEl <$> t) <#> face <@> uphi <@> a
      where
        -- [phi -> a; us]
        face = foldr (\ x y -> pure imax <@> x <@> y) (pure iz) (phi : map fst us)
        uphi = lam "i" $ \ i -> ilam "o" $ \ o -> do
          let sys' = (phi , a) : map (mapSnd (`bapp` i)) us
              sys = map (mapSnd $ ilam "o" . const) sys'
          combine (l <@> i) (unEl <$> bapp t i) __IMPOSSIBLE__ sys <..> o
    combine l ty d [] = d
    combine l ty d [(psi,u)] = u
    combine l ty d ((psi,u):xs)
            = pure tPOr <#> l <@> psi <@> (foldr (\ x y -> pure imax <@> x <@> y) (pure iz) (map fst xs))
                        <#> (ilam "o" $ \ _ -> ty) -- the type
                        <@> u <@> (combine l ty d xs)

    gTransp :: Maybe (LM m Term) -> LM m (Abs Type) -> [(LM m Term,LM m (Abs Term))] -> LM m Term -> LM m Term -> LM m Term
    gTransp (Just l) t u phi a
     | flag = do
      t' <- t
      us' <- mapM snd u
      case ( 0 `freeIn` (raise 1 t' `lazyAbsApp` var 0)
           , 0 `freeIn` map (\ u -> raise 1 u `lazyAbsApp` var 0) us'
           ) of
        (False,False) -> a
        (False,True)  -> doGTransp l t u phi a -- TODO? optimize to "hcomp (l <@> io) (bapp t io) ((phi,NoAbs a):u) a" ?
        (True,_) -> doGTransp l t u phi a
     | otherwise = doGTransp l t u phi a

    gTransp Nothing t sys phi a = do
      let (psis,us) = unzip sys
      -- Γ ⊢ i.Ξ
      xi <- (open =<<) $ do
        bind "i" $ \ i -> do
          TelV xi _ <- (lift . telView =<<) $ t `bapp` i
          return xi
      argnames <- do
        teleArgNames . unAbs <$> xi
      glamN argnames $ \ xi_args -> do
        b' <- bind "i" $ \ i -> do
          ti <- t `bapp` i
          xin <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          xi_args <- xi_args
          ni <- pure ineg <@> i
          phi <- phi
          lift $ piApplyM ti =<< trFillTel' flag xin phi xi_args ni
        usxi <- forM us $ \ u -> bind "i" $ \ i -> do
          ui <- u `bapp` i
          xin <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          xi_args <- xi_args
          ni <- pure ineg <@> i
          phi <- phi
          lift $ apply ui <$> trFillTel' flag xin phi xi_args ni
        axi <- do
          a <- a
          xif <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          phi <- phi
          xi_args <- xi_args
          lift $ apply a <$> transpTel' flag xif phi xi_args
        s <- reduce $ getSort (absBody b')
        reportSDoc "cubical.transp" 20 $ pretty (raise 1 b' `lazyAbsApp` var 0)
        let noTranspSort = if 0 `freeIn` (raise 1 b' `lazyAbsApp` var 0) || 0 `freeIn` (map (`lazyAbsApp` var 0) (raise 1 usxi))
              then noTranspError b'
              else return axi

        case s of
          Type l -> do
            l <- open $ lam_i (Level l)
            b' <- open b'
            axi <- open axi
            usxi <- mapM open usxi
            gTransp (Just l) b' (zip psis usxi) phi axi
          Inf _ _  -> noTranspSort
          SSet _  -> noTranspSort
          SizeUniv -> noTranspSort
          LockUniv -> noTranspSort
          IntervalUniv -> noTranspSort
          Prop{}  -> noTranspSort
          _ -> noTranspError b'
    lam_i = Lam defaultArgInfo . Abs "i"
    go :: Telescope -> [[(Term,Term)]] -> Term -> Args -> ExceptT (Closure (Abs Type)) m Args
    go EmptyTel            [] _  []       = return []
    go (ExtendTel t delta) (u:us) phi (a:args) = do
      -- Γ,i ⊢ t
      -- Γ,i ⊢ (x : t). delta
      -- Γ ⊢ a : t[0]
      s <- reduce $ getSort t
      -- Γ ⊢ b : t[1]    Γ, i ⊢ bf : t[i]
      (b,bf) <- runNamesT [] $ do
        l <- case s of
               SSet _ -> return Nothing
               IntervalUniv -> return Nothing
               SizeUniv     -> return Nothing
               LockUniv     -> return Nothing
               Inf _ _ -> return Nothing
               Type l -> Just <$> open (lam_i (Level l))
               _ -> noTranspError (Abs "i" (unDom t))
        t <- open $ Abs "i" (unDom t)
        u <- forM u $ \ (psi,upsi) -> do
              (,) <$> open psi <*> open (Abs "i" upsi)
        [phi,a] <- mapM open [phi, unArg a]
        b <- gTransp l t u phi a
        bf <- bind "i" $ \ i -> do
                            gTransp ((<$> l) $ \ l -> lam "j" $ \ j -> l <@> (pure imin <@> i <@> j))
                                    (bind "j" $ \ j -> t `bapp` (pure imin <@> i <@> j))
                                    u
                                    (pure imax <@> (pure ineg <@> i) <@> phi)
                                    a
        return (b, absBody bf)
      (:) (b <$ a) <$> go (lazyAbsApp delta bf) us phi args
    go EmptyTel            _ _ _ = __IMPOSSIBLE__
    go (ExtendTel t delta) _ _ _ = __IMPOSSIBLE__
  let (psis,uss) = unzip us
      us' | null us = replicate (length args) []
          | otherwise = map (zip psis) $ List.transpose (map absBody uss)
  go (absBody delta) us' phi args

-- | Like @transpTel@ but performing a transpFill.
trFillTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> Term          -- Γ ⊢ r : I
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[r]
trFillTel = trFillTel' False

trFillTel' :: (PureTCM m, MonadError TCErr m) =>
          Bool
          -> Abs Telescope -- Γ ⊢ i.Δ
          -> Term
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> Term          -- Γ ⊢ r : I
          -> ExceptT (Closure (Abs Type)) m Args      -- Γ ⊢ Δ[r]
trFillTel' flag delta phi args r = do
  imin <- lift primIMin
  imax <- lift primIMax
  ineg <- lift primINeg
  transpTel' flag (Abs "j" $ raise 1 delta `lazyAbsApp` (imin `apply` (map argN [var 0, raise 1 r])))
            (imax `apply` [argN $ ineg `apply` [argN r], argN phi])
            args



-- hcompTel' :: Bool -> Telescope -> [(Term,Abs [Term])] -> [Term] -> ExceptT (Closure (Abs Type)) TCM [Term]
-- hcompTel' b delta sides base = undefined

-- hFillTel' :: Bool -> Telescope -- Γ ⊢ Δ
--           -> [(Term,Abs [Term])]  -- [(φ,i.δ)] with  Γ,φ ⊢ i.δ : I → Δ
--           -> [Term]            -- Γ ⊢ δ0 : Δ, matching the [(φ,i.δ)]
--           -> Term -- Γ ⊢ r : I
--           -> ExceptT (Closure (Abs Type)) TCM [Term]
-- hFillTel' b delta sides base = undefined

pathTelescope
  :: forall m. (PureTCM m, MonadError TCErr m) =>
  Telescope -- Δ
  -> [Arg Term] -- lhs : Δ
  -> [Arg Term] -- rhs : Δ
  -> m Telescope
pathTelescope tel lhs rhs = do
  x <- runExceptT (pathTelescope' tel lhs rhs)
  case x of
    Left t -> do
      enterClosure t $ \ t ->
                 typeError . GenericDocError =<<
                    (text "The sort of" <+> pretty t <+> text "should be of the form \"Set l\"")
    Right tel -> return tel

pathTelescope'
  :: forall m. (PureTCM m, MonadError (Closure Type) m) =>
  Telescope -- Δ
  -> [Arg Term] -- lhs : Δ
  -> [Arg Term] -- rhs : Δ
  -> m Telescope
pathTelescope' tel lhs rhs = do
  pathp <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinPathP
  go pathp (raise 1 tel) lhs rhs
 where
  -- Γ,i ⊢ Δ, Γ ⊢ lhs : Δ[0], Γ ⊢ rhs : Δ[1]
  go :: Term -> Telescope -> [Arg Term] -> [Arg Term] -> m Telescope
  go pathp (ExtendTel a tel) (u : lhs) (v : rhs) = do
    let t = unDom a
    l <- subst 0 __DUMMY_TERM__ <$> getLevel t
    let a' = El (Type l) (apply pathp $ [argH $ Level l] ++ map argN [Lam defaultArgInfo (Abs "i" $ unEl t), unArg u, unArg v])
        -- Γ,eq : u ≡ v, i : I ⊢ m = eq i : t[i]
        -- m  = runNames [] $ do
        --        [u,v] <- mapM (open . unArg) [u,v]
        --        bind "eq" $ \ eq -> bind "i" $ \ i ->
    (ExtendTel (a' <$ a) <$>) . runNamesT [] $ do
      let nm = (absName tel)
      tel <- open $ Abs "i" tel
      [u,v] <- mapM (open . unArg) [u,v]
      [lhs,rhs] <- mapM open [lhs,rhs]
      bind nm $ \ eq -> do
        lhs <- lhs
        rhs <- rhs
        tel' <- bind "i" $ \ i ->
                  lazyAbsApp <$> (lazyAbsApp <$> tel <*> i) <*> (eq <@@> (u, v, i))
        lift $ go pathp (absBody tel') lhs rhs
  go _ EmptyTel [] [] = return EmptyTel
  go _ _ _ _ = __IMPOSSIBLE__
  getLevel :: Type -> m Level
  getLevel t = do
    s <- reduce $ getSort t
    case s of
      Type l -> pure l
      s      -> throwError =<< buildClosure t

data TranspError = CannotTransp {errorType :: (Closure (Abs Type)) }

instance Exception TranspError
instance Show TranspError where
  show _ = "TranspError"

tryTranspError :: TCM a -> TCM (Either (Closure (Abs Type)) a)
tryTranspError (TCM m) = TCM $ \ s env -> do
  mapLeft errorType <$> (try (m s env))

transpPathPTel' ::
             NamesT TCM (Abs (Abs Telescope)) -- ^ j.i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[0,i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[1,i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : PathP (λ j → Δ[j,0]) (x 0) (y 0)
             -> NamesT TCM [Arg Term] -- PathP (λ j → Δ[j,0]) (x 1) (y 1) [ φ ↦ q ]
transpPathPTel' theTel x y phi p = do
 let neg j = cl primINeg <@> j
 -- is the open overkill?
 qs <- (open =<<) $ fmap (fmap (\ (Abs n (Arg i t)) -> Arg i (Lam defaultArgInfo $ Abs n t)) . sequenceA)
                  $ bind "j" $ \ j -> do
   theTel <- absApp <$> theTel <*> j
   faces <- sequence [neg j, j]
   us <- forM [x,y] $ \ z -> do
           bind "i" $ \ i -> forM z (<@> i)
   let sys = zip faces us
   -- [(neg j, bind "i" $ \ i -> flip map x (<@> i))
   -- ,(j , bind "i" $ \ i -> flip map y (<@> i))]
   phi <- phi
   p0 <- mapM (<@> j) p
   let toArgs = zipWith (\ a t -> t <$ a) (teleArgNames (unAbs $ theTel))
   eq <- lift . runExceptT $ transpSysTel' False theTel sys phi (toArgs p0)
   either (lift . lift . throw . CannotTransp) pure eq
 qs

transpPathTel' ::
             NamesT TCM (Abs Telescope) -- ^ i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : Path (Δ[0]) (x 0) (y 0)
             -> NamesT TCM [Arg Term] -- Path (Δ[1]) (x 1) (y 1) [ φ ↦ q ]
transpPathTel' theTel x y phi p = do
 let neg j = cl primINeg <@> j
 -- is the open overkill?
 qs <- (open =<<) $ fmap (fmap (\ (Abs n (Arg i t)) -> Arg i (Lam defaultArgInfo $ Abs n t)) . sequenceA)
                  $ bind "j" $ \ j -> do
   theTel <- theTel
   faces <- sequence $ [neg j, j]
   us <- forM [x,y] $ \ z -> do
           bind "i" $ \ i -> forM z (<@> i)
   let sys = zip faces us
   -- [(neg j, bind "i" $ \ i -> flip map x (<@> i))
   -- ,(j , bind "i" $ \ i -> flip map y (<@> i))]
   phi <- phi
   p0 <- mapM (<@> j) p
   let toArgs = zipWith (\ a t -> t <$ a) (teleArgNames (unAbs theTel))
   eq <- lift . runExceptT $ transpSysTel' False theTel sys phi (toArgs p0)
   either (lift . lift . throw . CannotTransp) pure eq
 qs

trFillPathTel' ::
               NamesT TCM (Abs Telescope) -- ^ i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : Path (Δ[0]) (x 0) (y 0)
             -> NamesT TCM Term            -- ^ r
             -> NamesT TCM [Arg Term] -- Path (Δ[r]) (x r) (y r) [ φ ↦ q; (r = 0) ↦ q ]
trFillPathTel' tel x y phi p r = do
  let max i j = cl primIMin <@> i <@> j
  let min i j = cl primIMin <@> i <@> j
  let neg i = cl primINeg <@> i
  x' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM x (<@> (min r i))
  y' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM y (<@> (min r i))
  transpPathTel' (bind "i" $ \ i -> absApp <$> tel <*> min r i)
                 x'
                 y'
                 (max phi (neg r))
                 p

trFillPathPTel' ::
               NamesT TCM (Abs (Abs Telescope)) -- ^ j.i.Δ                 const on φ
             -> [NamesT TCM Term]          -- ^ x : (i : I) → Δ[0,i]  const on φ
             -> [NamesT TCM Term]          -- ^ y : (i : I) → Δ[1,i]  const on φ
             -> NamesT TCM Term            -- ^ φ
             -> [NamesT TCM Term]          -- ^ p : Path (\ j -> Δ[j,0]) (x 0) (y 0)
             -> NamesT TCM Term            -- ^ r
             -> NamesT TCM [Arg Term] -- Path (\ j → Δ[j,r]) (x r) (y r) [ φ ↦ q; (r = 0) ↦ q ]
trFillPathPTel' tel x y phi p r = do
  let max i j = cl primIMin <@> i <@> j
  let min i j = cl primIMin <@> i <@> j
  let neg i = cl primINeg <@> i
  x' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM x (<@> (min r i))
  y' <- (mapM open =<<) $ lamTel $ bind "i" $ \ i -> forM y (<@> (min r i))
  transpPathPTel' (bind "j" $ \ j -> bind "i" $ \ i -> absApp <$> (absApp <$> tel <*> j) <*> min r i)
                 x'
                 y'
                 (max phi (neg r))
                 p



-- given Γ ⊢ I type, and Γ ⊢ Δ telescope, build Δ^I such that
-- Γ ⊢ (x : A, y : B x, ...)^I = (x : I → A, y : (i : I) → B (x i), ...)
expTelescope :: Type -> Telescope -> Telescope
expTelescope int tel = unflattenTel names ys
  where
    stel = size tel
    xs = flattenTel tel
    names = teleNames tel
    t = ExtendTel (defaultDom $ raise stel int) (Abs "i" EmptyTel)
    s = expS stel
    ys = map (fmap (abstract t) . applySubst s) xs


-- | Γ, Δ^I, i : I |- expS |Δ| : Γ, Δ
expS :: Nat -> Substitution
expS stel = prependS __IMPOSSIBLE__
  [ Just (var n `apply` [Arg defaultArgInfo $ var 0]) | n <- [1..stel] ]
  (raiseS (stel + 1))


-- * Special cases of Type
-----------------------------------------------------------

-- | A @Type@ with sort @Type l@
--   Such a type supports both hcomp and transp.
data LType = LEl Level Term deriving (Eq,Show)

fromLType :: LType -> Type
fromLType (LEl l t) = El (Type l) t

lTypeLevel :: LType -> Level
lTypeLevel (LEl l t) = l

toLType :: MonadReduce m => Type -> m (Maybe LType)
toLType ty = do
  sort <- reduce $ getSort ty
  case sort of
    Type l -> return $ Just $ LEl l (unEl ty)
    _      -> return $ Nothing

instance Subst LType where
  type SubstArg LType = Term
  applySubst rho (LEl l t) = LEl (applySubst rho l) (applySubst rho t)

-- | A @Type@ that either has sort @Type l@ or is a closed definition.
--   Such a type supports some version of transp.
--   In particular we want to allow the Interval as a @ClosedType@.
data CType = ClosedType Sort QName | LType LType deriving (Eq,Show)

instance P.Pretty CType where
  pretty = P.pretty . fromCType

fromCType :: CType -> Type
fromCType (ClosedType s q) = El s (Def q [])
fromCType (LType t) = fromLType t

toCType :: MonadReduce m => Type -> m (Maybe CType)
toCType ty = do
  sort <- reduce $ getSort ty
  case sort of
    Type l -> return $ Just $ LType (LEl l (unEl ty))
    SSet{} -> do
      t <- reduce (unEl ty)
      case t of
        Def q [] -> return $ Just $ ClosedType sort q
        _        -> return $ Nothing
    _      -> return $ Nothing

instance Subst CType where
  type SubstArg CType = Term
  applySubst rho (ClosedType s q) = ClosedType (applySubst rho s) q
  applySubst rho (LType t) = LType $ applySubst rho t

hcomp
  :: (HasBuiltins m, MonadError TCErr m, MonadReduce m, MonadPretty m)
  => NamesT m Type
  -> [(NamesT m Term, NamesT m Term)]
  -> NamesT m Term
  -> NamesT m Term
hcomp ty sys u0 = do
  iz <- primIZero
  tHComp <- primHComp
  let max i j = cl primIMax <@> i <@> j
  ty <- ty
  (l, ty) <- toLType ty >>= \case
    Just (LEl l ty) -> return (l, ty)
    Nothing -> lift $ do -- TODO: support Setω properly
      typeError . GenericDocError =<< sep
        [ text "Cubical Agda: cannot generate hcomp clauses at type", prettyTCM ty ]
  l <- open $ Level l
  ty <- open $ ty
  face <- (foldr max (pure iz) $ map fst $ sys)
  sys <- lam "i'" $ \ i -> combineSys l ty [(phi, u <@> i) | (phi,u) <- sys]
  pure tHComp <#> l <#> ty <#> pure face <@> pure sys <@> u0

transpSys :: (HasBuiltins m, MonadError TCErr m, MonadReduce m) =>
               NamesT m (Abs Type) -- ty
               -> [(NamesT m Term, NamesT m Term)] -- sys
               -> NamesT m Term -- φ
               -> NamesT m Term
               -> NamesT m Term
transpSys ty sys phi u = do
  let max i j = cl primIMax <@> i <@> j
  iz <- primIZero
  tTransp <- primTrans
  tComp <- fromMaybe __IMPOSSIBLE__ <$> getTerm' builtinComp
  l_ty <- bind "i" $ \ i -> do
      ty <- absApp <$> ty <*> i
      toLType ty >>= \case
        Just (LEl l ty) -> return (l,ty)
        Nothing -> return (__DUMMY_LEVEL__, unEl ty) -- TODO: properly support Setω
  l <- open $ Lam defaultArgInfo . fmap (Level . fst) $ l_ty
  ty <- open $ Lam defaultArgInfo . fmap snd $ l_ty

  if null sys then pure tTransp <#> l <@> ty <@> phi <@> u else do

  let face = max phi (foldr max (pure iz) $ map fst $ sys)
  sys <- (open =<<) $ lam "i'" $ \ i -> do
    let base = (phi, ilam "o" $ \ _ -> u)
    combineSys l ty $ base : [(phi, u <@> i) | (phi,u) <- sys]

  pure tComp <#> l <@> ty <#> face <@> sys <@> u

debugClause :: String -> Clause -> TCM ()
debugClause s c = do
      reportSDoc s 20 $
        "gamma:" <+> prettyTCM gamma
      reportSDoc s 20 $ addContext gamma $
        "ps   :" <+> prettyTCM (patternsToElims ps)
      reportSDoc s 20 $ addContext gamma $
        "type :" <+> maybe "nothing" prettyTCM rhsTy
      reportSDoc s 20 $ addContext gamma $
        "body :" <+> maybe "nothing" prettyTCM rhs

      reportSDoc s 30 $
        addContext gamma $ "c:" <+> pretty c
  where
    gamma = clauseTel c
    ps = namedClausePats c
    rhsTy = clauseType c
    rhs = clauseBody c
