-- | Implementation of the primitives relating to Cubical identity types.
module Agda.TypeChecking.Primitive.Cubical.Id
  ( -- * General elimination form
    primIdElim'
  -- * Introduction form
  , primConId'
  -- * Projection maps (primarily used internally)
  , primIdFace'
  , primIdPath'
  -- * Kan operations
  , doIdKanOp
  )
  where

import Control.Monad.Except

import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad

import qualified Data.IntMap as IntMap
import Data.Traversable
import Data.Maybe

import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Substitute (apply, sort, listS, applySubst)
import Agda.TypeChecking.Reduce (reduceB', reduce')
import Agda.TypeChecking.Names
  (runNamesT, runNames, cl, lam, ilam, open)

import Agda.Interaction.Options.Base (optCubical)

import Agda.Syntax.Common (Cubical(..), Arg(..), defaultArgInfo, hasQuantity0, defaultArg)

import Agda.TypeChecking.Primitive.Base
  ((-->), nPi', pPi', hPi', el, el', el's, (<@>), (<#>), (<..>), argN)

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Debug (__IMPOSSIBLE_VERBOSE__)

import Agda.TypeChecking.Primitive.Cubical.Base

-- | Primitive elimination rule for the cubical identity types. Unlike
-- J, @idElim@ makes explicit the structure of Swan's identity types as
-- being pairs of a cofibration and a path. Moreover, it records that
-- the path is definitionally @refl@ under that cofibration.
primIdElim' :: TCM PrimitiveImpl
primIdElim' = do
  -- The implementation here looks terrible but most of it is actually
  -- the type.
  requireCubical CErased ""
  t <- runNamesT [] $
    hPi' "a" (el $ cl primLevel) $ \ a ->
    hPi' "c" (el $ cl primLevel) $ \ c ->
    hPi' "A" (sort . tmSort <$> a) $ \ bA ->
    hPi' "x" (el' a bA) $ \ x ->
    nPi' "C" (nPi' "y" (el' a bA) $ \ y ->
              el' a (cl primId <#> a <#> bA <@> x <@> y) --> (sort . tmSort <$> c)) $ \ bC ->
    -- To construct (C : (y : A) → Id A x y → Type c), it suffices to:

    -- For all cofibrations φ,
    nPi' "φ" primIntervalType (\ phi ->
      -- For all y : A [ φ → (λ _ → x) ]
      nPi' "y" (el's a $ cl primSub <#> a <@> bA <@> phi <@> lam "o" (const x)) $ \ y ->
      let pathxy = cl primPath <#> a <@> bA <@> x <@> outSy
          outSy  = cl primSubOut <#> a <#> bA <#> phi <#> lam "o" (const x) <@> y
          reflx  = lam "o" $ \ _ -> lam "i" $ \ _ -> x -- TODO Andrea, should block on o
      -- For all w : (Path A x (outS y)) [ φ (λ _ → refl {x = outS y} ]
      in nPi' "w" (el's a $ cl primSub <#> a <@> pathxy <@> phi <@> reflx) $ \ w ->
      let outSw = (cl primSubOut <#> a <#> pathxy <#> phi <#> reflx <@> w)
      in el' c $ bC <@> outSy <@> (cl primConId <#> a <#> bA <#> x <#> outSy <@> phi <@> outSw))
      -- Construct an inhabitant of (C (outS y) (conid φ (outS w)))
    -->
    hPi' "y" (el' a bA) (\ y ->
      nPi' "p" (el' a $ cl primId <#> a <#> bA <@> x <@> y) $ \ p ->
      el' c $ bC <@> y <@> p)

  -- Implementation starts here:
  conid <- primConId
  sin <- primSubIn
  path <- primPath
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \case
    [a,c,bA,x,bC,f,y,p] -> do
      sp <- reduceB' p
      cview <- conidView'
      case cview (unArg x) $ unArg $ ignoreBlocking sp of
        -- Record that the right endpoint and the path definitionally
        -- agree with x φ holds. This is guaranteed internally by the
        -- typing rule for @conId@ but can't be recovered from
        -- @primIdPath@ and @primIdFace@ (see #2598)
        Just (phi, w) -> do
          let y' = sin `apply` [a, bA, phi, argN (unArg y)]
          let w' = sin `apply` [a, argN (path `apply` [a, bA, x, y]), phi, argN (unArg w)]
          redReturn $ unArg f `apply` [phi, defaultArg y', defaultArg w']
        _ -> return $ NoReduction $ map notReduced [a,c,bA,x,bC,f,y] ++ [reduced sp]
    _ -> __IMPOSSIBLE_VERBOSE__ "implementation of primIdElim called with wrong arity"

-- | Introduction form for the cubical identity types.
primConId' :: TCM PrimitiveImpl
primConId' = do
  requireCubical CErased ""
  t <- runNamesT [] $
    hPi' "a" (el $ cl primLevel) $ \ a ->
    hPi' "A" (sort . tmSort <$> a) $ \ bA ->
    hPi' "x" (el' a bA) $ \ x ->
    hPi' "y" (el' a bA) $ \ y ->
    primIntervalType -- Cofibration
    --> (el' a $ cl primPath <#> a <#> bA <@> x <@> y)
    --> (el' a $ cl primId <#> a <#> bA <@> x <@> y)

  -- Implementation note: conId, as the name implies, is a constructor.
  -- It's not represented as a constructor because users can't match on
  -- it (but we, internally, can: see createMissingConIdClause).

  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \case
    [l,bA,x,y,phi,p] -> do
      sphi <- reduceB' phi
      view <- intervalView'
      case view $ unArg $ ignoreBlocking sphi of
        -- But even though it's a constructor, it does reduce, in some
        -- cases: If the cofibration is definitely true, then we return
        -- reflId.  TODO: Handle this in the conversion checker instead?
        IOne -> do
          reflId <- getTerm (getBuiltinId builtinConId) builtinReflId
          redReturn $ reflId
        _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced sphi, notReduced p]
    _ -> __IMPOSSIBLE_VERBOSE__ "implementation of primConId called with wrong arity"

-- | Extract the underlying cofibration from an inhabitant of the
-- cubical identity types.
--
-- TODO (Amy, 2022-08-17): Projecting a cofibration from a Kan type
-- violates the cubical phase distinction.
primIdFace' :: TCM PrimitiveImpl
primIdFace' = do
  requireCubical CErased ""
  t <- runNamesT [] $
    hPi' "a" (el $ cl primLevel) $ \ a ->
    hPi' "A" (sort . tmSort <$> a) $ \ bA ->
    hPi' "x" (el' a bA) $ \ x ->
    hPi' "y" (el' a bA) $ \ y ->
    el' a (cl primId <#> a <#> bA <@> x <@> y)
    --> primIntervalType

  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \case
    [l,bA,x,y,t] -> do
      st <- reduceB' t
      mConId <- getName' builtinConId
      cview <- conidView'
      case cview (unArg x) $ unArg (ignoreBlocking st) of
        Just (phi, _) -> redReturn (unArg phi)
        _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
    _ -> __IMPOSSIBLE__

-- | Extract the underlying path from an inhabitant of the
-- cubical identity types.
primIdPath' :: TCM PrimitiveImpl
primIdPath' = do
  requireCubical CErased ""
  t <- runNamesT [] $
    hPi' "a" (el $ cl primLevel) $ \ a ->
    hPi' "A" (sort . tmSort <$> a) $ \ bA ->
    hPi' "x" (el' a bA) $ \ x ->
    hPi' "y" (el' a bA) $ \ y ->
    el' a (cl primId <#> a <#> bA <@> x <@> y)
    --> el' a (cl primPath <#> a <#> bA <@> x <@> y)

  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \case
    [l,bA,x,y,t] -> do
      st <- reduceB' t
      mConId <- getName' builtinConId
      cview <- conidView'
      case cview (unArg x) $ unArg (ignoreBlocking st) of
        Just (_, w) -> redReturn (unArg w)
        _ -> return $ NoReduction $ map notReduced [l,bA,x,y] ++ [reduced st]
    _ -> __IMPOSSIBLE__

-- | Check that a term matches a given predicate on every consistent
-- substitution of interval variables which makes the given cofibration
-- hold.
onEveryFace
  :: Term -- ^ The cofibration @φ@
  -> Term -- ^ The term to test
  -> (Term -> Bool)
  -- ^ The predicate to test with.
  -> ReduceM Bool
onEveryFace phi u p = do
  unview <- intervalUnview'
  let boolToI b = if b then unview IOne else unview IZero
  as <- decomposeInterval phi
  bools <- for as $ \ (bs,ts) -> do
    let u' = listS (IntMap.toAscList $ IntMap.map boolToI bs) `applySubst` u
    t <- reduce2Lam u'
    return $! p $ ignoreBlocking t
  pure (and bools)

doIdKanOp
  :: KanOperation           -- ^ Are we composing or transporting?
  -> FamilyOrNot (Arg Term) -- ^ Level argument
  -> FamilyOrNot (Arg Term, Arg Term, Arg Term)
    -- ^ Domain, left and right endpoints of the identity type
  -> ReduceM (Maybe (Reduced t Term))
doIdKanOp kanOp l bA_x_y = do
  let getTermLocal :: IsBuiltin a => a -> ReduceM Term
      getTermLocal = getTerm $ kanOpName kanOp ++ " for " ++ getBuiltinId builtinId

  unview <- intervalUnview'
  mConId <- getName' builtinConId
  cview <- conidView'
  let isConId t = isJust $ cview __DUMMY_TERM__ t

  sa0 <- reduceB' (kanOpBase kanOp)
  -- TODO: wasteful to compute b even when cheaper checks might fail
  --
  -- Should we go forward with the Kan operation? This is the case when
  -- doing transport always, and when every face fo the partial element
  -- has reduced to @conid@ otherwise. Note that @conidView@ treats
  -- @reflId@ as though it were @conid i1 refl@.
  b <- case kanOp of
    TranspOp{}    -> return True
    HCompOp _ u _ ->
      onEveryFace (unArg . ignoreBlocking . kanOpCofib $ kanOp) (unArg u) isConId

  case mConId of
    Just conid | isConId (unArg . ignoreBlocking $ sa0), b -> (Just <$>) . (redReturn =<<) $ do
      tHComp    <- getTermLocal builtinHComp
      tTrans    <- getTermLocal builtinTrans
      tIMin     <- getTermLocal builtinDepIMin
      idFace    <- getTermLocal builtinIdFace
      idPath    <- getTermLocal builtinIdPath
      tPathType <- getTermLocal builtinPath
      tConId    <- getTermLocal builtinConId

      runNamesT [] $ do
        let
          io = pure $ unview IOne
          iz = pure $ unview IZero
          conId = pure tConId

          eval TranspOp{} l bA phi _ u0 =
            pure tTrans <#> l <@> bA <@> phi <@> u0
          eval HCompOp{} l bA phi u u0 =
            pure tHComp <#> (l <@> io) <#> (bA <@> io) <#> phi <@> u <@> u0

        -- Compute a line of levels. So we can invoke 'eval' uniformly.
        l <- case l of
          IsFam l -> open . unArg $ l
          IsNot l -> open (Lam defaultArgInfo $ NoAbs "_" $ unArg l)

        p0 <- open . unArg $ kanOpBase kanOp

        -- p is the partial element we are extending against. This is
        -- used to compute the resulting cofibration, so we fake a
        -- partial element when doing transport.
        p <- case kanOp of
          HCompOp _ u _ -> do
            u <- open . unArg $ u
            pure $ \i o -> u <@> i <..> o
          TranspOp{} -> do
            pure $ \i o -> p0

        phi <- open . unArg . ignoreBlocking $ kanOpCofib kanOp

        -- Similarly to the fake line of levels above, fake lines of
        -- everything even when we're doing composition, for uniformity
        -- of eval.
        [bA, x, y] <- case bA_x_y of
          IsFam (bA, x, y) -> for [bA, x, y] $ \a ->
            open $ runNames [] $ lam "i" (const (pure $ unArg a))
          IsNot (bA, x, y) -> for [bA, x, y] $ \a ->
            open (Lam defaultArgInfo $ NoAbs "_" $ unArg a)

        -- The resulting path is constant when when
        --    @Σ φ λ o → -- primIdFace p i1 o@
        -- holds. That's why cofibrations have to be closed under Σ,
        -- c.f. primDepIMin.
        cof <- pure tIMin
          <@> phi
          <@> ilam "o" (\o ->
            pure idFace <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io) <@> (p io o))

        -- Do the Kan operation for our faces in the Path type.
        path <- eval kanOp l
          (lam "i" $ \i -> pure tPathType <#> (l <@> i) <#> (bA <@> i) <@> (x <@> i) <@> (y <@> i))
          phi
          (lam "i" $ \i -> ilam "o" $ \o ->
            pure idPath <#> (l <@> i) <#> (bA <@> i) <#> (x <@> i) <#> (y <@> i) <@> (p i o))
          (pure idPath <#> (l <@> iz) <#> (bA <@> iz) <#> (x <@> iz) <#> (y <@> iz) <@> p0)

        conId <#> (l <@> io) <#> (bA <@> io) <#> (x <@> io) <#> (y <@> io)
          <@> pure cof
          <@> pure path
    _ -> return $ Nothing
