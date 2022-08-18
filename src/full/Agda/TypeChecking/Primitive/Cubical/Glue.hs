{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Primitive.Cubical.Glue
  ( mkGComp
  , doGlueKanOp

  , primGlue'
  , prim_glue'
  , prim_unglue'
  )
  where

import Control.Monad.Except

import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Maybe

import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Substitute (absBody, apply, sort, subst, applyE)
import Agda.TypeChecking.Reduce (reduceB', reduce')
import Agda.TypeChecking.Names (NamesT, runNamesT, runNames, cl, lam, open, ilam)

import Agda.Interaction.Options.Base (optCubical)

import Agda.Syntax.Common
  ( Hiding(..), Cubical(..), Arg(..)
  , ConOrigin(..), ProjOrigin(..)
  , Relevance(..)
  , setRelevance
  , defaultArgInfo, hasQuantity0, defaultArg, setHiding
  )

import Agda.TypeChecking.Primitive.Base
  ( (-->), nPi', pPi', hPi', el, el', el's, (<@>), (<@@>), (<#>), argN, argH, (<..>)
  , SigmaKit(..), getSigmaKit
  )

import Agda.Syntax.Internal
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.TypeChecking.Monad.Debug (__IMPOSSIBLE_VERBOSE__)

import Agda.TypeChecking.Primitive.Cubical.Base

-- | Define a "ghcomp" version of gcomp. Normal comp looks like:
--
-- comp^i A [ phi -> u ] u0 = hcomp^i A(1/i) [ phi -> forward A i u ] (forward A 0 u0)
--
-- So for "gcomp" we compute:
--
-- gcomp^i A [ phi -> u ] u0 = hcomp^i A(1/i) [ phi -> forward A i u, ~ phi -> forward A 0 u0 ] (forward A 0 u0)
--
-- The point of this is that gcomp does not produce any empty
-- systems (if phi = 0 it will reduce to "forward A 0 u".
mkGComp :: HasBuiltins m => String -> NamesT m (NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term -> NamesT m Term)
mkGComp s = do
  let getTermLocal = getTerm s
  tPOr <- getTermLocal "primPOr"
  tIMax <- getTermLocal builtinIMax
  tIMin <- getTermLocal builtinIMin
  tINeg <- getTermLocal builtinINeg
  tHComp <- getTermLocal builtinHComp
  tTrans <- getTermLocal builtinTrans
  io      <- getTermLocal builtinIOne
  iz      <- getTermLocal builtinIZero
  let forward la bA r u = pure tTrans <#> lam "i" (\ i -> la <@> (i `imax` r))
                                      <@> lam "i" (\ i -> bA <@> (i `imax` r))
                                      <@> r
                                      <@> u
  return $ \ la bA phi u u0 ->
    pure tHComp <#> (la <@> pure io)
                <#> (bA <@> pure io)
                <#> imax phi (ineg phi)
                <@> lam "i" (\ i -> combineSys (la <@> i) (bA <@> i)
                                      [ (phi,      ilam "o" $ \o -> forward la bA i (u <@> i <..> o))
                                      , (ineg phi, ilam "o" $ \o -> forward la bA (pure iz) u0)
                                      ])
                <@> forward la bA (pure iz) u0

-- | Perform the Kan operations for a @Glue φ A (T , e)@ type.
doGlueKanOp
  :: PureTCM m
  => KanOperation -- ^ Are we composing or transporting?
  -> FamilyOrNot (Arg Term, Arg Term, Arg Term, Arg Term, Arg Term, Arg Term)
  -- ^ The data of the Glue operation: The levels of @A@ and @T@, @A@
  -- itself, the extent of @T@, @T@ itself, and the family of
  -- equivalences.
  -> TermPosition
  -- ^ Are we computing a plain hcomp/transp or are we computing under
  -- @unglue@?
  -> m (Maybe Term)

doGlueKanOp (HCompOp psi u u0) (IsNot (la, lb, bA, phi, bT, e)) tpos = do
-- hcomp {psi} u u0 : Glue {la} {lb} bA {φ} (bT, e)
-- ... |- la, lb : Level
-- ... |- bA : Type la
-- ... |- bT : Partial φ (Type lB)
-- ... |- e : PartialP φ λ o → bT o ≃ bA
  let getTermLocal = getTerm $ builtinHComp ++ " for " ++ builtinGlue
  tHComp   <- getTermLocal builtinHComp
  tEFun    <- getTermLocal builtinEquivFun
  tglue    <- getTermLocal builtin_glue
  tunglue  <- getTermLocal builtin_unglue
  io       <- getTermLocal builtinIOne
  tItIsOne <- getTermLocal builtinItIsOne
  view     <- intervalView'

  runNamesT [] $ do
    [psi, u, u0] <- mapM (open . unArg) [ignoreBlocking psi, u, u0]
    [la, lb, bA, phi, bT, e] <- mapM (open . unArg) [la, lb, bA, phi, bT, e]

    ifM (headStop tpos phi) (return Nothing) $ Just <$> do
    let
      tf i o   = hfill lb (bT <..> o) psi u u0 i
      unglue g = pure tunglue <#> la <#> lb <#> bA <#> phi <#> bT <#> e <@> g

      a1 = pure tHComp <#> la <#> bA <#> (imax psi phi)
        <@> lam "i" (\i -> combineSys la bA
            [ (psi, ilam "o" (\o -> unglue (u <@> i <..> o)))
            , (phi, ilam "o" (\o -> pure tEFun <#> lb <#> la <#> (bT <..> o) <#> bA <@> (e <..> o) <@> tf i o))
            ])
        <@> unglue u0

      t1 = tf (pure io)

    case tpos of
      Head       -> t1 (pure tItIsOne)
      Eliminated -> a1

-- ...    |- psi, u0
-- ..., i |- la, lb, bA, phi, bT, e
doGlueKanOp (TranspOp psi u0) (IsFam (la, lb, bA, phi, bT, e)) tpos = do
-- transp (λ i → Glue {la} {lb} bA {φ} (bT , e)) ψ u0
  let
    localUse = builtinTrans ++ " for " ++ builtinGlue
    getTermLocal = getTerm localUse
  tHComp <- getTermLocal builtinHComp
  tTrans <- getTermLocal builtinTrans
  tForall <- getTermLocal builtinFaceForall
  tEFun   <- getTermLocal builtinEquivFun
  tEProof <- getTermLocal builtinEquivProof
  toutS   <- getTermLocal builtinSubOut
  tglue   <- getTermLocal builtin_glue
  tunglue <- getTermLocal builtin_unglue
  io      <- getTermLocal builtinIOne
  iz      <- getTermLocal builtinIZero
  tLMax   <- getTermLocal builtinLevelMax
  tTransp <- getTermLocal builtinTranspProof
  tItIsOne <- getTermLocal builtinItIsOne
  kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
  runNamesT [] $ do

    gcomp <- mkGComp localUse

    -- transpFill: transp (λ j → bA (i ∧ j)) (φ ∨ ~ i) u0
    -- connects u0 and transp bA i0 u0
    let transpFill la bA phi u0 i =
          pure tTrans <#> lam "j" (\ j -> la <@> imin i j)
                      <@> lam "j" (\ j -> bA <@> imin i j)
                      <@> (imax phi (ineg i))
                      <@> u0
    [psi,u0] <- mapM (open . unArg) [ignoreBlocking psi,u0]

    -- glue1 t a = glue la[i1/i] lb[i1/i] bA[i1/i] phi[i1/i] bT[i1/i] e[i1/i] t a
    glue1 <- do
      g <- open $ (tglue `apply`) . map ((setHiding Hidden) . (subst 0 io)) $ [la, lb, bA, phi, bT, e]
      return $ \ t a -> g <@> t <@> a

    [la, lb, bA, phi, bT, e] <- mapM (\ a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [la, lb, bA, phi, bT, e]

    -- Andreas, 2022-03-24, fixing #5838
    -- Following the updated note
    --
    --   Simon Huber, A Cubical Type Theory for Higher Inductive Types
    --   https://simhu.github.io/misc/hcomp.pdf (February 2022)
    --
    -- See: https://github.com/agda/agda/issues/5755#issuecomment-1043797776

    -- unglue_u0 i = unglue la[i/i] lb[i/i] bA[i/i] phi[i/i] bT[i/i] e[i/e] u0
    let unglue_u0 i = foldl (<#>) (pure tunglue) (map (<@> i) [la, lb, bA, phi, bT, e]) <@> u0

    view <- intervalView'

    ifM (headStop tpos (phi <@> pure io)) (return Nothing) $ Just <$> do
    let
      tf i o = transpFill lb (lam "i" $ \ i -> bT <@> i <..> o) psi u0 i
      t1 o = tf (pure io) o

      -- compute "forall. phi"
      forallphi = pure tForall <@> phi

      -- a1 with gcomp
      -- a1 = gcomp (ψ ∨ (∀ i. φ)) (λ { i (φ = i1) → unglue_u0 i ; i ((∀ i. φ) = i1) → equivFun ... })
      --        (unglue_u0 i0)
      a1 = gcomp la bA (imax psi forallphi)
        (lam "i" $ \ i -> combineSys (la <@> i) (bA <@> i)
          [ (phi,       ilam "o" $ \_ -> unglue_u0 i)
          , (forallphi, ilam "o" $ \o -> w i o <@> (tf i o))
          ])
        (unglue_u0 (pure iz))

      max l l' = pure tLMax <@> l <@> l'
      sigCon x y = pure (Con (sigmaCon kit) ConOSystem []) <@> x <@> y

      -- The underlying function of our partial equivalence at the given
      -- endpoint of the interval, together with proof (o : IsOne φ).
      w i o = pure tEFun <#> (lb <@> i)
                         <#> (la <@> i)
                         <#> (bT <@> i <..> o)
                         <#> (bA <@> i)
                         <@> (e <@> i <..> o)

      -- Type of fibres of the partial equivalence over a1.
      fiberT o = fiber (lb <@> pure io) (la <@> pure io)
        (bT <@> (pure io) <..> o) (bA <@> pure io)
        (w (pure io) o)
        a1

      -- We don't have to do anything special for "~ forall. phi"
      -- here (to implement "ghcomp") as it is taken care off by
      -- tEProof in t1'alpha below
      pe o = -- o : IsOne φ
        combineSys (max (la <@> pure io) (lb <@> pure io)) (fiberT o)
          [ (psi       , ilam "o" $ \_ -> sigCon u0     (lam "_" $ \_ -> a1))
          , (forallphi , ilam "o" $ \o -> sigCon (t1 o) (lam "_" $ \_ -> a1))
          ]
      -- pe is a partial fibre of the equivalence with extent (ψ ∨ ∀ i. φ)
      -- over a1

      -- "ghcomp" is implemented in the proof of tEProof
      -- (see src/data/lib/prim/Agda/Builtin/Cubical/Glue.agda)
      t1'alpha o = -- o : IsOne φ
         -- Because @e i1 1=1@ is an equivalence, we can extend the
         -- partial fibre @pe@ to an actual fibre of (e i1 1=1) over a1.
         pure toutS <#> (max (la <@> pure io) (lb <@> pure io)) <#> fiberT o
          <#> imax psi forallphi
          <#> pe o
          <@> (pure tEProof
                <#> (lb <@> pure io)        <#> (la <@> pure io)
                <@> (bT <@> pure io <..> o) <@> (bA <@> pure io)
                <@> (e <@> pure io <..> o)  <@> a1
                <@> (imax psi forallphi)
                <@> pe o)

      -- TODO: optimize?
      t1' o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaFst kit)])
      alpha o = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaSnd kit)])
      a1' = pure tHComp <#> (la <@> pure io) <#> (bA <@> pure io)
        <#> imax (phi <@> pure io) psi
        <@> lam "j" (\j -> combineSys (la <@> pure io) (bA <@> pure io)
          [ (phi <@> pure io, ilam "o" $ \o -> alpha o <@@> (w (pure io) o <@> t1' o, a1, j))
          , (psi,             ilam "o" $ \o -> a1)
          ])
        <@> a1

    -- glue1 (ilam "o" t1') a1'
    case tpos of
      Head -> t1' (pure tItIsOne)
      Eliminated -> a1'
doGlueKanOp _ _ _ = __IMPOSSIBLE__

-- The implementation of 'primGlue'. Handles reduction where the partial
-- element is defined.
primGlue' :: TCM PrimitiveImpl
primGlue' = do
  requireCubical CFull ""
  -- primGlue
  --   : {la lb : Level} (A : Type la) {φ : I}
  --   → (T : Partial φ (Type lb)
  --   → (e : PartialP φ λ o → A ≃ T o)
  --   → Type lb
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       nPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" primIntervalType $ \ φ ->
       nPi' "T" (pPi' "o" φ $ \ o -> el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       pPi' "o" φ (\ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a)
       --> (sort . tmSort <$> lb))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ts ->
    case ts of
     [la,lb,a,phi,t,e] -> do
       sphi <- reduceB' phi
       -- If @φ = i1@ then we reduce to @T 1=1@, since @Glue@ is also a Kan operation.
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         -- Otherwise we're a regular ol' type.
         _    -> return (NoReduction $ map notReduced [la,lb,a] ++ [reduced sphi] ++ map notReduced [t,e])
     _ -> __IMPOSSIBLE__

-- | The implementation of 'prim_glue', the introduction form for @Glue@
-- types.
prim_glue' :: TCM PrimitiveImpl
prim_glue' = do
  requireCubical CFull ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
       pPi' "o" φ (\ o -> el' lb (t <@> o)) --> (el' la a --> el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)))

  -- Takes a partial element of @t : T@ and an element of the base type @A@
  -- which extends @e t@, and makes it into a Glue.
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 8 $ \case
    [la, lb, bA, phi, bT, e, t, a] -> do
      sphi <- reduceB' phi
      -- When @φ = 1@ then @t : T@ is totally defined.
      case view $ unArg $ ignoreBlocking $ sphi of
        IOne -> redReturn $ unArg t `apply` [argN one]
        -- Otherwise we'll just wait to get unglued.
        _    -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e,t,a])
    _ -> __IMPOSSIBLE__

-- | The implementation of 'prim_unglue', the elimination form for
-- @Glue@ types.
prim_unglue' :: TCM PrimitiveImpl
prim_unglue' = do
  requireCubical CFull ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "lb" (el $ cl primLevel) $ \ lb ->
       hPi' "A" (sort . tmSort <$> la) $ \ a ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (pPi' "o" φ $ \ o ->  el' (cl primLevelSuc <@> lb) (Sort . tmSort <$> lb)) $ \ t ->
       hPi' "e" (pPi' "o" φ $ \ o -> el' (cl primLevelMax <@> la <@> lb) $ cl primEquiv <#> lb <#> la <@> (t <@> o) <@> a) $ \ e ->
       (el' lb (cl primGlue <#> la <#> lb <@> a <#> φ <@> t <@> e)) --> el' la a)

  -- Takes an element @b : Glue φ A (T, e)@ to an element of @A@ which,
  -- under @φ@, agrees with @e b@. Recall that @φ ⊢ e : A → T@ and @φ ⊢
  -- Glue φ A (T, e) = T@ so this is well-typed.
  view <- intervalView'
  one <- primItIsOne
  mGlue <- getPrimitiveName' builtinGlue
  mglue <- getPrimitiveName' builtin_glue
  mtransp <- getPrimitiveName' builtinTrans
  mhcomp <- getPrimitiveName' builtinHComp
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 7 $ \case
    [la, lb, bA, phi, bT, e, b] -> do
      sphi <- reduceB' phi
      case view $ unArg $ ignoreBlocking $ sphi of
        -- When @φ = i1@ we have @Glue i1 A (T , e) = T@ so @b : T@,
        -- and we must produce @unglue b : A [ i1 → e b ]@. But that's
        -- just @e b@!
        IOne -> do
          let argOne = setRelevance Irrelevant $ argN one
          tEFun <- getTerm builtin_unglue builtinEquivFun
          redReturn $ tEFun `apply` [lb,la,argH $ unArg bT `apply` [argOne],bA, argN $ unArg e `apply` [argOne],b]

        -- Otherwise we're dealing with a proper glued thing.
        -- Definitely a sticky situation!
        _    -> do
          sb <- reduceB' b
          let fallback sbA = return (NoReduction $ map notReduced [la,lb] ++ map reduced [sbA, sphi] ++ map notReduced [bT,e] ++ [reduced sb])
          case unArg $ ignoreBlocking $ sb of
            -- Case 1: unglue (glue a) = a. This agrees with the @φ =
            -- i1@ reduction because under @φ@, the argument to
            -- @glue@ must be in the image of the equivalence.
            Def q es
              | Just [_, _, _, _, _, _, _, a] <- allApplyElims es
              , Just q == mglue -> redReturn $ unArg a

            -- Case 2: unglue (transp (λ i → Glue ...) r u0).
            -- Defer to the implementation of @doGlueKanOp DoTransp ... Eliminated@: It knows how to unglue itself.
            Def q [Apply l, Apply bA, Apply r, Apply u0] | Just q == mtransp -> do
              sbA <- reduceB' bA
              -- Require that bA be a lambda abstraction...
              case unArg $ ignoreBlocking sbA of
                Lam _ t -> do
                  -- And that its body reduces to a Glue type.
                  st <- reduceB' (absBody t)
                  case ignoreBlocking st of
                    -- In this case, we use the Glue data extracted from
                    -- the family we're transporting over.
                    Def g es | Just [la', lb', bA', phi', bT', e'] <- allApplyElims es, Just g == mGlue -> do
                        redReturn . fromMaybe __IMPOSSIBLE__ =<<
                          doGlueKanOp (TranspOp (notBlocked r) u0) (IsFam (la',lb',bA',phi',bT',e')) Eliminated
                    _ -> fallback (st *> sbA)
                _ -> fallback sbA

            -- Case 3: unglue (hcomp u u0).
            -- Defer to the implementation of @doGlueKanOp DoHComp ... Eliminated@: It knows how to unglue itself.
            Def q [Apply l,Apply bA,Apply r,Apply u,Apply u0] | Just q == mhcomp -> do
              sbA <- reduceB' bA
              case unArg $ ignoreBlocking sbA of
                -- Idem: use the Glue data from the type we're doing
                -- hcomp in.
                Def g es | Just [la', lb', bA', phi', bT', e'] <- allApplyElims es, Just g == mGlue -> do
                  redReturn . fromMaybe __IMPOSSIBLE__ =<<
                    doGlueKanOp (HCompOp (notBlocked r) u u0) (IsNot (la',lb',bA',phi',bT',e')) Eliminated
                _ -> fallback sbA

            _ -> return (NoReduction $ map notReduced [la,lb,bA] ++ [reduced sphi] ++ map notReduced [bT,e] ++ [reduced sb])
    _ -> __IMPOSSIBLE__
