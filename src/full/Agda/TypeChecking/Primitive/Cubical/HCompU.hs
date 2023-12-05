{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Primitive.Cubical.HCompU
  ( doHCompUKanOp
  , prim_glueU'
  , prim_unglueU'
  )
  where

import Control.Monad

import Agda.Syntax.Common
  ( Cubical(..), Arg(..)
  , ProjOrigin(..)
  )
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Pure

import Agda.TypeChecking.Names
  ( runNamesT, runNames, cl, lam, open, ilam )
import Agda.TypeChecking.Primitive.Base
  ( (-->), nPi', pPi', hPi', el, el', el's, (<@>), (<@@>), (<#>), argN, (<..>)
  , SigmaKit(..), getSigmaKit
  )
import Agda.TypeChecking.Primitive.Cubical.Glue
import Agda.TypeChecking.Primitive.Cubical.Base
import Agda.TypeChecking.Reduce
  ( reduceB', reduceB )
import Agda.TypeChecking.Substitute
  ( absBody, apply, sort, applyE )

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad

import Agda.Utils.Impossible (__IMPOSSIBLE__)

-- | Perform the Kan operations for an @hcomp {A = Type} {φ} u u0@ type.
doHCompUKanOp
  :: forall m. PureTCM m
  => KanOperation
  -> FamilyOrNot (Arg Term, Arg Term, Arg Term, Arg Term)
  -> TermPosition
  -> m (Maybe Term)

-- TODO (Amy, 2022-08-17): This is literally the same algorithm as
-- doGlueKanOp, but specialised for using transport as the equivalence.
-- Can we deduplicate them?
doHCompUKanOp (HCompOp psi u u0) (IsNot (la, phi, bT, bA)) tpos = do
  let getTermLocal :: IsBuiltin a => a -> m Term
      getTermLocal = getTerm $ getBuiltinId builtinHComp ++ " for " ++ getBuiltinId builtinHComp ++ " of Set"
  io       <- getTermLocal builtinIOne
  iz       <- getTermLocal builtinIZero
  tHComp   <- getTermLocal builtinHComp
  tTransp  <- getTermLocal builtinTrans
  tunglue  <- getTermLocal builtin_unglueU
  tLSuc    <- getTermLocal builtinLevelSuc
  tSubIn   <- getTermLocal builtinSubIn
  tItIsOne <- getTermLocal builtinItIsOne
  runNamesT [] $ do
    [psi, u, u0] <- mapM (open . unArg) [ignoreBlocking psi, u, u0]
    [la, phi, bT, bA] <- mapM (open . unArg) [la, phi, bT, bA]

    ifM (headStop tpos phi) (return Nothing) $ Just <$> do

    let
      transp la bA a0 = pure tTransp <#> lam "i" (const la) <@> lam "i" bA <@> pure iz <@> a0
      tf i o = hfill la (bT <@> pure io <..> o) psi u u0 i

      bAS = pure tSubIn <#> (pure tLSuc <@> la) <#> (Sort . tmSort <$> la) <#> phi <@> bA
      unglue g = pure tunglue <#> la <#> phi <#> bT <#> bAS <@> g

      a1 = pure tHComp <#> la <#> bA <#> (imax psi phi)
        <@> lam "i" (\i -> combineSys la bA
            [ (psi, ilam "o" (\o -> unglue (u <@> i <..> o)))
            , (phi, ilam "o" (\ o -> transp la (\i -> bT <@> (ineg i) <..> o) (tf i o)))
            ])
        <@> unglue u0

      t1 = tf (pure io)

    -- pure tglue <#> la <#> phi <#> bT <#> bAS <@> (ilam "o" $ \ o -> t1 o) <@> a1
    case tpos of
      Eliminated -> a1
      Head       -> t1 (pure tItIsOne)


doHCompUKanOp (TranspOp psi u0) (IsFam (la, phi, bT, bA)) tpos = do
  let
    localUse = getBuiltinId builtinTrans ++ " for " ++ getBuiltinId builtinHComp ++ " of Set"
    getTermLocal :: IsBuiltin a => a -> m Term
    getTermLocal = getTerm localUse
  tPOr <- getTermLocal builtinPOr
  tIMax <- getTermLocal builtinIMax
  tIMin <- getTermLocal builtinIMin
  tINeg <- getTermLocal builtinINeg
  tHComp <- getTermLocal builtinHComp
  tTrans <- getTermLocal builtinTrans
  tTranspProof <- getTermLocal builtinTranspProof
  tSubIn <- getTermLocal builtinSubIn
  tForall  <- getTermLocal builtinFaceForall
  io      <- getTermLocal builtinIOne
  iz      <- getTermLocal builtinIZero
  tLSuc   <- getTermLocal builtinLevelSuc
  tPath   <- getTermLocal builtinPath
  tItIsOne   <- getTermLocal builtinItIsOne
  kit <- fromMaybe __IMPOSSIBLE__ <$> getSigmaKit
  runNamesT [] $ do
    -- Helper definitions we'll use:
    gcomp <- mkGComp localUse

    let
      transp la bA a0 = pure tTrans <#> lam "i" (const la) <@> lam "i" bA <@> pure iz <@> a0
      transpFill la bA phi u0 i = pure tTrans
        <#> ilam "j" (\ j -> la <@> imin i j)
        <@> ilam "j" (\ j -> bA <@> imin i j)
        <@> (imax phi (ineg i))
        <@> u0

    [psi, u0] <- mapM (open . unArg) [ignoreBlocking psi, u0]

    [la, phi, bT, bA] <- mapM (\a -> open . runNames [] $ lam "i" (const (pure $ unArg a))) [la, phi, bT, bA]

    -- Andreas, 2022-03-25, issue #5838.
    -- Port the fix of @unglueTranspGlue@ and @doGlueKanOp DoTransp@
    -- also to @doHCompUKanOp DoTransp@, as suggested by Tom Jack and Anders Mörtberg.
    -- We define @unglue_u0 i@ that is first used with @i@ and then with @i0@.
    -- The original code used it only with @i0@.
    tunglue <- cl $ getTermLocal builtin_unglueU
    let
      bAS i = pure tSubIn
        <#> (pure tLSuc <@> (la <@> i)) <#> (Sort . tmSort <$> (la <@> i)) <#> (phi <@> i)
        <@> (bA <@> i)
      unglue_u0 i = pure tunglue
        <#> (la <@> i) <#> (phi <@> i) <#> (bT <@> i)
        <#> bAS i <@> u0

    ifM (headStop tpos (phi <@> pure io)) (return Nothing) $ Just <$> do

    let
      tf i o = transpFill la (lam "i" $ \ i -> bT <@> i <@> pure io <..> o) psi u0 i
      t1 o   = tf (pure io) o

      -- compute "forall. phi"
      forallphi = pure tForall <@> phi

      -- a1 with gcomp
      a1 = gcomp la bA (imax psi forallphi)
        (lam "i" $ \ i -> combineSys (la <@> i) (bA <@> i)
          [ (psi,       ilam "o" $ \_ -> unglue_u0 i)
          , (forallphi, ilam "o" (\o -> transp (la <@> i) (\j -> bT <@> i <@> ineg j <..> o) (tf i o)))
          ])
          (unglue_u0 (pure iz))

      w i o = lam "x" $ transp (la <@> i) (\j -> bT <@> i <@> ineg j <..> o)

      pt o = -- o : [ φ 1 ]
        combineSys (la <@> pure io) (bT <@> pure io <@> pure io <..> o)
          [ (psi       , ilam "o" $ \_ -> u0)
          , (forallphi , ilam "o" $ \o -> t1 o)
          ]

      -- "ghcomp" is implemented in the proof of tTranspProof
      -- (see src/data/lib/prim/Agda/Builtin/Cubical/HCompU.agda)
      t1'alpha o = -- o : [ φ 1 ]
         pure tTranspProof
          <#> (la <@> pure io) <@> lam "i" (\i -> bT <@> pure io <@> ineg i <..> o)
          <@> imax psi forallphi
          <@> pt o
          <@> (pure tSubIn <#> (la <@> pure io) <#> (bA <@> pure io) <#> imax psi forallphi
                <@> a1)

      -- TODO: optimize?
      t1' o   = t1'alpha o <&> (`applyE` [Proj ProjSystem (sigmaFst kit)])
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
      Eliminated -> a1'
      Head       -> t1' (pure tItIsOne)
doHCompUKanOp _ _ _ = __IMPOSSIBLE__

-- | The implementation of 'prim_glueU', the introduction form for
-- @hcomp@ types.
prim_glueU' :: TCM PrimitiveImpl
prim_glueU' = do
-- TODO (Amy, 2022-08-17): Same thing about duplicated code with Glue
-- applies here.
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (nPi' "i" primIntervalType $ \ _ -> pPi' "o" φ $ \ o -> sort . tmSort <$> la) $ \ t ->
       hPi' "A" (el's (cl primLevelSuc <@> la) $ cl primSub <#> (cl primLevelSuc <@> la) <@> (Sort . tmSort <$> la) <@> φ <@> (t <@> primIZero)) $ \ a -> do
       let bA = (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <#> (t <@> primIZero) <@> a)
       pPi' "o" φ (\ o -> el' la (t <@> cl primIOne <..> o))
         --> (el' la bA)
         --> el' la (cl primHComp <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <@> t <@> bA))
  view <- intervalView'
  one <- primItIsOne
  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 6 $ \ts ->
    case ts of
      [la,phi,bT,bA,t,a] -> do
       sphi <- reduceB' phi
       case view $ unArg $ ignoreBlocking $ sphi of
         IOne -> redReturn $ unArg t `apply` [argN one]
         _    -> return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA,t,a])
      _ -> __IMPOSSIBLE__

-- | The implementation of 'prim_unglueU', the elimination form for
-- @hcomp@ types.
prim_unglueU' :: TCM PrimitiveImpl
prim_unglueU' = do
-- TODO (Amy, 2022-08-17): Same thing about duplicated code with Glue
-- applies here.
  requireCubical CErased ""
  t <- runNamesT [] $
       hPi' "la" (el $ cl primLevel) (\ la ->
       hPi' "φ" primIntervalType $ \ φ ->
       hPi' "T" (nPi' "i" primIntervalType $ \ _ -> pPi' "o" φ $ \ o -> sort . tmSort <$> la) $ \ t ->
       hPi' "A" (el's (cl primLevelSuc <@> la) $ cl primSub <#> (cl primLevelSuc <@> la) <@> (Sort . tmSort <$> la) <@> φ <@> (t <@> primIZero)) $ \ a -> do
       let bA = (cl primSubOut <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <#> (t <@> primIZero) <@> a)
       el' la (cl primHComp <#> (cl primLevelSuc <@> la) <#> (Sort . tmSort <$> la) <#> φ <@> t <@> bA)
         --> el' la bA)

  view <- intervalView'
  one <- primItIsOne
  mglueU <- getPrimitiveName' builtin_glueU
  mtransp <- getPrimitiveName' builtinTrans
  mHCompU <- getPrimitiveName' builtinHComp
  let mhcomp = mHCompU

  return $ PrimImpl t $ primFun __IMPOSSIBLE__ 5 $ \case
    [la,phi,bT,bA,b] -> do
      sphi <- reduceB' phi
      case view $ unArg $ ignoreBlocking $ sphi of
        -- Case where the hcomp has reduced away: Transport backwards
        -- along the partial element we've glued.
        IOne -> do
          tTransp <- getTerm (getBuiltinId builtin_unglueU) builtinTrans
          iNeg    <- getTerm (getBuiltinId builtin_unglueU) builtinINeg
          iZ      <- getTerm (getBuiltinId builtin_unglueU) builtinIZero
          redReturn <=< runNamesT [] $ do
            [la,bT,b] <- mapM (open . unArg) [la,bT,b]
            pure tTransp <#> lam "i" (\ _ -> la) <@> lam "i" (\ i -> bT <@> ineg i <..> pure one)
              <@> pure iZ <@> b

        -- Otherwise, we're dealing with a proper glu- didn't I already
        -- make this joke? Oh, yeah, in prim_unglue, right.
        _ -> do
          sb <- reduceB' b
          let fallback sbA = return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA] ++ [reduced sb])
          case unArg $ ignoreBlocking $ sb of
            -- Project:
            Def q es | Just [_,_,_,_,_, a] <- allApplyElims es, Just q == mglueU -> redReturn $ unArg a

            -- Transport:
            Def q [Apply l, Apply bA, Apply r, Apply u0] | Just q == mtransp -> do
              sbA <- reduceB bA
              case unArg $ ignoreBlocking sbA of
                Lam _ t -> do
                  st <- reduceB' (absBody t)
                  case ignoreBlocking st of
                    Def h es | Just [la,_,phi,bT,bA] <- allApplyElims es, Just h == mHCompU -> do
                      redReturn . fromMaybe __IMPOSSIBLE__ =<<
                        doHCompUKanOp (TranspOp (notBlocked r) u0) (IsFam (la,phi,bT,bA)) Eliminated
                    _ -> fallback (st *> sbA)
                _  -> fallback sbA

            -- Compose:
            Def q [Apply l,Apply bA,Apply r,Apply u,Apply u0] | Just q == mhcomp -> do
              sbA <- reduceB bA
              case unArg $ ignoreBlocking sbA of
                Def h es | Just [la,_,phi,bT,bA] <- allApplyElims es, Just h == mHCompU -> do
                  redReturn . fromMaybe __IMPOSSIBLE__ =<<
                    doHCompUKanOp (HCompOp (notBlocked r) u u0) (IsNot (la,phi,bT,bA)) Eliminated
                _ -> fallback sbA
            _ -> return (NoReduction $ map notReduced [la] ++ [reduced sphi] ++ map notReduced [bT,bA] ++ [reduced sb])

    _ -> __IMPOSSIBLE__
