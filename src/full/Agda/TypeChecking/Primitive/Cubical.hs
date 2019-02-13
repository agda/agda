{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Primitive.Cubical where
import Prelude hiding (null, (!!))

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans ( lift )

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin


import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.Utils.Except

#include "undefined.h"
import Agda.Utils.Impossible


-- | Tries to @primTransp@ a whole telescope of arguments, following the rule for Σ types.
--   If a type in the telescope does not support transp, @transpTel@ throws it as an exception.
transpTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term          -- Γ ⊢ φ : F  -- i.Δ const on φ
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[1]
transpTel delta phi args = do
  tTransp <- liftTCM primTrans
  imin <- liftTCM primIMin
  imax <- liftTCM primIMax
  ineg <- liftTCM primINeg
  let
    noTranspError t = lift . throwError =<< liftTCM (buildClosure t)
    bapp :: (Applicative m, Subst t a) => m (Abs a) -> m t -> m a
    bapp t u = lazyAbsApp <$> t <*> u
    gTransp (Just l) t phi a = pure tTransp <#> l <@> (Lam defaultArgInfo . fmap unEl <$> t) <@> phi <@> a
    gTransp Nothing  t phi a = do
      -- Γ ⊢ i.Ξ
      xi <- (open =<<) $ do
        bind "i" $ \ i -> do
          TelV xi _ <- (liftTCM . telView =<<) $ t `bapp` i
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
          lift $ piApplyM ti =<< trFillTel xin phi xi_args ni
        axi <- do
          a <- a
          xif <- bind "i" $ \ i -> xi `bapp` (pure ineg <@> i)
          phi <- phi
          xi_args <- xi_args
          lift $ apply a <$> transpTel xif phi xi_args
        s <- reduce $ getSort (absBody b')
        case s of
          Type l -> do
            l <- open $ lam_i (Level l)
            b' <- open b'
            axi <- open axi
            gTransp (Just l) b' phi axi
          Inf    ->
            case 0 `freeIn` (raise 1 b' `lazyAbsApp` var 0) of
              False -> return axi
              True -> noTranspError b'
          _ -> noTranspError b'
    lam_i = Lam defaultArgInfo . Abs "i"
    go :: Telescope -> Term -> Args -> ExceptT (Closure (Abs Type)) TCM Args
    go EmptyTel            _   []       = return []
    go (ExtendTel t delta) phi (a:args) = do
      -- Γ,i ⊢ t
      -- Γ,i ⊢ (x : t). delta
      -- Γ ⊢ a : t[0]
      s <- reduce $ getSort t
      -- Γ ⊢ b : t[1], Γ,i ⊢ b : t[i]
      (b,bf) <- runNamesT [] $ do
        l <- case s of
               Inf -> return Nothing
               Type l -> Just <$> open (lam_i (Level l))
               _ -> noTranspError (Abs "i" (unDom t))
        t <- open $ Abs "i" (unDom t)
        [phi,a] <- mapM open [phi, unArg a]
        b <- gTransp l t phi a
        bf <- bind "i" $ \ i -> do
                            gTransp ((<$> l) $ \ l -> lam "j" $ \ j -> l <@> (pure imin <@> i <@> j))
                                    (bind "j" $ \ j -> t `bapp` (pure imin <@> i <@> j))
                                    (pure imax <@> (pure ineg <@> i) <@> phi)
                                    a
        return (b, absBody bf)
      (:) (b <$ a) <$> go (lazyAbsApp delta bf) phi args
    go (ExtendTel t delta) phi []    = __IMPOSSIBLE__
    go EmptyTel            _   (_:_) = __IMPOSSIBLE__
  go (absBody delta) phi args

-- | Like @transpTel@ but performing a transpFill.
trFillTel :: Abs Telescope -- Γ ⊢ i.Δ
          -> Term
          -> Args          -- Γ ⊢ δ : Δ[0]
          -> Term          -- Γ ⊢ r : I
          -> ExceptT (Closure (Abs Type)) TCM Args      -- Γ ⊢ Δ[r]
trFillTel delta phi args r = do
  imin <- liftTCM primIMin
  imax <- liftTCM primIMax
  ineg <- liftTCM primINeg
  transpTel (Abs "j" $ raise 1 delta `lazyAbsApp` (imin `apply` (map argN [var 0, raise 1 r])))
            (imax `apply` [argN $ ineg `apply` [argN r], argN phi])
            args

