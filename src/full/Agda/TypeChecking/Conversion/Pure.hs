{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Conversion.Pure where

import Control.Monad.Except
import System.IO.Unsafe (unsafeDupablePerformIO)
import Data.IORef

import Agda.Syntax.Internal

import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.Utils.Impossible

pureConversion ::
       TCM b               -- ^ What to do on `neverUnblock`
    -> (Blocker -> TCM b)  -- ^ What to do on other blockers.
    -> (a -> TCM b)        -- ^ What to do with successful result.
    -> TCM a
    -> TCM b
pureConversion rigidblock flexblock nonblocked = \m ->
  localTC (\e -> e {envCompareBlocked = True, envPureConversion = True}) $
  verboseBracket "tc.conv.pure" 40 "runPureConversion" $ do
    oldState <- getTC
    let debugResult msg =
           reportSDoc "tc.conv.pure" 40 $ "runPureConversion result: " <+> msg
    res <- (Right <$> m) `catchError` \case
      PatternErr block ->
        pure $ Left block

      -- András 2024-10-21: we treat this as a rigid blocker. Not sure why,
      -- but the old code did it like this.
      TypeError{} -> do
        debugResult "type error"
        pure $ Left neverUnblock

      GenericException{} -> __IMPOSSIBLE__
      IOException{}      -> __IMPOSSIBLE__
      ParserError{}      -> __IMPOSSIBLE__
    putTC oldState
    case res of
      Left block | block == neverUnblock -> do
        debugResult "stuck"
        rigidblock
      Left block -> do
        debugResult $ "blocked on" <+> prettyTCM block
        flexblock block
      Right a ->
        nonblocked a
{-# INLINE pureConversion #-}

-- | Run conversion without modifying constraint or meta state. A state
--   modification instead throws a pattern violation.
runPureConversion :: TCM a -> TCM a
runPureConversion =
  pureConversion (patternViolation neverUnblock) patternViolation pure

-- | Compare terms, catch and return pattern violation.
pureBlockOrEqualTerm :: Type -> Term -> Term -> TCM (Either Blocker Bool)
pureBlockOrEqualTerm a u v =
  pureConversion (pure $ Right False) (pure . Left) (\_ -> pure $ Right True) (equalTerm a u v)

-- | Don't catch pattern violation.
pureEqualTerm :: Type -> Term -> Term -> TCM Bool
pureEqualTerm a u v =
  pureConversion (pure False) patternViolation (\_ -> pure True) (equalTerm a u v)

pureBlockOrEqualTermInReduceM :: Type -> Term -> Term -> ReduceM (Either Blocker Bool)
pureBlockOrEqualTermInReduceM a u v = do
  st <- getTCState
  e  <- askTC
  pure $! unsafeDupablePerformIO $ do
    ref <- newIORef st
    unTCM (pureBlockOrEqualTerm a u v) ref e

pureBlockOrEqualType :: Type -> Type -> TCM (Either Blocker Bool)
pureBlockOrEqualType a b =
  pureConversion (pure $ Right False) (pure . Left) (\_ -> pure $ Right True) (equalType a b)

pureCompareAs :: Comparison -> CompareAs -> Term -> Term -> TCM Bool
pureCompareAs cmp a u v =
  pureConversion (pure False) patternViolation (\_ -> pure True) (compareAs cmp a u v)
