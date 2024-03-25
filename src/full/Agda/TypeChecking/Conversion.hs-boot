{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Conversion where

import Control.Monad.Except ( MonadError )
import qualified Control.Monad.Fail as Fail

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Polarity.Base
import Agda.TypeChecking.Warnings

type MonadConversion m =
  ( PureTCM m
  , MonadConstraint m
  , MonadMetaSolver m
  , MonadError TCErr m
  , MonadWarning m
  , MonadStatistics m
  , MonadFresh ProblemId m
  , MonadFresh Int m
  , Fail.MonadFail m
  )

compareTerm  :: MonadConversion m => Comparison -> Type -> Term -> Term -> m ()
compareAs    :: MonadConversion m => Comparison -> CompareAs -> Term -> Term -> m ()
compareTermOnFace :: MonadConversion m => Comparison -> Term -> Type -> Term -> Term -> m ()
compareAtom  :: MonadConversion m => Comparison -> CompareAs -> Term -> Term -> m ()
compareArgs  :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> Args -> Args -> m ()
compareElims :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> [Elim] -> [Elim] -> m ()
compareType  :: MonadConversion m => Comparison -> Type -> Type -> m ()
compareSort  :: MonadConversion m => Comparison -> Sort -> Sort -> m ()
compareLevel :: MonadConversion m => Comparison -> Level -> Level -> m ()
equalTerm    :: MonadConversion m => Type -> Term -> Term -> m ()
equalTermOnFace :: MonadConversion m => Term -> Type -> Term -> Term -> m ()
equalType    :: MonadConversion m => Type -> Type -> m ()
equalSort    :: MonadConversion m => Sort -> Sort -> m ()
equalLevel   :: MonadConversion m => Level -> Level -> m ()
leqType      :: MonadConversion m => Type -> Type -> m ()
leqLevel     :: MonadConversion m => Level -> Level -> m ()
leqSort      :: MonadConversion m => Sort -> Sort -> m ()
