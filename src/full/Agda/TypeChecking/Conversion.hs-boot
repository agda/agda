
module Agda.TypeChecking.Conversion where

import Control.Applicative (Const)
import Control.Monad.Except ( MonadError )
import qualified Control.Monad.Fail as Fail

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
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
compareAs_   :: MonadConversion m => Comparison -> CompareAsHet -> Het 'LHS Term -> Het 'RHS Term -> m ()
compareAsDir :: MonadConversion m => CompareDirection -> CompareAs -> Term -> Term -> m ()
compareTypeDir_ :: (MonadConversion m, AreSides s₁ s₂)
                => CompareDirection -> Het s₁ Type -> Het s₂ Type -> m ()
compareTermOnFace :: MonadConversion m => Comparison -> Term -> Type -> Term -> Term -> m ()
compareAtom  :: MonadConversion m => Comparison -> CompareAs -> Term -> Term -> m ()
compareArgs  :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> Args -> Args -> m ()
compareElims :: MonadConversion m => [Polarity] -> [IsForced] -> Type -> Term -> [Elim] -> [Elim] -> m ()
compareElims_ :: MonadConversion m => [Polarity] -> [IsForced] -> TwinT' Type -> TwinT' Term -> H'LHS [Elim] -> H'RHS [Elim] -> m ()
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

data TypeView_ =
    TPi (Dom TwinT) (Abs TwinT)
  | TDefRecordEta QName Defn (TwinT' Args)
  | TLam
  | TLevel
  | TOther

type MkTwinM m = (MonadTCEnv m, ReadTCState m)
type TypeViewM m = (HasBuiltins m, HasConstInfo m, MkTwinM m)

typeView :: forall m. TypeViewM m => TwinT' Term -> m (TypeView_)
mkTwinTele :: MkTwinM m => TwinT' Telescope -> m Telescope_

valueCmpDir_ :: (MonadConversion m, AreSides s₁ s₂) =>
                  (Constraint -> m a) ->
                    CompareDirection -> CompareAsHet -> Het s₁ Term -> Het s₂ Term ->
                      m a

compareAsDir_ :: (MonadConversion m, AreSides s₁ s₂)
                  => CompareDirection -> CompareAsHet -> Het s₁ Term -> Het s₂ Term -> m ()
