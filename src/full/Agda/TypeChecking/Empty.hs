
module Agda.TypeChecking.Empty
  ( isEmptyType
  , isEmptyTel
  , ensureEmptyType
  , checkEmptyTel
  ) where

import Control.Monad        ( void )
import Control.Monad.Except ( MonadError(..) )

import Data.Semigroup
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.Match ( fromSplitPatterns )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce ( instantiateFull )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.List
import Agda.Utils.Monad

import Agda.Utils.Impossible

data ErrorNonEmpty
  = Fail               -- ^ Generic failure
  | FailBecause TCErr  -- ^ Failure with informative error
  | DontKnow Blocker   -- ^ Emptyness check blocked

instance Semigroup ErrorNonEmpty where
  DontKnow u1     <> DontKnow u2  = DontKnow $ unblockOnBoth u1 u2  -- Both must unblock for this to proceed
  e@DontKnow{}    <> _            = e
  _               <> e@DontKnow{} = e
  FailBecause err <> _            = FailBecause err
  Fail            <> err          = err

instance Monoid ErrorNonEmpty where
  mempty  = Fail
  mappend = (Data.Semigroup.<>)

-- | Ensure that a type is empty.
--   This check may be postponed as emptiness constraint.
ensureEmptyType
  :: Range -- ^ Range of the absurd pattern.
  -> Type  -- ^ Type that should be empty (empty data type or iterated product of such).
  -> TCM ()
ensureEmptyType r t = caseEitherM (checkEmptyType r t) failure return
  where
  failure (DontKnow u)      = addConstraint u $ IsEmpty r t
  failure (FailBecause err) = throwError err
  failure Fail              = typeError $ ShouldBeEmpty t []

-- | Check whether a type is empty.
isEmptyType :: Type -> TCM Bool
isEmptyType ty = isRight <$> checkEmptyType noRange ty

-- | Check whether some type in a telescope is empty.
isEmptyTel :: Telescope -> TCM Bool
isEmptyTel tel = isRight <$> checkEmptyTel noRange tel

-- Either the type is possibly non-empty (Left err) or it is really empty
-- (Right ()).
checkEmptyType :: Range -> Type -> TCM (Either ErrorNonEmpty ())
checkEmptyType range t = do
  mr <- tryRecordType t
  case mr of

    -- If t is blocked or a meta, we cannot decide emptiness now.  Postpone.
    Left (Blocked b t) -> return $ Left (DontKnow b)

    -- If t is not a record type, try to split
    Left (NotBlocked nb t) -> do
      -- from the current context xs:ts, create a pattern list
      -- xs _ : ts t and try to split on _ (the last variable)
      tel0 <- getContextTelescope
      let gamma = telToList tel0 ++ [domFromArg $ defaultArg (underscore, t)]
          tel   = telFromList gamma
          ps    = teleNamedArgs tel

      dontAssignMetas $ do
        r <- splitLast Inductive tel ps
        case r of
          Left UnificationStuck{} -> do
            blocker <- unblockOnAnyMetaIn <$> instantiateFull tel -- TODO Jesper: get proper blocking information from unification
            return $ Left $ DontKnow blocker
          Left _                  -> return $ Left Fail
          Right cov -> do
            let ps = map (namedArg . lastWithDefault __IMPOSSIBLE__ . fromSplitPatterns . scPats) $ splitClauses cov
            if (null ps) then return (Right ()) else
              Left . FailBecause <$> do typeError_ $ ShouldBeEmpty t ps

    -- If t is a record type, see if any of the field types is empty
    Right (r, pars, def) -> do
      if | NoEta{} <- recEtaEquality def -> return $ Left Fail
         | otherwise -> void <$> do checkEmptyTel range $ recTel def `apply` pars

-- | Check whether one of the types in the given telescope is constructor-less
--   and if yes, return its index in the telescope (0 = leftmost).
checkEmptyTel :: Range -> Telescope -> TCM (Either ErrorNonEmpty Int)
checkEmptyTel r = loop 0
  where
  loop i EmptyTel            = return $ Left Fail
  loop i (ExtendTel dom tel) = orEitherM
    [ (i <$) <$> checkEmptyType r (unDom dom)
    , underAbstraction dom tel $ loop (succ i)
    ]
