
module Agda.TypeChecking.Empty (isEmptyType) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except

import Data.Semigroup
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Either
import Agda.Utils.Monad

data ErrorNonEmpty
  = Fail              -- ^ Generic failure
  | FailBecause TCErr -- ^ Failure with informative error
  | DontKnow          -- ^ Emptyness check blocked

instance Semigroup ErrorNonEmpty where
  DontKnow        <> _        = DontKnow
  _               <> DontKnow = DontKnow
  FailBecause err <> _        = FailBecause err
  Fail            <> err      = err

instance Monoid ErrorNonEmpty where
  mempty  = Fail
  mappend = (Data.Semigroup.<>)

-- | Check whether a type is empty.
--   This check may be postponed as emptiness constraint.
isEmptyType :: Range -> Type -> TCM ()
isEmptyType r t = caseEitherM (loop t) failure return
  where
  failure DontKnow          = addConstraint $ IsEmpty r t
  failure (FailBecause err) = throwError err
  failure Fail              = typeError $ ShouldBeEmpty t []

  -- Either the type is possibly non-empty (Left err) or it is really empty
  -- (Right ()).
  loop :: Type -> TCM (Either ErrorNonEmpty ())
  loop t = do
    mr <- tryRecordType t
    case mr of

      -- If t is blocked or a meta, we cannot decide emptiness now.  Postpone.
      Left Nothing -> return $ Left DontKnow

      -- If t is not a record type, try to split
      Left (Just t) -> do
        -- from the current context xs:ts, create a pattern list
        -- xs _ : ts t and try to split on _ (the last variable)
        tel0 <- getContextTelescope
        let gamma = telToList tel0 ++ [domFromArg $ defaultArg (underscore, t)]
            tel   = telFromList gamma
            ps    = teleNamedArgs tel

        dontAssignMetas $ do
          r <- splitLast Inductive tel ps
          case r of
            Left UnificationStuck{} -> return $ Left DontKnow
            Left _                  -> return $ Left Fail
            Right cov -> do
              let ps = map (namedArg . last . scPats) $ splitClauses cov
              if (null ps) then return (Right ()) else
                Left . FailBecause <$> do typeError_ $ ShouldBeEmpty t ps

      -- If t is a record type, see if any of the field types is empty
      Right (r, pars, def) -> do
        if not $ recEtaEquality def then return $ Left Fail else do
          checkTel $ recTel def `apply` pars

  checkTel :: Telescope -> TCM (Either ErrorNonEmpty ())
  checkTel EmptyTel          = return $ Left Fail
  checkTel (ExtendTel dom tel) = orEitherM
    [ loop (unDom dom)
    , underAbstraction dom tel checkTel
    ]
