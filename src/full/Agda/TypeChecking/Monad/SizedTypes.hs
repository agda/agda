
module Agda.TypeChecking.Monad.SizedTypes where

import Control.Applicative
import Control.Monad.Error

import Agda.Interaction.Options
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.Utils.Monad

-- | Check if a type is the 'primSize' type. The argument should be 'reduce'd.

isSizeType :: Type -> TCM Bool
isSizeType v = isSizeTypeTest <*> pure v

{- ORIGINAL CODE
isSizeType :: Type -> TCM Bool
isSizeType (El _ v) = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return False) $
  case v of
    Def x [] -> do
      Def size [] <- primSize
      return $ x == size
    _ -> return False
  `catchError` \_ -> return False

isSizeNameTest :: TCM (QName -> Bool)
isSizeNameTest = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return $ const False) $ do
    Def size [] <- primSize
    return (size ==)
  `catchError` \_ -> return $ const False
-}

isSizeNameTest :: TCM (QName -> Bool)
isSizeNameTest = ifM (optSizedTypes <$> pragmaOptions)
  isSizeNameTestRaw
  (return $ const False)

isSizeNameTestRaw :: TCM (QName -> Bool)
isSizeNameTestRaw = liftTCM $
  do
    Def size [] <- primSize
    return (size ==)
  `catchError` \_ -> return $ const False

isSizeTypeTest :: TCM (Type -> Bool)
isSizeTypeTest =
  ifM (not . optSizedTypes <$> pragmaOptions) (return $ const False) $ do
    testName <- isSizeNameTestRaw
    let testType (El _ (Def d [])) = testName d
        testType _                 = False
    return testType

sizeType :: TCM Type
sizeType = El (mkType 0) <$> primSize

sizeSuc :: TCM (Maybe QName)
sizeSuc = liftTCM $
  ifM (not . optSizedTypes <$> pragmaOptions) (return Nothing) $ do
    Def x [] <- primSizeSuc
    return $ Just x
  `catchError` \_ -> return Nothing

-- | A useful view on sizes.
data SizeView = SizeInf | SizeSuc Term | OtherSize Term

-- | Compute the size view of a term. The argument should be 'reduce'd.
--   Precondition: sized types are enabled.
sizeView :: Term -> TCM SizeView
sizeView v = do
  Def inf [] <- primSizeInf
  Def suc [] <- primSizeSuc
  case v of
    Def x []  | x == inf -> return SizeInf
    Def x [u] | x == suc -> return $ SizeSuc (unArg u)
    _                    -> return $ OtherSize v

-- | Turn a size view into a term.
unSizeView :: SizeView -> TCM Term
unSizeView SizeInf       = primSizeInf
unSizeView (SizeSuc v)   = flip apply [Arg NotHidden Relevant v] <$> primSizeSuc
unSizeView (OtherSize v) = return v
