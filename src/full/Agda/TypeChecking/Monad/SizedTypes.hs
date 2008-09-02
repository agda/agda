
module Agda.TypeChecking.Monad.SizedTypes where

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
isSizeType :: MonadTCM tcm => Type -> tcm Bool
isSizeType (El _ v) = liftTCM $
  ifM (not . optSizedTypes <$> commandLineOptions) (return False) $
  case v of
    Def x [] -> do
      Def size [] <- primSize
      return $ x == size
    _ -> return False
  `catchError` \_ -> return False

sizeType :: MonadTCM tcm => tcm Type
sizeType = El (Type 0) <$> primSize

-- | A useful view on sizes.
data SizeView = SizeInf | SizeSuc Term | OtherSize Term

-- | Compute the size view of a term. The argument should be 'reduce'd.
--   Precondition: sized types are enabled.
sizeView :: MonadTCM tcm => Term -> tcm SizeView
sizeView v = do
  Def inf [] <- primSizeInf
  Def suc [] <- primSizeSuc
  case v of
    Def x []  | x == inf -> return SizeInf
    Def x [u] | x == suc -> return $ SizeSuc (unArg u)
    _                    -> return $ OtherSize v

-- | Turn a size view into a term.
unSizeView :: MonadTCM tcm => SizeView -> tcm Term
unSizeView SizeInf       = primSizeInf
unSizeView (SizeSuc v)   = flip apply [Arg NotHidden v] <$> primSizeSuc
unSizeView (OtherSize v) = return v

