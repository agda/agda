{-# OPTIONS -cpp #-}

module TypeChecking.Records where

import Control.Applicative
import Control.Monad
import Data.List

import Syntax.Common
import qualified Syntax.Concrete.Name as C
import Syntax.Abstract.Name
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Substitute

#include "../undefined.h"
import Utils.Impossible

-- | Order the fields of a record construction.
orderFields :: MonadTCM tcm => QName -> [C.Name] -> [(C.Name, a)] -> tcm [a]
orderFields r xs fs = do
  shouldBeNull (ys \\ nub ys) $ DuplicateFields . nub
  shouldBeNull (ys \\ xs)     $ TooManyFields r
  shouldBeNull (xs \\ ys)     $ TooFewFields r
  return $ order xs fs
  where
    ys = map fst fs

    shouldBeNull [] err = return ()
    shouldBeNull xs err = typeError $ err xs

    -- invariant: both arguments contain the same fields
    -- TODO: a little inefficient
    order [] []	= []
    order (x : xs) ((y, e) : fs)
      | x == y	  = e : order xs fs
      | otherwise = order (x : xs) (fs ++ [(y, e)])
    order _ _ = __IMPOSSIBLE__

-- | The name of the module corresponding to a record.
recordModule :: QName -> ModuleName
recordModule = mnameFromList . qnameToList

-- | Get the definition for a record. Throws an exception if the name
--   does not refer to a record.
getRecordDef :: MonadTCM tcm => QName -> tcm Defn
getRecordDef r = do
  def <- theDef <$> getConstInfo r
  case def of
    Record _ _ _ _ _ _ -> return def
    _		       -> typeError $ ShouldBeRecordType (El Prop $ Def r [])

-- | Get the field names of a record.
getRecordFieldNames :: MonadTCM tcm => QName -> tcm [C.Name]
getRecordFieldNames r = do
  Record _ _ fs _ _ _ <- getRecordDef r
  return $ map (nameConcrete . qnameName) fs

-- | Get the field types of a record.
getRecordFieldTypes :: MonadTCM tcm => QName -> tcm Telescope
getRecordFieldTypes r = do
  Record _ _ _ tel _ _ <- getRecordDef r
  return tel

-- | Get the type of the record constructor.
getRecordConstructorType :: MonadTCM tcm => QName -> [Arg Term] -> tcm Type
getRecordConstructorType r pars = do
  Record _ _ _ tel s _ <- getRecordDef r
  return $ telePi (apply tel pars) $ El s $ Def r pars

-- | Check if a name refers to a record.
isRecord :: MonadTCM tcm => QName -> tcm Bool
isRecord r = do
  def <- theDef <$> getConstInfo r
  return $ case def of
    Record _ _ _ _ _ _ -> True
    _		       -> False

{-| Compute the eta expansion of a record. The first argument should be
    a record. Given

    @record R : Set where x : A; y : B@

    and @r : R@, @etaExpand R [] r@ is @[R.x r, R.y r]@
-}
etaExpandRecord :: MonadTCM tcm => QName -> Args -> Term -> tcm (Telescope, Args)
etaExpandRecord r pars u = do
  Record _ _ xs tel _ _ <- getRecordDef r
  let tel'   = apply tel pars
      proj x = Arg NotHidden $ Def x $ map hide pars ++ [Arg NotHidden u]
  return (tel', map proj xs)
  where
    hide (Arg _ x) = Arg Hidden x

