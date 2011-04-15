{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Datatypes where

import Data.List

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible

#include "../undefined.h"

-- | Get the name of the datatype constructed by a given constructor.
--   Precondition: The argument must refer to a constructor
getConstructorData :: MonadTCM tcm => QName -> tcm QName
getConstructorData c = do
  def <- getConstInfo c
  case theDef def of
    Constructor{conData = d} -> return d
    _                        -> __IMPOSSIBLE__

-- | Check if a name refers to a datatype or a record with a named constructor.
isDatatype :: MonadTCM tcm => QName -> tcm Bool
isDatatype d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{}                   -> return True
    Record{recNamedCon = namedC} -> return namedC
    _                            -> return False

-- | Check if a name refers to a datatype or a record.
isDataOrRecordType :: MonadTCM tcm => QName -> tcm Bool
isDataOrRecordType d = do
  def <- getConstInfo d
  case theDef def of
    Datatype{} -> return True
    Record{}   -> return True
    _          -> return False

data DatatypeInfo = DataInfo
  { datatypeName   :: QName
  , datatypeParTel :: Telescope
  , datatypePars   :: Args
  , datatypeIxTel  :: Telescope
  , datatypeIxs    :: Args
  }

-- | Get the name and parameters from a type if it's a datatype or record type
--   with a named constructor.
getDatatypeInfo :: MonadTCM tcm => Type -> tcm (Maybe DatatypeInfo)
getDatatypeInfo t = do
  t <- reduce t
  case unEl t of
    Def d args -> do
      n          <- getDefFreeVars d
      args       <- return $ genericDrop n args
      def        <- instantiateDef =<< getConstInfo d
      TelV tel _ <- telView (defType def)
      let npars  = case theDef def of
            Datatype{dataPars = np} -> Just np
            Record{recPars = np, recNamedCon = True}
              | genericLength args == np -> Just np
              | otherwise                -> __IMPOSSIBLE__
            _                            -> Nothing
      return $ do
        np <- npars
        let (pt, it) = genericSplitAt np $ telToList tel
            parTel   = telFromList pt
            ixTel    = telFromList it
            (ps, is) = genericSplitAt np args
        return $ DataInfo { datatypeName = d
                          , datatypeParTel = parTel
                          , datatypePars   = ps
                          , datatypeIxTel  = ixTel
                          , datatypeIxs    = is
                          }
    _ -> return Nothing
