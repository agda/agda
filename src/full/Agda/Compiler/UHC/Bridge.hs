{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Exports the UHC API, and provides dummy
-- definitions if the backend is disabled.
module Agda.Compiler.UHC.Bridge
  ( uhcBackendEnabled

  -- UHC.Util.Pretty
  , PP_Doc
  , putPPFile
  , disp
  , pp

  -- UHC.Util.Serialize
  , Serialize
  , putSerializeFile
  , serialize
  , unserialize

  -- UHC.Light.Compiler.Base.API
  , EHCOpts
  , defaultEHCOpts
  , HsName
  , CTag
  , mkHsName
  , mkHsName1
  , mkUniqueHsName

  -- UHC.Light.Compiler.Core.API
  , CModule
  , CImport
  , CExport
  , CDeclMeta
  , CDataCon
  , CExpr
  , CBind
  , CAlt
  , CPat
  , CPatFld
--  , CPatRest

  , mkUnit
  , mkInt
  , mkInteger
  , mkChar
  , mkString
  , mkError
  , mkUndefined
  , mkVar
  , mkLet1Plain
  , mkLet1Strict
  , mkLetRec
  , mkLam
  , mkApp
  , mkBind1
  , mkBind1Nm1
  , mkCTag
  , destructCTag
  , ctagUnit
  , ctagTrue
  , ctagFalse
  , ctagCons
  , ctagNil
  , mkCase
  , mkAlt
  , mkPatCon
  , mkPatRestEmpty
  , mkPatFldBind
  , mkTagTup
  , mkModule
  , mkImport
  , mkExport
  , mkMetaData
  , mkMetaDataCon
  , mkMetaDataConFromCTag
  , mkMain
  , parseExpr
  , printModule
  ) where

#include "undefined.h"
import Agda.Utils.Impossible

import Data.Binary.Put
import Data.Binary.Get
import Data.Typeable

#if defined(UHC_BACKEND)
import UHC.Util.Pretty
import UHC.Util.Serialize
import UHC.Util.ParseUtils
import UHC.Util.ScanUtils
import UU.Scanner.Position

import UHC.Light.Compiler.Core.API
import UHC.Light.Compiler.Base.API
#else

-- UHC.Util.Pretty
type PP_Doc = String

class Show a => PP a where
  pp :: a -> PP_Doc

instance PP CExpr where
  pp CExpr_DUMMY = "DUMMY - UHC backend is disabled"

putPPFile :: String -> PP_Doc -> Int -> IO ()
putPPFile = __IMPOSSIBLE__

disp :: PP_Doc -> Int -> ShowS
disp s _ = (s ++)

-- UHC.Util.Serialize
class Serialize a where

putSerializeFile :: FilePath -> a -> IO ()
putSerializeFile = __IMPOSSIBLE__

serialize :: x -> Put
serialize = __IMPOSSIBLE__

unserialize :: Get x
unserialize = __IMPOSSIBLE__

-- UHC.Light.Compiler.Base.API

data EHCOpts
defaultEHCOpts :: EHCOpts
defaultEHCOpts = __IMPOSSIBLE__

data HsName deriving (Typeable)
deriving instance Eq HsName
deriving instance Ord HsName
deriving instance Show HsName
instance Serialize HsName where

data CTag deriving (Typeable)
deriving instance Eq CTag
deriving instance Ord CTag
deriving instance Show CTag
instance Serialize CTag where

mkHsName :: [String] -> String -> HsName
mkHsName = __IMPOSSIBLE__

mkHsName1 :: String -> HsName
mkHsName1 = __IMPOSSIBLE__

mkUniqueHsName :: String -> [String] -> String -> HsName
mkUniqueHsName = __IMPOSSIBLE__

-- UHC.Light.Compiler.Core.API
data CModule
instance Serialize CModule
data CImport
data CExport
data CDeclMeta
data CDataCon
-- dummy to use as parse result for core pragmas
data CExpr = CExpr_DUMMY deriving (Eq, Ord, Show, Typeable)
instance Serialize CExpr where
data CBind
data CAlt
data CPat
data CPatFld
data CPatRest

mkUnit :: EHCOpts -> CExpr
mkUnit = __IMPOSSIBLE__

mkInt :: EHCOpts -> Int -> CExpr
mkInt = __IMPOSSIBLE__

mkInteger :: EHCOpts -> Integer -> CExpr
mkInteger = __IMPOSSIBLE__

mkChar :: Char -> CExpr
mkChar = __IMPOSSIBLE__

mkString :: EHCOpts -> String -> CExpr
mkString = __IMPOSSIBLE__

mkError :: EHCOpts -> String -> CExpr
mkError = __IMPOSSIBLE__

mkUndefined :: EHCOpts -> CExpr
mkUndefined = __IMPOSSIBLE__

mkVar :: HsName -> CExpr
mkVar = __IMPOSSIBLE__

mkLet1Plain :: HsName -> CExpr -> CExpr -> CExpr
mkLet1Plain = __IMPOSSIBLE__

mkLet1Strict :: HsName -> CExpr -> CExpr -> CExpr
mkLet1Strict = __IMPOSSIBLE__

mkLetRec :: [CBind] -> CExpr -> CExpr
mkLetRec = __IMPOSSIBLE__

mkLam :: [HsName] -> CExpr -> CExpr
mkLam = __IMPOSSIBLE__

mkApp :: CExpr -> [CExpr] -> CExpr
mkApp = __IMPOSSIBLE__

mkBind1 :: HsName -> CExpr -> CBind
mkBind1 = __IMPOSSIBLE__

mkBind1Nm1 :: HsName -> CBind
mkBind1Nm1 = __IMPOSSIBLE__

mkCTag :: HsName -> HsName -> Int -> Int -> CTag
mkCTag = __IMPOSSIBLE__

destructCTag :: a -> (HsName -> HsName -> Int -> Int -> a) -> CTag -> a
destructCTag = __IMPOSSIBLE__

ctagUnit :: CTag
ctagUnit = __IMPOSSIBLE__

ctagTrue :: EHCOpts -> CTag
ctagTrue = __IMPOSSIBLE__

ctagFalse :: EHCOpts -> CTag
ctagFalse = __IMPOSSIBLE__

ctagCons :: EHCOpts -> CTag
ctagCons = __IMPOSSIBLE__

ctagNil :: EHCOpts -> CTag
ctagNil = __IMPOSSIBLE__

mkCase :: CExpr -> [CAlt] -> CExpr
mkCase = __IMPOSSIBLE__

mkAlt :: CPat -> CExpr -> CAlt
mkAlt = __IMPOSSIBLE__

mkPatCon :: CTag -> CPatRest -> [CPatFld] -> CPat
mkPatCon = __IMPOSSIBLE__

mkPatRestEmpty :: CPatRest
mkPatRestEmpty = __IMPOSSIBLE__

mkPatFldBind :: (HsName, CExpr) -> CBind -> CPatFld
mkPatFldBind = __IMPOSSIBLE__

mkTagTup :: CTag -> [CExpr] -> CExpr
mkTagTup = __IMPOSSIBLE__

mkModule :: HsName -> [CExport] -> [CImport] -> [CDeclMeta] -> CExpr -> CModule
mkModule = __IMPOSSIBLE__

mkImport :: HsName -> CImport
mkImport = __IMPOSSIBLE__

mkExport :: HsName -> CExport
mkExport = __IMPOSSIBLE__

mkMetaData :: HsName -> [CDataCon] -> CDeclMeta
mkMetaData = __IMPOSSIBLE__

mkMetaDataCon :: HsName -> Int -> Int -> CDataCon
mkMetaDataCon = __IMPOSSIBLE__

mkMetaDataConFromCTag :: CTag -> Maybe CDataCon
mkMetaDataConFromCTag = __IMPOSSIBLE__

mkMain :: HsName -> CExpr
mkMain = __IMPOSSIBLE__

parseExpr :: EHCOpts -> String -> Either [String] CExpr
-- just always succeed, as we don't want to fail on UHC pragmas
-- if the backend is disabled
parseExpr _ _ = Right CExpr_DUMMY

printModule :: EHCOpts -> CModule -> PP_Doc
printModule = __IMPOSSIBLE__

#endif



uhcBackendEnabled :: Bool
#if defined(UHC_BACKEND)
uhcBackendEnabled = True
#else
uhcBackendEnabled = False
#endif
