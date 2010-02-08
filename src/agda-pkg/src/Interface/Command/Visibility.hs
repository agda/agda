module Interface.Command.Visibility where
-- FIXME: Proper Exports

-- Standard Library Imports
import Control.Monad.Trans
  ( liftIO )

-- External Library Imports
import qualified Agda.Packaging.Database
  as Agda
import qualified Agda.Packaging.Monad
  as Agda
import qualified Distribution.InstalledPackageInfo
  as Cabal
import qualified Distribution.Simple.Utils
  as Cabal
import qualified Distribution.Text
  as Cabal

-- Local Library Imports
import Interface.Options

--------------------------------------------------------------------------------

modifyPkgVisibility :: (Cabal.InstalledPackageInfo -> Agda.DBOp)
                    -> String
                    -> Agda.AgdaPkg Opt ()
modifyPkgVisibility funToOp strPkgId =
  case Cabal.simpleParse strPkgId of
    Nothing    -> liftIO $ Cabal.die $ "invalid pkg id: " ++ strPkgId
    Just pkgId -> pkgId `Agda.modifyPkgInfoAndWriteDBWithFun` funToOp

exposePkg :: String -> Agda.AgdaPkg Opt ()
exposePkg =  modifyPkgVisibility (\ pkgInfo -> Agda.PkgModify pkgInfo{ Cabal.exposed = True  } )

hidePkg   :: String -> Agda.AgdaPkg Opt ()
hidePkg   =  modifyPkgVisibility (\ pkgInfo -> Agda.PkgModify pkgInfo{ Cabal.exposed = False } )
