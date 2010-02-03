module Interface.Command.Visibility where
-- FIXME: Proper Exports

-- Standard Library Imports
import qualified Distribution.InstalledPackageInfo
  as Cabal
import qualified Distribution.Text
  as Cabal

-- External Library Imports
import qualified Agda.Packaging.Database
  as Agda
import qualified Agda.Packaging.Monad
  as Agda

-- Local Library Imports
import Interface.Options

--------------------------------------------------------------------------------

-- FIXME: error handling
modifyPkgVisibility :: Bool -> String -> Agda.AgdaPkg Opt ()
modifyPkgVisibility makeVisible sPkgId =
  case Cabal.simpleParse sPkgId of
    Nothing    -> error $ "invalid pkg id: " ++ sPkgId
    Just pkgId -> Agda.modifyPkgInDB pkgId f
      where
        f :: Cabal.InstalledPackageInfo -> Cabal.InstalledPackageInfo
        f p = p { Cabal.exposed = makeVisible }


exposePkg :: String -> Agda.AgdaPkg Opt ()
exposePkg = modifyPkgVisibility True

hidePkg :: String -> Agda.AgdaPkg Opt ()
hidePkg = modifyPkgVisibility True