module Interface.Command.Dump where
-- FIXME: Proper Exports

-- Standard Library Imports
import Data.List
 ( intersperse )

-- External Library Imports
import qualified Agda.Packaging.Config
  as Agda
import qualified Agda.Packaging.Database
  as Agda
import qualified Agda.Packaging.Monad
  as Agda
import Distribution.InstalledPackageInfo
  as Cabal

-- Local Library Imports
import Interface.Options

--------------------------------------------------------------------------------

dumpPkgs :: Agda.AgdaPkg Opt ()
dumpPkgs = Agda.asksM
         $ mapM_ (Agda.liftIO . putStrLn)
         . intersperse "---"
         . map Cabal.showInstalledPackageInfo
         . Agda.flattenPkgDBs
         . Agda.configPkgDBStack
