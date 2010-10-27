module Interface.Command.List where

-- Standard Library Imports
import Data.List
  ( sortBy )
import Text.PrettyPrint

-- External Library Imports
import qualified Agda.Packaging.Config
  as Agda
import qualified Agda.Packaging.Database
  as Agda
import qualified Agda.Packaging.Monad
  as Agda
import qualified Agda.Packaging.Types
  as Agda
import qualified Distribution.InstalledPackageInfo
  as Cabal
    ( InstalledPackageInfo
    , exposed
    , installedPackageId
    , sourcePackageId )
import qualified Distribution.Package
  as Cabal
    ( pkgName
    , pkgVersion )
import qualified Distribution.Text
  as Cabal
    ( display )

-- Local Library Imports
import Interface.Options

--------------------------------------------------------------------------------

-- FIXME: Load GHC pkgs to determine whether or not things are broken
-- FIXME: add filtering support
listPkgs :: Agda.AgdaPkg Opt ()
listPkgs = do
  pkgDBStack <- Agda.asks Agda.configPkgDBStack
  mapM_ ppNamedPkgDB pkgDBStack
  where
    ppNamedPkgDB :: Agda.NamedPackageDB -> Agda.AgdaPkg Opt ()
    ppNamedPkgDB namedPkgDB = Agda.asksM
                            $ Agda.liftIO
                            . putStrLn
                            . render
                            . perNamedPkgDB namedPkgDB
                            . Agda.configPkgDBStack

    perNamedPkgDB :: Agda.NamedPackageDB -> Agda.PackageDBStack -> Doc
    perNamedPkgDB namedPkgDB pkgDBStack =
      text (Agda.dbName namedPkgDB) <> colon $$
        (nest 4 $ vcat $ sortedPkgNamesDoc)
      where
        sortedPkgNamesDoc :: [Doc]
        sortedPkgNamesDoc = map perInstalledPkgInfo
                          $ sortBy sortInstalledPkgInfos
                          $ Agda.db namedPkgDB

        perInstalledPkgInfo :: Cabal.InstalledPackageInfo -> Doc
        perInstalledPkgInfo ipi
          | Cabal.installedPackageId ipi `elem` brokenPkgs = braces $ doc
          | Cabal.exposed            ipi                   =          doc
          | otherwise                                      = parens $ doc
          where
            brokenPkgs = map Cabal.installedPackageId
                       $ Agda.brokenPkgs
                       $ Agda.flattenPkgDBs
                       $ pkgDBStack

            doc        = text
                       $ Cabal.display
                       $ Cabal.sourcePackageId ipi

        sortInstalledPkgInfos :: Cabal.InstalledPackageInfo
                              -> Cabal.InstalledPackageInfo
                              -> Ordering
        sortInstalledPkgInfos ipi1 ipi2 =
          case pkgInfoName ipi1 `compare` pkgInfoName ipi2 of
            LT -> LT
            GT -> GT
            EQ -> pkgInfoVersion ipi1 `compare` pkgInfoVersion ipi2
          where
            pkgInfoName    = Cabal.pkgName    . Cabal.sourcePackageId
            pkgInfoVersion = Cabal.pkgVersion . Cabal.sourcePackageId
