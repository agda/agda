{-# LANGUAGE OverloadedStrings #-}

module Interface.Command.Register where
-- FIXME: Proper Exports

-- Standard Library Imports
import Control.Applicative
import qualified Data.ByteString.Char8
  as BS
import qualified Distribution.ParseUtils
  as Cabal
import qualified Distribution.InstalledPackageInfo
  as Cabal
import System.Environment
-- import qualified Distribution.Text
--   as Cabal

-- External Library Imports
import qualified Agda.Packaging.Config
  as Agda
import qualified Agda.Packaging.Database
 as Agda
import qualified Agda.Packaging.Monad
  as Agda
import qualified Agda.Packaging.Types
  as Agda

-- Local Library Imports
import Interface.Exit
import Interface.Options
--import Utils

--------------------------------------------------------------------------------

envRegex :: BS.ByteString
envRegex = BS.pack "\\${[a-zA-Z0-9_]+}"

envSubst :: BS.ByteString -> IO BS.ByteString
envSubst s
  |  ("${" `BS.isPrefixOf`) s
  && ("}"  `BS.isSuffixOf`) s = BS.pack <$> result
  | otherwise                 = return s
    where
      result = getEnv
             $ BS.unpack
             $ BS.takeWhile (/= '}')
             $ BS.drop 2 s

registerPkg :: FilePath -> Agda.AgdaPkg Opt ()
registerPkg fileName = undefined
  -- FIXME: rewrite
  {-
  do
  npkgDBs <- Agda.asks Agda.configPkgDBStack
  case npkgDBs of
    []           -> undefined
    dbToModify:_ -> do
      contents         <- Agda.liftIO $
        if fileName == "-" then
          BS.getContents
        else
          BS.readFile fileName
      expandedContents <- return contents
      pkgInfo          <- parsePkgInfo expandedContents
      let cond pkgInfo' = Cabal.installedPackageId pkgInfo'
                       /= Cabal.installedPackageId pkgInfo
          newDB         = pkgInfo : filter cond $ Agda.db dbToModify
      Agda.writePkgDBToFile newDB $ Agda.dbName dbToModify
  where
    parsePkgInfo :: BS.ByteString
                 -> Agda.AgdaPkg Opt Cabal.InstalledPackageInfo
    parsePkgInfo contents =
      case Cabal.parseInstalledPackageInfo $ BS.unpack contents of
        Cabal.ParseFailed err    ->
          case Cabal.locatedErrorMsg err of
            (Nothing, s) -> Agda.liftIO $ die                     s
            (Just l , s) -> Agda.liftIO $ die $ show l ++ ": " ++ s
        Cabal.ParseOk _warns res -> do
          return res
    -}
