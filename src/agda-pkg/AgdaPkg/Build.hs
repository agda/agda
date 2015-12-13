{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
module AgdaPkg.Build where

import Control.Monad.Catch
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.Version
import System.Directory hiding (findFiles)
import System.Environment
import System.Exit
import System.FilePath
import System.Process

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.Hash (hash)
import qualified Data.Hash as H
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Maybe

import Agda.Compiler.Common
import Agda.TypeChecking.Monad.Base hiding (stPackageDBs)
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.State
import Agda.Interaction.Imports
import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Main
import Agda.Packaging.Base
import Agda.Packaging.Database
import Agda.TypeChecking.Monad.Imports (setPackageDBs)
import qualified Agda.Compiler.MAlonzo.Compiler as MAZ
import qualified Agda.Interaction.Highlighting.HTML as HTML
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import Agda.Syntax.Abstract (toTopLevelModuleName)

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.List

import Paths_Agda

import AgdaPkg.Error
import AgdaPkg.Monad
import AgdaPkg.PackageDesc

#include "undefined.h"
import Agda.Utils.Impossible

packageMatches :: PackageFilter -> Package -> Bool
packageMatches PAll _ = True
packageMatches PNone _ = False
packageMatches (PByPkgId ks) pkg = pkgId pkg `Set.member` ks


-- | Returns the files with the given file name suffixes. First element
-- is source dir path, second is file path relative to src dir.
findSourceFiles :: (MonadPkg m, MonadIO m) => BuildInfo -> Set String -> m [(FilePath, FilePath)]
findSourceFiles bldInfo suffs = concat <$> mapM (findFiles suffs) (bSrcDirs bldInfo)

findFiles :: (MonadPkg m, MonadIO m) => Set String -> FilePath -> m [(FilePath, FilePath)]
findFiles suffs dir = do
  pkgLoc <- pLocation <$> getCurrentPackage
  liftIO $ findFiles' suffs (pkgLoc </> dir)

findFiles' :: Set String -> FilePath -> IO [(FilePath, FilePath)]
findFiles' suffs srcDir = go srcDir "."
  where
    go srcDir rel = do
      chlds <- filter (not . flip elem [".", ".."]) <$> getDirectoryContents (srcDir </> rel)
      rs <- forM chlds $ \chld -> do
        isDir <- doesDirectoryExist (srcDir </> rel </> chld)
        if | isDir -> go srcDir (rel </> chld)
           | takeExtension chld `Set.member` suffs -> return [(srcDir, rel </> chld)]
           | otherwise -> return []
      return $ concat rs

buildSinglePackage :: (MonadIO m, MonadThrow m, MonadPkg m)
  => Targets -> m ()
buildSinglePackage targets =
  buildComponent targets . head . pComponents =<< getCurrentPackage

copyFiles :: [(FilePath, FilePath)] -> FilePath -> IO ()
copyFiles src dest = do
  for_ src $ \(base, rel) -> do
    createDirectoryIfMissing True (takeDirectory $ dest </> rel)
    copyFile (base </> rel) (dest </> rel)

resolveAgdaPackage
  :: (MonadThrow m, MonadPkg m)
  => PackageName
  -> VersionConstraint
  -> m PackageId
resolveAgdaPackage nm vc = do
  pkgs <- map snd . exposedPackages' <$> getPkgDBs
  let p = \c -> idName (pkgId c) == nm && constraintMatches (idVersion (pkgId c)) vc
  case filter p pkgs of
    [] -> throwM $ MissingDependency $ show nm ++ "-" ++ show vc
    [pkg] -> return $ pkgId pkg
    -- maybe just pick the newest one if there are multiple candidates?
    xs -> throwM $ GenericAgdaPkgError "No unique candidate package for constraints!"
  where
    constraintMatches :: Version -> VersionConstraint -> Bool
    constraintMatches v1 vc = case vc of
      VAny -> True
      VExactly v2 -> v1 == v2
      VAnd vcs -> all (constraintMatches v1) vcs

computePackageKey
  :: (MonadIO m, MonadThrow m, MonadPkg m)
  => [(FilePath, FilePath)] -- list of all source files
  -> m PackageKey
computePackageKey fs = do
  -- hash source files
  hs <-
    forM fs $ \(a,b) -> do
      h' <- liftIO $ hashFile (a </> b)
      -- also hash package-relative path
      return $ h' `H.combine` hash b
  -- hash package desc
  pkg <- getCurrentPackage
  pkgHash <- liftIO $ hashFile $ (pLocation pkg </> "agda-pkg.yaml")

  -- include the package key of all lib Agda dependencies
  let deps = pkg ^. (library' . buildInfo . dependencies . agdaDependencies)
  depHashes <- map (hashText . packageKey . idKey) <$> mapM (uncurry resolveAgdaPackage) (Map.toList deps)

  let h = foldl1 H.combine (pkgHash:hs ++ depHashes)

  return $ PackageKey $ T.pack $ show $ H.asWord64 h
  where
    hashByteString = BS.foldl' (\h b -> H.combine h (H.hashWord8 b)) (H.hashWord8 0)
    hashText = T.foldl' (\h c -> H.combine h (H.hash c)) (H.hash (0 :: Integer))
    hashFile = fmap hashByteString . BS.readFile

buildComponent :: (MonadPkg m, MonadIO m, MonadThrow m)
  => Targets -> Component -> m ()
buildComponent targets comp = do
  agdaFiles <- findSourceFiles (cBuildInfo comp) (Set.fromList [".agda", ".lagda"])
  hsFiles <- findSourceFiles (cBuildInfo comp) (Set.fromList [".hs"])
  pkgDesc <- getCurrentPackage
  bldDir <- getBuildDir

  -- compute package key
  pkgKey <- computePackageKey (agdaFiles ++ hsFiles)

  let pkgUnqName = (T.unpack $ pName pkgDesc) ++ "-" ++
                   (showVersion $ pVersion pkgDesc) ++ "-" ++
                   (T.unpack $ packageKey pkgKey)
      pkgDir = bldDir </> pkgUnqName </> "lib"
      cabalPkgDir = bldDir </> pkgUnqName </> "cabal-pkg"

  liftIO $ copyFiles agdaFiles (pkgDir </> "src")


  liftIO $ createDirectoryIfMissing True (cabalPkgDir </> "src")

  extraOpts <- getAgdaOptions
  opts <- caseEitherM
    (liftIO $ runOptM $ parseStandardOptions
      ((bAgdaOptions $ cBuildInfo comp) ++ extraOpts))
    (throwM . InvalidAgdaOptions)
    (\opts -> return $ opts
    -- Note: we use the original Agda files for compilation, we only copy the sources into the
    -- package for documentation purposes. Maybe we should use the copied Agda files
    -- to make sure a package is consistent? However, it would be nice if we still get
    -- the original file paths in error messages.
                        { optIncludePaths   = map (pLocation pkgDesc </>) (bSrcDirs $ cBuildInfo comp)
                        --[pkgDir </> "src"]
                        , optInterfaceDir   = Just $ pkgDir </> "ifaces"
                        , optCompileDir     = Just $ cabalPkgDir </> "src"
                        , optDefaultLibs    = False
                        , optLaTeXDir       = pkgDir </> "doc" </> "LaTeX"
                        }
    )

  dbStack <- getPkgDBs
  let deps = pkgDesc ^. (library' . buildInfo . dependencies . agdaDependencies)
  depsPkgIds <- Set.fromList <$> mapM (uncurry resolveAgdaPackage) (Map.toList deps)
  let dbStack' = filterPkgDBs (packageMatches (PByPkgId depsPkgIds)) dbStack

  liftIO $ runTCMPrettyErrors' $ do
    setCommandLineOptions opts

    setPackageDBs dbStack'

    importPrimitiveModules

    ifaces <- mapM (\(x, y) -> typeCheck (x </> y)) agdaFiles

    -- generate html docs
    when (HtmlDoc `Set.member` targets) $ do
      let htmlDir = pkgDir </> "doc" </> "html"
      liftIO $ createDirectoryIfMissing  True htmlDir
      -- copy css file
      cssFile <- liftIO $ getDataFileName "Agda.css"
      liftIO $ copyFile cssFile (htmlDir </> "Agda.css")
      -- generate html
      mapM_ (generateHTMLDocs htmlDir) ifaces

    when (LaTeXDoc `Set.member` targets) $ do
      let latexDir = pkgDir </> "doc" </> "LaTeX"
      liftIO $ createDirectoryIfMissing  True latexDir

      mapM_ (\i -> LaTeX.generateLaTeX (toTopLevelModuleName $ iModuleName i) (iHighlighting i)) ifaces

    when (CabalPackage `Set.member` targets) $ do
      -- compile
      localTCState $ ignoreAbstractMode $ mapM_ (\i -> setInterface i >> MAZ.compile i) ifaces
      -- copy hs files
      liftIO $ copyFiles hsFiles (cabalPkgDir </> "src")

    return ()

  when (CabalPackage `Set.member` targets) $ do
    writeCabalFile cabalPkgDir

  let pkgId = PackageId
        { idKey = pkgKey
        , idName = pName pkgDesc
        , idVersion = pVersion pkgDesc
        }
      pkg = Package
        { pkgId = pkgId
        , pkgDependencies = depsPkgIds
        , pkgSrc = pkgUnqName </> "lib" </> "src"
        , pkgDoc = pkgUnqName </> "lib" </> "doc"
        , pkgIfaces = pkgUnqName </> "lib" </> "ifaces"
        }
  liftIO $ writePackage (bldDir </> pkgUnqName <.> ".apkg") pkg


installSinglePackage :: (MonadPkg m, MonadIO m, MonadThrow m)
  => Targets -> m ()
installSinglePackage targets = do
  buildSinglePackage targets
  copySinglePackage

getTopPackageDB :: (MonadPkg m) => m PkgDB
getTopPackageDB = head . stkDBs <$> getPkgDBs

copySinglePackage :: (MonadPkg m, MonadIO m) => m ()
copySinglePackage = do
  buildDir <- getBuildDir

  targetDb <- getTopPackageDB

  -- we need to copy everything in builddir
  liftIO $ copyDirContent buildDir (dbPath targetDb)


generateHTMLDocs :: FilePath -> Interface -> TCM ()
generateHTMLDocs outDir i = do
  HTML.generatePage renderer outDir mod
  where
    mod = toTopLevelModuleName $ iModuleName i
    renderer css _ contents = HTML.page css mod $ HTML.code $ HTML.tokenStream contents (iHighlighting i)


writeCabalFile :: (MonadPkg m, MonadIO m) => FilePath -> m ()
writeCabalFile f = do
  pkg <- getCurrentPackage
  (_, fs) <- unzip <$> findFiles (Set.fromList [".hs"]) (f </> "src")

  let Just lib = pkg ^. library
      deps = lib ^. (buildInfo . dependencies)
      agdaDeps' = deps ^. agdaDependencies
      agdaDeps = map (T.unpack . T.append "Agda-" . fst) $ Map.toList agdaDeps'
      hsDeps   = map (T.unpack . fst) $ Map.toList $ deps ^. hsDependencies
      expMods = map (intercalate "." . splitDirectories . normalise . dropExtension) fs

  let content = unlines
        [ "name: Agda-" ++ T.unpack (pName pkg)
        , "version: " ++ showVersion (pVersion pkg)
        , "build-type: Simple"
        , "cabal-version: >= 1.10"
        , "library"
        , "  default-language: Haskell2010"
        , "  exposed-modules: " ++ intercalate ", " expMods
        , "  hs-source-dirs:  src"
        , "  build-depends:   " ++ intercalate ", "
            (["base >= 4.8 && <4.9", "Agda-MAlonzo-RTE"] ++ agdaDeps ++ hsDeps)
        ]
  liftIO $ writeFile (f </> "Agda-" ++ T.unpack (pName pkg) <.> ".cabal") content
  liftIO $ writeFile (f </> "Setup.hs") $ unlines
        [ "import Distribution.Simple"
        , "main = defaultMain"
        ]

typeCheck :: FilePath -> TCM Interface
typeCheck relPath = do
  m <- moduleName =<< liftIO (absolute relPath)
  (i, mw) <- getInterface' m NotMainInterface
  case mw of
    -- Unsolved metas.
    SomeWarnings (Warnings w@(_:_) _) -> typeError $ UnsolvedMetas w
    -- Unsolved constraints.
    SomeWarnings (Warnings _ w@(_:_)) -> typeError $ UnsolvedConstraints w
    NoWarnings -> return i
    _ -> __IMPOSSIBLE__

withSinglePackage :: (Monad m, MonadThrow m, MonadIO m, MonadMask m)
  => FilePath -> GlobalOptions
  -> PkgT m a -> m a
withSinglePackage dir opts cont = do
  let pkgDescFile = dir </> "agda-pkg.yaml"
  hasPkgDesc <- liftIO $ doesFileExist pkgDescFile

  agdaDBs <- readAgdaPkgDBs opts

  let agdaDBStack = PkgDBStack
        { stkDBs = agdaDBs
        , stkPkgExposed = packageMatches (gPkgFilter opts)
        }

  if not hasPkgDesc then do
    throwM $ MissingPackageFile
  else do
    pkgDesc <- readPackageDesc pkgDescFile

    withBuildDir (gBuildDir opts) $ \buildDir -> do
      let buildEnv = PackageBuildEnv
            { pbePackage = pkgDesc
            , pbeBuildDir = buildDir
            , pbePkgDBs = agdaDBStack
            , pbeAgdaOpts = gAgdaOpts opts
            }
      runPkgT buildEnv cont
  where
    withBuildDir (WithDir f) cont = cont f
    withBuildDir (TempDir) cont =
      withTempDir "agda-setup" cont

getPathFromEnv :: MonadIO m => String -> m [String]
getPathFromEnv var =
  wordsBy (==':') . fromMaybe "" . lookup var <$> liftIO getEnvironment

readAgdaPkgDBs :: (MonadThrow m, MonadIO m) => GlobalOptions -> m [PkgDB]
readAgdaPkgDBs opts =
  doRead . (++ extraDBs) =<< getPathFromEnv "AGDA_PACKAGE_PATH"
  where
    extraDBs = reverse $ gPkgDBs opts
    doRead :: (MonadIO m, MonadThrow m) => [FilePath] -> m [PkgDB]
    doRead pkgDBs = liftIO $ exceptTToThrow GenericAgdaPkgError $ mapM readPkgDB pkgDBs



callProcess' :: FilePath -> FilePath -> [String] -> IO ()
callProcess' wd exe args = do
  (_, _, _, p) <- createProcess $ (proc exe args) { cwd = Just wd }
  r <- waitForProcess p
  case r of
    ExitSuccess   -> return ()
    ExitFailure _ -> do
      throwM $ ExternalProcessError exe ""


-- | Run a TCM action in IO; catch, pretty print and rethrow errors.
runTCMPrettyErrors' :: (MonadIO m, MonadThrow m) => TCM a -> m a
runTCMPrettyErrors' tcm = do
  r <- liftIO $ runTCMTop' $ (Right <$> tcm) `catchError` \err -> do
    s <- prettyError err
    return $ Left $ AgdaError err s

  either throwM return r

withTempDir :: (MonadIO m, MonadMask m) => FilePath -> (FilePath -> m a) -> m a
withTempDir nm a = do
  temp <- liftIO getTemporaryDirectory
  let tempDir = temp </> nm

  bracket
    (liftIO $ createDirectory tempDir)
    (const $ liftIO $ removeDirectoryRecursive tempDir)
    (\_ -> a tempDir)
