import Control.Monad
import Data.List
import Distribution.InstalledPackageInfo
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Simple.Configure
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.PackageIndex
import Distribution.Text
import Distribution.Types.GenericPackageDescription
import Distribution.Types.PackageId
import Distribution.Types.PackageName
import Distribution.Verbosity
import Distribution.Version
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.IO.Temp
import System.Process

-- | Usage information.

usage :: String
usage = unlines
  [ "agda-licences <dist>"
  , ""
  , "Prints the declared licence of every Cabal package that the Agda"
  , "binary depends on (as determined by the configuration in the Cabal"
  , "build directory <dist>), as well as the declared licence of Agda"
  , "itself. Note that the binary may depend on non-Cabal packages as"
  , "well."
  , ""
  , "The licence printed for the rts package is that of (some version"
  , "of) the ghc package."
  , ""
  , "This program does not work properly unless a suitable version of"
  , "cabal-install is available."
  ]

-- | A header, printed before the licences.

header :: String
header = unlines $
  [ "The Agda binaries depend on a number of libraries. This text is an"
  , "attempt at listing the copyright statements and licences of all"
  , "Cabal packages that Agda depends on. The corresponding information"
  , "for other dependencies is hopefully available elsewhere."
  , ""
  ]

-- | The top-level program.

main :: IO ()
main = do
  -- Get the localBuildInfo.
  args           <- getArgs
  localBuildInfo <- case args of
    [d] -> getPersistBuildConfig d
    _   -> exit Nothing

  -- Locate Agda.cabal.
  agdaCabal <- case pkgDescrFile localBuildInfo of
    Nothing -> exit $ Just "Agda.cabal was not found."
    Just f  -> return f

  -- Print a header.
  putStr header

  -- Try to print the licence of Agda's source code.
  printLicenses Nothing agdaCabal
  putStrLn ""

  -- Try to print the licences of Agda's dependencies.
  forAndIntersperseM_
    (allPackages $ installedPkgs localBuildInfo)
    (putStrLn "") $ \pkg -> do

    let realPkgId = sourcePackageId pkg
        pkgId
            -- For some reason integer-gmp-1.0.1.0 is not available on
            -- Hackage, but it seems as if integer-gmp-1.0.0.1 has the
            -- same licence.
          | unPackageName (pkgName realPkgId) == "integer-gmp" &&
            pkgVersion realPkgId == mkVersion [1,0,1,0] = realPkgId { pkgVersion = mkVersion [1,0,0,1] }
          | unPackageName (pkgName realPkgId) == "rts" = PackageIdentifier { pkgName    = mkPackageName "ghc"
                               , pkgVersion = nullVersion
                               }
            -- Replace the rts package, which cannot be unpacked, with
            -- the ghc package.
          | otherwise = realPkgId

    withSystemTempDirectory "agda-licenses" $ \tempDir -> do
      pkgDir <-
        dropFinalNewline . drop (length "Unpacking to ") <$>
        readProcess "cabal" [ "unpack"
                            , "--destdir=" ++ tempDir
                            , display pkgId
                            ]
                            ""
      cabalFiles <-
        filter ((== ".cabal") . takeExtension) <$>
        getDirectoryContents pkgDir
      cabalFile <- case cabalFiles of
        [c] -> return c
        cs  -> error $ "Not a unique Cabal file: " ++
                       intercalate ", " cs
      withCurrentDirectory pkgDir $
        printLicenses (Just $ display realPkgId) cabalFile
  where
  dropFinalNewline s = case lines s of
    []      -> ""
    (s : _) -> s

-- | Tries to print the declared licences for the given Cabal file.
--
-- If a string is given, then this string is used as a header, and
-- otherwise the package identifier is used.

printLicenses :: Maybe String -> FilePath -> IO ()
printLicenses header cabalFile = do
  desc <- packageDescription <$>
            readGenericPackageDescription silent cabalFile
  hrule '='
  putStrLn $ case header of
    Nothing -> display (package desc)
    Just s  -> s
  hrule '='
  putStrLn ""
  forAndIntersperseM_
    (licenseFiles desc)
    (do putStrLn ""
        hrule '-'
        putStrLn "")
    ((putStr . unlines . lines) <=< readFile)
  where
  hrule c = putStrLn $ replicate 72 c

-- | Perform the second action for every element in the list, and
-- perform the first action once in between any two of the former
-- actions.

forAndIntersperseM_ :: Monad m => [a] -> m () -> (a -> m ()) -> m ()
forAndIntersperseM_ xs a f =
  forM_ (intersperse Nothing $ map Just xs) $ \x ->
    maybe a f x

-- | Prints the given error message (if any) and usage information to
-- stderr, and exits with an exit code signalling failure.

exit :: Maybe String -> IO a
exit s = do
  case s of
    Nothing -> return ()
    Just s  -> hPutStr stderr $ s ++ "\n\n"
  hPutStr stderr usage
  exitFailure
