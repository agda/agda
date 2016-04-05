{-# LANGUAGE DoAndIfThenElse #-}
module Main where

import System.FilePath
import Options.Applicative
import Data.List
import qualified Data.Set as Set
import Data.Version
import Data.Maybe

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Catch

import System.Directory
import System.Process

import AgdaPkg.PackageDesc
import AgdaPkg.Monad
import AgdaPkg.Build
import AgdaPkg.Error
import AgdaPkg.Internal

import Agda.Packaging.Database
import Agda.Packaging.Base

import Agda.Utils.IO.Directory
import Agda.Utils.Except
import Paths_Agda


data Options
  = Options
  { optCommand :: Command
  , optGlobalOpts :: GlobalOptions
  }
  deriving (Show)

data Command
  = BuildPackage Targets
  | InstallPackage Targets
  | InitPackageDb FilePath
  deriving (Show)

targetParser :: Parser Targets
targetParser = (\x y z -> Set.unions [x, y, z])
  <$> tgFlag True "html-documentation" HtmlDoc
  <*> tgFlag False "latex-documentation" LaTeXDoc
  <*> tgFlag True "cabal-package" CabalPackage
  where
    tgFlag def t g = (\x -> if x then Set.singleton g else Set.empty)
                <$> booleanFlag def (long (t)) (long ("no-" ++ t))

booleanFlag :: Bool -> Mod FlagFields Bool -> Mod FlagFields Bool -> Parser Bool
booleanFlag def yes no = (\x y -> if x || y then x && not y else def)
  <$> flag False True yes
  <*> flag False True no



initPackageDbOptions :: Parser Command
initPackageDbOptions = InitPackageDb
  <$> argument str (metavar "PATH")

fcommand :: Parser Command
fcommand = subparser
    (   command "build" (info (BuildPackage <$> targetParser)
        (progDesc "Build a single package."))
    <>  command "install" (info (InstallPackage <$> targetParser)
        (progDesc "Install a package into the package db."))
    <>  command "init-pkg-db" (info initPackageDbOptions
       (progDesc "Initialize a new package db."))
    )

globalOptions :: Parser GlobalOptions
globalOptions = GlobalOptions
  <$> many (strOption (long "agda-option" <> metavar "OPT" <> help "Extra Agda options"))
  <*> buildDir
  <*> (defDB <$> many (strOption (long "agda-package-db" <> metavar "DIR" <> help "Add an Agda Package Package DB")))
  <*> pure PAll
  where
    buildDir :: Parser BuildDir
    buildDir = fromMaybe (WithDir "_build")
      <$> ((Just . WithDir <$> (strOption (long "build-dir" <> metavar "DIR" <> help "Build directory")))
        <|> (flag Nothing (Just TempDir) (long "temp-build-dir" <> help "Use a temporary build directory"))
        )
    defDB [] = ["__GLOBAL_DB__"]
    defDB xs = xs

opts :: Parser Options
opts = Options
  <$> fcommand
  <*> globalOptions

main :: IO ()
main = do
  opts <- execParser
    (info (helper <*> opts)
          (fullDesc <> progDesc "Agda package build tool." <> header "Agda Package build tool"))

  let gOpts = optGlobalOpts opts

  cwd <- liftIO getCurrentDirectory
  case optCommand opts of
    BuildPackage tgs -> do
      withSinglePackage cwd gOpts $
        buildSinglePackage tgs
    InstallPackage tgs -> do
      withSinglePackage cwd gOpts $
        installSinglePackage tgs
    InitPackageDb f ->
      initPackageDB f
