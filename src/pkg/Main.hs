module Main where

-- Standard Library Imports
import           Control.Applicative
import qualified Data.ByteString.Char8
  as BS
import           System.Console.GetOpt
import           System.Environment

-- External Library Imports
import qualified Agda.Packaging.Config
  as Agda
import qualified Agda.Packaging.Database
  as Agda
import qualified Agda.Packaging.Monad
  as Agda

-- Local Imports
import Interface.Command
import Interface.Exit
import Interface.Options
import Interface.Usage
import Interface.Version

-------------------------------------------------------------------------------

main :: IO ()
main = do
  progName  <- getProgName
  givenArgs <- getArgs
  case getOpt Permute allOpts givenArgs of
    -- if --help was given
    (givenOpts, _givenCmds, []) | OptHelp    `elem` givenOpts ->
      bye $ usageInfo (BS.unpack (usageHeader (BS.pack progName))) allOpts

    -- if --version was given
    (givenOpts, _givenCmds, []) | OptVersion `elem` givenOpts ->
      bye $ versionString

    -- if a command was given
    (givenOpts,  givenCmds, [])                               ->
      processCmds progName givenOpts givenCmds

    -- anything else
    (_givenOpts, _givenCmds, errors)                          ->
      die $  concat errors
          ++ "See --help for usage info."

  where
    -- Process the commands (not the args prefixed with '--'),
    -- determine the package database stack, and initialize the
    -- environment for the AgdaPkg monad
    processCmds :: String -> [Opt] -> [Cmd] -> IO ()
    processCmds progName givenOpts givenCmds = do
      pkgDBPathStack <-
        -- if only --global was given
        if        (OptDBGlobal `elem` givenOpts
          &&  not (OptDBUser   `elem` givenOpts))
        then
          pure (:)
            <*> Agda.getPkgDBPathGlobal
            <*> pure []
        else
          -- if only --user was given
          if        (OptDBGlobal `elem` givenOpts
            &&  not (OptDBUser   `elem` givenOpts))
          then
            pure (:)
              <*> Agda.getPkgDBPathUser
              <*> pure []
          else
            -- if neither or both of --global and --user were given
            pure (\ db1 db2 -> db1 : db2 : [])
              <*> Agda.getPkgDBPathGlobal
              <*> Agda.getPkgDBPathUser
      -- load the package databases from the path stack
      pkgDBStack <- Agda.getPkgDBs pkgDBPathStack
      let initConfig = Agda.AgdaPkgConfig
            { Agda.configOpts       = givenOpts
            , Agda.configOrigBroken = [] -- FIXME
            , Agda.configPkgDBStack = pkgDBStack
            , Agda.configProgName   = progName }
      -- process the commands
      -- FIXME: this runReaderT should be hidden by the API
      Agda.runReaderT (Agda.runAgdaPkg dispatch) initConfig

      where
        -- Take some action according to the commands (not the args
        -- prefixed with '--').  The interface follows the
        -- specification outlined in the 'Haskell Cabal' document,
        -- with deviations to conform to essential parts of the
        -- current GHC interface.
        dispatch :: Agda.AgdaPkg Opt ()
        dispatch =
          case givenCmds of
            []                                 ->
              -- FIXME: this liftIO should be hidden by API
              Agda.liftIO $ die $  "no command specified\n"
                                ++ "See --help for usage info."

            ["describe"  , _pkgId]             ->
              error "describe"

            ["expose"    , pkgId]              ->
              exposePkg pkgId

            ["dump"]                           ->
              dumpPkgs

            ["field"     , _pkgId, _fields]    ->
              error "field"

            ["hide"      , pkgId]              ->
              hidePkg pkgId

            ["list"]                           ->
              listPkgs

            ["register"  , fileName]           ->
              registerPkg fileName

            ["unregister", _pkgId]             ->
              error "unregister"

            ["update"    , fileName]           ->
              -- FIXME
              registerPkg fileName

            cmd:_                              ->
              -- FIXME: This liftIO should be hidden by API
              Agda.liftIO $ die $  "unrecognized command "
                                ++ "`" ++ cmd ++ "'\n"
                                ++ "See --help for usage info."
