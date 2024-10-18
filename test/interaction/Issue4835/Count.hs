{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}

import Control.Monad.IO.Class          ( liftIO )
import qualified Data.HashMap.Strict as HM
import System.FilePath                 ( (</>), (<.>) )

import Agda.Interaction.FindFile       ( toIFile )
import Agda.Interaction.Options        ( defaultOptions )
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common              ( ModuleNameHash(..), pattern NameId )
import Agda.Syntax.Common.Pretty       ( prettyShow )
import Agda.TypeChecking.Monad.Base    ( TCErr, iSignature, internalError, runTCMTop, sigDefinitions, srcFromPath )
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions )
import Agda.TypeChecking.Serialise     ( decodeFile )
import Agda.Utils.FileName             ( absolute, filePath )
import Agda.Utils.Hash                 ( hashString )
import Agda.Utils.Lens                 ( (^.) )

-- Find out how often the given module ID occurs in names in the given module.
countModID :: String -> ModuleNameHash -> IO (Either TCErr Int)
countModID modName modID = runTCMTop do
  setCommandLineOptions defaultOptions

  sourcePath <- liftIO $ absolute $ "Issue4835" </> modName <.> "agda"
  srcFile    <- srcFromPath sourcePath
  interPath  <- toIFile srcFile
  mInter     <- decodeFile $ filePath interPath

  case mInter of
    Nothing -> internalError "failed to load interface file"
    Just inter -> do
      let defs = iSignature inter ^. sigDefinitions
      let names = concatMap A.qnameToList0 $ HM.keys defs
      let modIDs = [modID' | NameId _ modID' <- fmap A.nameId names, modID' == modID]
      return $ length modIDs

main :: IO ()
main = do
  -- Derive the module ID of ModA.
  let qName = (C.Qual . C.simpleName) "Issue4835" $ (C.QName . C.simpleName) "ModA"
  let modID = ModuleNameHash $ hashString $ prettyShow qName

  -- Count occurrences of the module ID in ModA and ModB, respectively.
  countA <- countModID "ModA" modID
  countB <- countModID "ModB" modID

  -- Expect more than zero occurrences in ModA as a sanity check.
  putStrLn $ case countA of
    Left err -> "no countA: " ++ show err
    Right n -> if n /= 0 then "OK" else "invalid countA: " ++ show n

  -- Expect no occurrences in ModB. This is the actual regression test.
  putStrLn $ case countB of
    Left err -> "no countB: " ++ show err
    Right n -> if n == 0 then "OK" else "invalid countB: " ++ show n
