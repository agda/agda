import Control.Monad.Except
import Control.Monad.IO.Class
import Data.HashMap.Strict
import Data.Word
import System.FilePath

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Serialise
import Agda.Utils.FileName
import Agda.Utils.Hash
import Agda.Utils.Lens
import Agda.Syntax.Common.Pretty

-- Find out how often the given module ID occurs in names in the given module.
countModID :: String -> ModuleNameHash -> IO (Either TCErr Int)
countModID modName modID = runTCMTop $ do
  setCommandLineOptions $ defaultOptions

  sourcePath <- liftIO $ absolute $ "Issue4835" </> modName <.> "agda"
  interPath <- toIFile $ SourceFile sourcePath
  mInter <- decodeFile $ filePath interPath

  case mInter of
    Nothing -> throwError $ stringTCErr "failed to load interface file"
    Just inter -> do
      let defs = iSignature inter ^. sigDefinitions
      let names = concatMap A.qnameToList0 $ keys defs
      let modIDs = [modID' | NameId _ modID' <- fmap A.nameId names, modID' == modID]
      return $ length modIDs

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
