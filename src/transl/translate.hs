{- 
#include "config.h" 
-}
-- | Top level Agda module for using the emacs front-end
module Main(main) where
import Monads
--import Parse_com       (Command(..), getCommand, isQuit)
--import Commands  -- semantic actions for the most commands
import InteractionMonad(IM, runIM, undoToIM, liftIOIM, liftEIM,
                        accessPCMIM, liftPCMIM, readPCMIM, nrOfState,
                        handle, raise, when,Error(..),outputIM,flushOutput)
import ProofMonad      (PCM, toggleTraceFl,putStrTable,getStrTable)
import ProofState      (initState)
import LoadPrelude     (loadPrelude)
import BasicOps        (includePrelude)
--import MetaVars        (MetaVar)
import Position        (Position(Position), noPosition)
import Error           (eMsg, EMsg, ErrMsg(ENoFile), prEMsg)
--import Version         (version, compiled)
--import Plugin          (PluginCall(..))
--import PluginTable     (pluginAction)
#ifdef DYNAMIC_PLUGINS
--import DynamicPlugin
#endif
import IO              (Handle, hGetLine, stdin, hSetBuffering, 
                        stdout, BufferMode(NoBuffering))
import System.Environment(getArgs)
import System.IO.Error(IOError,catch,isEOFError)
--import Typechecking -- Only here since we have a boot file for it
--import BasicEngineOps -- Only here since we have a boot file for it
import External -- Only to import boot file
--import Imitate -- Only to import boot file
--import CITrans
import FString(StrTable)
import TransNewSyntax
--import List(intersperse)
--import Utilities
--import CITrans()
import PPrint(PDetail (..),ppDebug,ppReadable)
--import AgdaTrace
--import Monads(traceM)
import Lex (lexStart,lx)
import CParser(CParser,pExpr,finalP,pLetDefs,pOper,pBindIds)

mkError :: EMsg -> String
mkError e = prEMsg e

tryReadFile :: String -> IM (String)
tryReadFile f = liftIOIM (readFile f)
                  `handle` (\_ -> raise $ eMsg noPosition (ENoFile f))

pParse :: CParser a -> Position -> String -> PCM a
pParse p (Position s l c) inp = do
     st <- getStrTable
     let ts = lx True s l c st inp
     (a,st) <- liftESTM $ finalP p ts 
     putStrTable st
     return a 


loop :: String -> IM String
loop  b = do contents <- tryReadFile b
             ds <- liftPCMIM$ pParse pLetDefs (Position b 1 0) contents    
             return (unlines$ map ppReadable $ translateCLetDefs ds)
        `handle` (\ e -> (liftIOIM (putStrLn (mkError e))) >> return "")

inits :: [String] -> IM ()
inits fs = do s <- mapM loop fs
              liftIOIM $ putStr $ unlines s
              return ()


main :: IO () 
main  = do hSetBuffering stdout NoBuffering
           fs <- getArgs
           runIM (inits fs)  initState
           return ()
