module Agda.Termination.Dummy where

--import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.TypeChecking.Monad

import Control.Monad.Trans
import Data.Map as Map
import Data.List as List

checkTermination :: TCM ()
checkTermination = do
			liftIO $ putStrLn "Dummy termination checker"
			sig <- getSignature
			processSig sig

processSig :: Signature -> TCM()
processSig sig = mapM_ processDefinitions defss where
	defss {- :: [Definitions] -} = List.map mdefDefs mdefs
	mdefs {- :: [ModuleDef] -} = List.map snd $ Map.assocs sig
	-- names ds = Map.keys ds

processDefinitions :: Definitions -> TCM()
processDefinitions defs = mapM_ processDef $ List.map simpleDef $ Map.assocs defs

simpleDef :: (Name, Definition) -> (Name, Defn)
simpleDef (n, d) = (n,theDef d)
 
processDef :: (Name, Defn) -> TCM()
processDef (name, (Function cs isa)) =  processFun name cs
processDef _ = return ()


processFun :: Name -> [Clause] -> TCM()
processFun name cs = mapM_ (processClause name) cs

processClause name c@(Clause args body) = liftIO $ 
     do
	putStr (show name ++ " " ++ show args)
	if isRecursiveClause name c then putStrLn " REC"
        			    else putStrLn " nonrec"

isRecursiveClause :: Name -> Clause -> Bool
isRecursiveClause name c@(Clause args body) = isRecursiveBody name body

isRecursiveBody :: Name -> ClauseBody -> Bool
isRecursiveBody name (Body t) = isRecursiveTerm name t
isRecursiveBody name (Bind abs) = isRecursiveBody name (absBody abs)
isRecursiveBody name (NoBind  cb) = isRecursiveBody name cb
isRecursiveBody name (NoBody) = False

isRecursiveTerm name (Var n []) = False
isRecursiveTerm name (Var n args) = isRecursiveArgs name args
isRecursiveTerm name (Lam _ abs) = isRecursiveTerm name (absBody abs)
isRecursiveTerm name (Def qn args) = cmpQn qn name || isRecursiveArgs name args
isRecursiveTerm name (Con _ args) = isRecursiveArgs name args
isRecursiveTerm _ _ = False
isRecursiveArgs name as = any (isRecursiveTerm name) $ List.map unArg as

cmpQn (QName (Name id _ ) _ _) (Name id' _) = id == id'
