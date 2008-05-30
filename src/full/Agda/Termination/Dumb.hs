module Agda.Termination.Dumb where

--import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Position(noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract (concreteToAbstract_, OldName(..))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors

import Agda.Termination.Utils

import Agda.Utils.Pretty
import Agda.Utils.Monad

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List as List
import Text.PrettyPrint

import Agda.Termination.RCall

checkTermination :: TCM ()
checkTermination = do
			liftIO $ putStrLn "Termination check"
			sig <- getSignature
			processSig sig

processSig :: Signature -> TCM()
processSig sig = processDefinitions $ sigDefinitions sig

{-
processSig sig = mapMM processDefinitions defss where
	defss {- :: [Definitions] -} = List.map mdefDefs mdefs
	mdefs {- :: [ModuleDef] -} = List.map snd $ Map.assocs sig
	-- names ds = Map.keys ds
-}

-- processModule :: ModuleDef -> TCM ()
-- processModule m = withCurrentModule mname $ processDefinitions defss where
--     mname = mdefName m
--     defss = mdefDefs m

processDefinitions :: Map QName Definition -> TCM()
processDefinitions defs = mapMM processDef $ List.map simpleDef $ Map.assocs defs

simpleDef :: (QName, Definition) -> (QName, Defn)
simpleDef (n, d) = (n, theDef d)
 
processDef :: (QName, Defn) -> TCM()
processDef (name, (Function cs _ _ isa)) =  processFun name cs
processDef _ = return ()


processFun :: QName -> [Clause] -> TCM()
processFun name cs = processFun' name 1 cs

processFun' :: QName -> Nat ->[Clause] -> TCM()
processFun' name num [] = return ()
processFun' name num (c:cs) = processClause name num c 
                              >> processFun' name (num+1) cs

processClause :: QName -> Nat -> Clause -> TCM()
processClause name num c@(Clause _ _ args body) = 
     do
        let targs = exPatTop args
        case callsClause name num c of
          [] -> return ()
          cs -> do
		  d <- prettyTCM targs
		  tcmsg $ show name ++ " " ++ show d
		  checkCalls targs cs

findDef :: String -> TCM (Maybe QName)
findDef s =  (findDef' $ C.Name noRange [C.Id noRange s]) 
             `catchError` (\e-> return Nothing)

findDef' :: C.Name -> TCM (Maybe QName)
findDef' s = do
  name <- concreteToAbstract_ (OldName s) 
  return $ Just name 

printCalls :: [RCall] -> TCM()
checkCalls :: Args -> [RCall] -> TCM()

printCalls cs = do 
		  liftIO $ putStr " REC " 
	          -- str <- show <$> prettyTCM cs
                  tcmsg . show =<< prettyTCM cs


checkCalls targs cs = mapMM (checkCall targs) cs


-- For recursive call  
--   f : A -> B
--   f(p) = ... f(e) ...
-- we need:
-- f-measure : Measure
-- f-measure = mu {M}
checkCall :: Args -> RCall -> TCM()
checkCall [targ] (RCall fun i j [arg]) = do
  -- tcmsg $ "Looking for " ++ hintName
  mhint <- findDef hintName
  pArg <- prettyTCM arg
  pTArg <- prettyTCM targ
  let strLess = show pArg ++ " < " ++ show pTArg
  case mhint of
    Just name -> foundHint name
    Nothing ->       
     tcmsg $ if strictSubterm (unArg arg) (unArg targ) 
          then msgGood strLess
          else msgBad  strLess
  where
    msgGood strLess = callid ++ " OK: " ++ strLess
    msgBad  strLess =  callid ++ " You need to prove " ++ strLess 
    callid = show fun ++ "-" ++ show i ++ "-" ++ show j
    hintName = callid++"-hint"
    foundHint qname = do
       hintType <- typeOfConst qname
       hintTypeDoc <- prettyTCM hintType
       tcmsg $ "Found hint for " ++ callid 
       tcmsg $ show hintTypeDoc

checkCall ((Arg Hidden _):tas) (RCall fun i j (a:as)) = 
    checkCall tas (RCall fun i j as)
checkCall _ _ = tcmsg "Sorry, don't know how to handle that"

-- cmpArgs takes two lists of args 
-- and returns a list of good pairs and a list of bad pairs
cmpArgs :: Args -> Args -> ([(Term,Term)],[(Term,Term)])
cmpArgs [] [] = ([],[])
cmpArgs (a:as) (b:bs) = (goodhd++goodtl,badhd++badtl) where
        (ta,tb) = (unArg a, unArg b)
	(goodhd,badhd) = if strictSubterm ta tb
		         then ([(ta,tb)],[])
			 else ([],[(ta,tb)])
        (goodtl,badtl) = cmpArgs as bs
cmpArgs _ _ = ([],[])
        
tcmsg :: String -> TCM()
tcmsg = liftIO . putStrLn 

------------------------------------------------------------
-- Gathering recursive calls
------------------------------------------------------------		  

callsClause, callsClause' :: QName -> Nat -> Clause -> [RCall]
callsClause name num c = fixCallNums $ callsClause' name num c
callsClause' name num c@(Clause _ _ args body) = callsBody name num body

fixCallNums :: [RCall] -> [RCall]
fixCallNums cs = zipWith fixCallNum cs [1..]

fixCallNum :: RCall -> Int -> RCall
fixCallNum (RCall fun i _ args) j = RCall fun i j args

callsBody :: QName -> Nat -> ClauseBody -> [RCall]
callsBody name num (Body t) = callsTerm name num t
callsBody name num (Bind abs) = callsBody name num (absBody abs)
callsBody name num (NoBind  cb) = callsBody name num cb
callsBody name num (NoBody) = []

callsTerm :: QName -> Nat -> Term -> [RCall]
callsTerm name num (Var n []) = []
callsTerm name num (Var n args) = callsArgs name num args
callsTerm name num (Lam _ abs) = callsTerm name num (absBody abs)
callsTerm name num def@(Def qn args) = callsDef name num def 
                                       ++ callsArgs name num args
callsTerm name num (Con _ args) = callsArgs name num args
callsTerm name num  _ = []

callsArgs :: QName -> Nat -> Args -> [RCall]
callsArgs name num as = concat  $ List.map ((callsTerm name num).unArg) as

--cmpQn (QName (Name id _) _ _) (Name id' _) = id == id'
callsDef :: QName -> Nat -> Term -> [RCall]
callsDef name num (Def name'  args)
  | name == name' = [RCall name (fromIntegral num) 0 args]
  | otherwise	  = []
callsDef name num _ = []


------------------------------------------------------------
--   Patterns to Terms
------------------------------------------------------------

type NatState a = State Nat a

exPatTop :: [Arg Pattern] -> [Arg Term]
exPatTop args = args' where
	(args',n) = runState (exPatArgs args) 0

exPatArgs :: [Arg Pattern] -> State Nat [Arg Term]
exPatArgs [] = return []
exPatArgs (x:xs)  = do 
	arg <- exPatArg x
	args <- exPatArgs xs
	return (arg:args)

exPatArg :: Arg Pattern -> State Nat (Arg Term)
exPatArg  (Arg hid pat) = exPat pat >>= return . (Arg hid )

exPat :: Pattern -> State Nat Term
exPat (VarP _) = do
   n <- get 
   put (n+1)
   return $ Var n []
exPat (ConP name as) = do
	args <- exPatArgs as
        return $ Con name args
exPat _ = error "exPat error"

------------------------------------------------------------
-- Subterm checking
------------------------------------------------------------

(===) :: Term -> Term -> Bool
Var n1 as1 === Var n2 as2 = n1 == n2 && allArgsEqual as1 as2
_	   === _	  = False

allArgsEqual :: Args -> Args -> Bool
allArgsEqual [] [] = True
allArgsEqual (a:as) (b:bs) = unArg a === unArg b && allArgsEqual as bs
allArgsEqual _ _ = False

subterm, strictSubterm :: Term -> Term -> Bool

subterm t1 t2 = (t1 === t2) || strictSubterm t1 t2

strictSubterm t (Con _ as) = subtermOfAnyArg t as
  -- any $ map ((subterm t) . unArg) as
			
strictSubterm _ _ = False

subtermOfAnyArg :: Term -> Args -> Bool
subtermOfAnyArg t [] = False
subtermOfAnyArg t (a:as) = subterm t (unArg a) || subtermOfAnyArg t as
