{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.EmacsInterface.EmacsAgda where

import Prelude hiding (print, putStr, putStrLn)
import Utils.IO

import Control.Monad.Error
import Control.Monad.Reader
import Data.Char
import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Maybe

import Interaction.BasicOps as BasicOps
import Interaction.Monad

import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Parser
import Syntax.Position
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete

import Text.PrettyPrint

import TypeChecker
import TypeChecking.Conversion
import TypeChecking.Constraints
import TypeChecking.Monad
import TypeChecking.MetaVars
import TypeChecking.Reduce
import TypeChecking.Errors

import Utils.ReadLine
import Utils.Monad
import Utils.Fresh
import Utils.Monad.Undo

#include "../../undefined.h"

--versionCommand :: String
--versionCommand = infoCommand "* Agda version *" (version++"\n\n"++compiled)

-- errorBuffer = "*error*"
-- environmentBuffer = "* Environment *"

constraintBuffer, contextBuffer, goalBuffer, resultBuffer,
  suggestionsBuffer, terminationBuffer, typeBuffer :: String

constraintBuffer  = "* Constraints *"
contextBuffer     = "* Context  *"
goalBuffer        = "* Goals *"
resultBuffer      = "* Result *"
suggestionsBuffer = "* Suggestions *"
terminationBuffer = "* Termination *"
typeBuffer        = "* Type *"
externalBuffer    = "* External Info *"

mkString :: String -> String
mkString s = "\""++ (concatMap replaceSpec s) ++ "\""
    where ss = lines s
          replaceSpec c | c == '\n' = "\\n" 
          replaceSpec c | c == '\"' = '\\':"\""
          replaceSpec c | c == '\\' = '\\':'\\':""
          replaceSpec c | otherwise = [c]
 
                        
inPar :: String -> String
inPar s = " (" ++ s ++ ")"

mkEmacsCommand :: String -> String
mkEmacsCommand s = "--- " ++ s ++ " +++\n"

mkCommand :: String -> String -> String
mkCommand s1 s2 = mkEmacsCommand (inPar (mkString s1 ++ inPar s2))

infoCommand,
  visitCommand  :: String -> String -> String
infoGoalCommand :: String -> String -> String -> String
updateReplaceCommand,
  updateCommand :: String -> String -> String -> String

errorCommand    :: String -> String
newstateCommand :: Int    -> String

errorCommand s                = mkCommand "error" (mkString s)
infoCommand s1 s2             = mkCommand "info" (mkString s1 ++ " " ++ mkString s2)

infoGoalCommand s1 s2 s3      = mkCommand "infogoal" (unwords (List.map mkString [s1,s2,s3]))

suggestGoalCommand s1 s2        = mkCommand "suggest" (mkString s1 ++ " " ++ s2)

newstateCommand n             = mkEmacsCommand (inPar (mkString "tr#" ++ " " ++ show n ))
updateCommand s1 s2 s3        = mkCommand "update" (unwords [s1,s2,s3])
updateReplaceCommand s1 s2 s3 = mkCommand "updateReplace" (unwords [s1,mkString s2,s3])
visitCommand s1 s2            = mkCommand "visit" (mkString s1 ++ s2)

--messageCommand s              = mkEmacsCommand (inPar (mkString "message"++mkString s))
--versionCommand                = mkCommand "version" (mkString version)

mkMetaList :: [InteractionId] -> String
mkMetaList mvs = inPar (unwords (List.map (show . getInteractionNumber) mvs))
      

getInteractionNumber (InteractionId i) = i


outputMeta :: InteractionId -> [InteractionId] -> Bool -> IM()
outputMeta m ms b = liftIO $ putStrLn (updateCommand (show $ getInteractionNumber m) (show b) (mkMetaList ms))


outputMetaReplace :: InteractionId -> String -> [InteractionId] -> IM()
outputMetaReplace m s ms = 
    do  liftIO $ putStrLn (updateReplaceCommand (show $ getInteractionNumber m) s (mkMetaList ms))


outputVisit :: String -> [InteractionId] -> IM ()
outputVisit f mvs = liftIO $ putStrLn (visitCommand f (mkMetaList mvs))


outputState :: IM ()
outputState = do n <- getUndoStateNumber
                 liftIO $ putStrLn (newstateCommand n)


data ExitCode a = Continue | ContinueIn TCEnv | Return a

type Command a = (String, [String] -> IM (ExitCode a))

matchCommand :: String -> [Command a] -> Either [String] ([String] -> IM (ExitCode a))
matchCommand x cmds =
    case List.filter (isPrefixOf x . fst) cmds of
	[(_,m)]	-> Right m
	xs	-> Left $ List.map fst xs

interaction :: String -> [Command a] -> (String -> IM (ExitCode a)) -> IM a
interaction prompt cmds eval = loop
    where
	go (Return x)	    = return x
	go Continue	    = loop
	go (ContinueIn env) = local (const env) loop

	loop =
	    do	ms <- liftIO $ readline prompt
		case fmap words ms of
		    Nothing		  -> return $ error "** EOF **"
		    Just []		  -> loop
		    Just (cmd:args) ->
			do  liftIO $ addHistory (fromJust ms)
			    case matchCommand cmd cmds of
				Right c	-> go =<< c args
				Left []	->
				    do	liftIO $ putStrLn $ "Unknown command '" ++ cmd ++ "'"
					loop
				Left xs	->
				    do	liftIO $ putStrLn $ "More than one command match: " ++ concat (intersperse ", " xs)
					loop
	    `catchError` \e ->
		do  s <- prettyError e
		    liftIO $ putStrLn $ errorCommand s
		    loop

printRange (Range NoPos _) = "Unknown Position " 
printRange (Range s e) = "At: " ++ file ++ line ++ col
	where
	    f	= srcFile s
	    sl	= posLine s
	    sc	= posCol s
	    file
		| List.null f    = ""
		| otherwise = "\"" ++ f ++ "\"" 
	    line = ", line " ++ show sl
	    col = ", column " ++ show sc


removeDQ,removeDQ' :: String -> String
removeDQ ('\"':s) = removeDQ' s -- "
removeDQ s        = s
removeDQ' "\""    = []
removeDQ' (c:cs)  = c:removeDQ' cs
removeDQ' s = error "Impossible"  ---Why doesnt IMPOSSIBLE work here

--removeDQ :: String -> String
--removeDQ s        = List.delete '\"' s


-- | The interaction loop.
emacsModeLoop :: IM () -> IM ()
emacsModeLoop typeCheck =
    do  reload
	interaction "Main> " commands evalTerm
    where
	reload = (setUndo >> typeCheck) -- `catchError`
		    -- \e -> liftIO $ do print e
			--	      putStrLn "Failed."

	commands =
	    [ "quit"	    |>  \_ -> return $ Return ()
	    , "reload"	    |>  \_ -> do reload
					 ContinueIn <$> ask
	    , "showConstraints" |> \args -> continueAfter $ showConstraints args
            , "give"	    |> \args -> continueAfter $ updateActionIM $ giveMeta args
            , "refine"	    |> \args -> continueAfter $ updateActionIM $ refineMeta args
	    , "meta"	    |> \args -> continueAfter $ showMetas args
            , "undo"	    |> \_ -> continueAfter $ mkUndo
            , "printg"      |> \args -> continueAfter $ showMetas args
            , "printGAll"   |> \_ -> continueAfter $ showMetas []
            , "printmc"     |> \args -> continueAfter $ showContext args
            , "LOAD"	    |> \args -> continueAfter $ updateActionIM $ loadFile reload args
	    , "eval"	    |> \args -> continueAfter $ evalIn args
            , "typeOfExpression"      |> \args -> continueAfter $ typeOf args
	    , "wakeup"	    |> \_ -> continueAfter $ retryConstraints
	    ]
	    where
		(|>) = (,)

continueAfter :: IM a -> IM (ExitCode b)
continueAfter m = 
    do  m 
        return Continue

updateActionIM :: IM () -> IM ()
updateActionIM action = do 
        outputState
        action
        showMetas []
        showConstraints []

loadFile :: IM () -> [String] -> IM ()
loadFile reload [file,buffer] =
    do	let file' = removeDQ file
            buffer' = removeDQ buffer
        setInputFile file' --ToDo: Should be buffer' but gives wrong range 
        mis <- getInteractionPoints
	setUndo
        reload
        mis' <- getInteractionPoints
        outputVisit file' ((List.\\) mis' mis) 
loadFile _ _ = liftIO $ putStrLn ":load file"

showConstraints :: [String] -> IM ()
showConstraints [c] =
    do	i  <- readM c
	cc <- abstractToConcrete_ <$>  BasicOps.getConstraint (CId i)
	liftIO $ putStrLn $ infoCommand constraintBuffer $ show cc
showConstraints [] =
    do	cs <- BasicOps.getConstraints
        let concrete = List.map abstractToConcrete_ cs
	liftIO $ putStrLn $ infoCommand constraintBuffer $ unlines $ List.map show concrete
showConstraints _ = liftIO $ putStrLn ":constraints [cid]"

	
showMetas :: [String] -> IM ()
showMetas [flag,f,l,c,m] = 
    do	i <- readM m
        let toNorm = if flag == "toiota" then Normalised else Instantiated
	outForm <- typeOfMeta toNorm (InteractionId i)
        let concrete = abstractToConcrete_ outForm 
	liftIO $ putStrLn $ infoCommand typeBuffer $ show concrete
showMetas [] = 
    do  (interactionMetas,implicitMetas) <- typeOfMetas Instantiated
        let concreteInteraction = List.map abstractToConcrete_ interactionMetas
            concreteImplicit =  List.map abstractToConcrete_ implicitMetas
            output = unlines $ List.map show concreteInteraction ++
                                ["----Implicit Metavariables---"] ++
                                List.map show concreteImplicit
        liftIO $ putStrLn $ infoCommand goalBuffer output
showMetas _ = liftIO $ putStrLn $ ":hidden [metaid]"

metaParseExpr ::  InteractionId -> String -> IM A.Expr
metaParseExpr ii s = 
    do	let s' = List.map (\c -> if c == '~' then '\n' else c) s --Emacsinterface replaces white space with ~
        m <- lookupInteractionId ii
        scope <- getMetaScope <$> lookupMeta m
        r <- getRange <$> lookupMeta m
	e <- liftIO $ parsePosString exprParser (rStart r) s'
	concreteToAbstract scope e

actOnMeta :: (InteractionId -> A.Expr -> IM a) -> [String] -> IM a
actOnMeta f (is:es) = 
     do  i <- readM is
         let ii = InteractionId i 
         e <- metaParseExpr ii (unwords es)
         f ii e
actOnMeta _ _ = __IMPOSSIBLE__


giveMeta :: [String] -> IM ()
giveMeta s | length s >= 5 = 
    flip actOnMeta (drop 3 s) $ \ii e -> do
	(_,iis) <- give ii Nothing e
        outputMeta ii iis False
        return ()
giveMeta _ = liftIO $ putStrLn $ ": give" ++ " metaid expr"



refineMeta :: [String] -> IM ()
refineMeta s | length s >= 5 = 
    flip actOnMeta (drop 3 s) $ \ii e -> do
          scope <- getInteractionScope ii
          (e,iis) <- refine ii Nothing e 
          debug (show e)
          let concrete = abstractToConcreteCtx (contextPrecedence scope) e
          outputMetaReplace ii (show concrete) iis
refineMeta _ = liftIO $ putStrLn $ ": refine" ++ " metaid expr"



retryConstraints :: IM ()
retryConstraints = liftTCM wakeupConstraints


evalIn :: [String] -> TCM ()
evalIn (f:l:c:ss) =
     flip actOnMeta ss $ \ii -> \e -> 
         do  v <- evalInMeta ii e 
             liftIO $ putStrLn $ infoCommand typeBuffer $ show $ abstractToConcrete_ v
evalIn _ = liftIO $ putStrLn ":eval metaid expr"

showContext :: [String] -> TCM ()
showContext [f,l,c,m] =
    do  ii <- InteractionId <$> readM m
        bindings <- contextOfMeta ii
        let concrete = List.map abstractToConcrete_ bindings
        liftIO $ putStrLn $ infoCommand typeBuffer $ unlines $ List.map show concrete
showContext _ = liftIO $ putStrLn ":printmc metaid"

parseExpr :: String -> TCM A.Expr
parseExpr s = concreteToAbstract_ =<< liftIO (parse exprParser s)

evalTerm :: String -> TCM (ExitCode a)
evalTerm s =
    do	e <- parseExpr s
        v <- evalInCurrent e
	liftIO $ putStrLn $ show $ abstractToConcrete_ v
	return Continue

typeOf :: [String] -> IM ()
typeOf (flag:f:l:c:m:ss) = 
    do  let toNorm = if flag == "toiota" then Normalised else Instantiated
        flip actOnMeta ss $ \ii e -> do 
            v <- typeInMeta ii toNorm e 
	    liftIO $ putStrLn $ infoCommand typeBuffer $ show $ abstractToConcrete_ v
typeOf _ = __IMPOSSIBLE__


