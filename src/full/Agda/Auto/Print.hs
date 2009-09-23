module Agda.Auto.Print where

import Data.IORef
import Char

import Agda.Auto.NarrowingSearch
import Agda.Auto.Syntax

printExp :: [MId] -> MExp o -> IO String
printExp = pexp 0

pexp :: Int -> [MId] -> MExp o -> IO String
pexp p ctx e = case e of
 Meta m -> do
  bind <- readIORef $ mbind m
  case bind of
   Nothing -> return "?"
   Just e -> pexp p ctx (NotM e)
 NotM e -> case e of  
  App elr args -> do
   let p' = case args of {NotM ALNil -> 4; _ -> 3}
   elr' <- pelr ctx elr
   args' <- pargs ctx args
   par p p' $ elr' ++ args'
  Lam _ (Abs id b) -> do
   b' <- pexp 1 (id : ctx) b
   par p 1 $ "\\" ++ pid ctx id ++ " -> " ++ b'
  Fun _ it ot -> do
   it' <- pexp 3 ctx it
   ot' <- pexp 2 ctx ot
   par p 2 $ it' ++ " -> " ++ ot'
  Pi _ _ it (Abs id ot) -> do
   it' <- pexp 1 ctx it
   ot' <- pexp 2 (id : ctx) ot
   par p 2 $ "[" ++ pid ctx id ++ ":" ++ it' ++ "] -> " ++ ot'
  Sort (SortLevel 0) -> par p 4 "*"
  Sort (SortLevel n) -> par p 4 $ "*" ++ show n
  Sort Type -> par p 4 "Type"

pid :: [MId] -> MId -> String
pid _ (Id s) = printId s
pid ctx NoId = "\"#" ++ show (length ctx) ++ "\""

par :: Monad m => Int -> Int -> String -> m String
par n1 n2 s | n1 > n2 = return $ "(" ++ s ++ ")"
par _ _ s = return s

pelr :: [MId] -> Elr o -> IO String
pelr ctx elr = case elr of
 Var v ->
  if v >= length ctx then
   return $ "@" ++ show (v - length ctx)
  else
   case ctx !! v of
    Id v -> return $ printId v
    NoId -> return $ "\"#" ++ show (length ctx - v - 1) ++ "\""
 Const c -> do
  c <- readIORef c
  return $ printId (cdname c)

pargs :: [MId] -> MArgList o -> IO String
pargs ctx args = case args of
 Meta m -> do
  bind <- readIORef $ mbind m
  case bind of
   Nothing -> return "[?]"
   Just args -> pargs ctx (NotM args)
 NotM args -> case args of
  ALNil -> return ""
  ALCons _ arg args -> do
   arg' <- pexp 4 ctx arg
   args' <- pargs ctx args
   return $ " " ++ arg' ++ args'
  ALConPar args -> do
   args' <- pargs ctx args
   return $ " " ++ "$" ++ args'

-- -----------------------------------

printConst :: ConstRef o -> IO String
printConst c = do
 cdef <- readIORef c
 typs <- printExp [] (cdtype cdef)
 case cdcont cdef of
  Def narg cls -> do
   clss <- mapM printClause cls
   return $ printId (cdname cdef) ++ " : " ++ typs ++ " {\n" ++ concatMap (\x -> x ++ "\n") clss ++ "};\n"
  Datatype cons -> do
   cons' <- mapM (\c -> do
             cdef <- readIORef c
             typs <- printExp [] (cdtype cdef)
             return $ " " ++ printId (cdname cdef) ++ " : " ++ typs ++ ";\n"
            ) cons
   return $ "data " ++ printId (cdname cdef) ++ " : " ++ typs ++ " {\n" ++ concat cons' ++ "};\n"
  Constructor -> return ""
  Postulate ->
   return $ "postulate " ++ printId (cdname cdef) ++ " : " ++ typs ++ ";\n"

printClause :: Clause o -> IO String
printClause (pats, e) = do
 (nv, patss) <- printPats 0 pats
 es <- printExp (replicate nv NoId) e
 return $ patss ++ " = " ++ es ++ ";"

printPats :: Nat -> [Pat o] -> IO (Nat, String)
printPats nv [] = return (nv, "")
printPats nv (p:ps) = do
 (nv', p') <- printPat nv p
 (nv'', ps') <- printPats nv' ps
 return (nv'', " " ++ p' ++ ps')

printPat :: Nat -> Pat o -> IO (Nat, String)
printPat nv (PatConApp c pats) = do
 cd <- readIORef c
 (nv', patss) <- printPats nv pats
 return (nv', "(" ++ printId (cdname cd) ++ patss ++ ")")
printPat nv PatVar = return (nv + 1, printId $ "#" ++ show nv)
printPat nv PatExp = return (nv, ".*")

-- -------------------------------

printId :: String -> String
printId "" = "!!empty string id!!"
printId s@(c : cs) =
 if (isAlpha c || (c == '_')) && all (\c -> isAlpha c || isDigit c || (c == '_') || (c == '\'')) cs then
  s
 else
  "\"" ++ s ++ "\""

