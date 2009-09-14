module Agda.Auto.Print where

import Data.IORef

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
   let id' = case id of
              Id s -> s
              NoId -> "#" ++ show (length ctx)
   par p 1 $ "\\" ++ id' ++ " -> " ++ b'
  Fun _ it ot -> do
   it' <- pexp 3 ctx it
   ot' <- pexp 2 ctx ot
   par p 2 $ it' ++ " -> " ++ ot'
  Pi _ it (Abs id ot) -> do
   it' <- pexp 1 ctx it
   ot' <- pexp 2 (id : ctx) ot
   let id' = case id of
              Id s -> s
              NoId -> "#" ++ show (length ctx)
   par p 2 $ "[" ++ id' ++ ":" ++ it' ++ "] -> " ++ ot'
  Sort (SortLevel 0) -> par p 4 "*"
  Sort (SortLevel n) -> par p 4 $ "*" ++ show n
  Sort Type -> par p 4 "Type"

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
    Id v -> return v
    NoId -> return $ "#" ++ show (length ctx - v - 1)
 Const c -> do
  c <- readIORef c
  return $ cdname c

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
   return $ " " ++ "_" ++ args'

-- ---------------------------------------------------

phnargs :: [MId] -> HNArgList o -> IO String
phnargs ctx args = case args of
  HNALNil -> return ""
  HNALCons arg args -> do
   arg' <- pcexp ctx arg
   args' <- pcargs ctx args
   return $ " " ++ arg' ++ args'
  HNALConPar args -> do
   args' <- pcargs ctx args
   return $ " " ++ "_" ++ args'

pcexp :: [MId] -> CExp o -> IO String
pcexp ctx (Clos acts e) = pexp 4 ctx e  -- TODO: print closure

pcargs :: [MId] -> CArgList o -> IO String
pcargs ctx args = case args of
  CALNil -> return ""
  CALConcat (Clos acts arg) args -> do  -- TODO: print closure
   arg' <- pargs ctx arg
   args' <- pcargs ctx args
   return $ arg' ++ args'

printConst :: ConstRef o -> IO String
printConst c = do
 cdef <- readIORef c
 typs <- printExp [] (cdtype cdef)
 case cdcont cdef of
  Def narg cls -> do
   clss <- mapM printClause cls
   return $ cdname cdef ++ " : " ++ typs ++ " {\n" ++ concatMap (\x -> " " ++ x ++ "\n") clss ++ "}\n"
  Datatype cons ->
   return $ "data " ++ cdname cdef ++ " : " ++ typs ++ "\nTODO: dump constructors too\n"  -- TODO
  Constructor ->
   return $ "constructor " ++ cdname cdef ++ " : " ++ typs ++ "\nTODO: do not dump constructor\n"  -- TODO
  Postulate ->
   return $ "postulate " ++ cdname cdef ++ " : " ++ typs ++ "\n"

printClause :: Clause o -> IO String
printClause (pats, e) = do
 patss <- mapM printPat pats
 es <- printExp [] e
 return $ concatMap (++ " ") patss ++ "= " ++ es

printPat :: Pat o -> IO String
printPat (PatConApp c pats) = do
 cd <- readIORef c
 patss <- mapM printPat pats
 return $ "(" ++ cdname cd ++ concatMap (" " ++) patss ++ ")"
printPat PatVar = return "_"
printPat PatExp = return "."


