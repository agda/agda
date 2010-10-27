module ISynEnv  where

import Data.List
import Id(UId,isDummyUId,SymTab)
import Position(Position,noPosition)
import ISynType
--import CITrans(CITrans,initCIT_CST)

type MValue = Exp   -- A value where the meta variables are evaluated


data Judgement a  = IsType a
                  | a :! Value
                  --deriving Show

type Context = [(UId,Exp)]    -- Context is in reverse order of Tel

type TCEnv = (Context,Environment)

emptyEnv :: Environment
emptyEnv = E ([],[])

update :: Env ->  UId -> Value -> Env
update env x v = (x,v):env

updateEnv :: Environment -> UId -> Value -> Environment
updateEnv (E (env,sigma)) x v = E (update env x v,sigma)

updateEnvMany :: Environment -> [(UId,Value)] -> Environment
updateEnvMany = foldl (\env -> uncurry (updateEnv env))

updatesEnv :: Environment -> [(Bool,UId)] -> [(Bool,Value)] -> (Environment,[(Bool,UId)],[(Bool,Value)])
updatesEnv env ((_,x):xs) ((_,v):vs) = updatesEnv (updateEnv env x v) xs vs
updatesEnv env xs vs = (env,xs,vs)

updatesEnv' :: Environment -> [(Bool,UId)] -> [Value] -> (Environment,[(Bool,UId)],[Value])
updatesEnv' env ((_,x):xs) (v:vs) = updatesEnv' (updateEnv env x v) xs vs
updatesEnv' env xs vs = (env,xs,vs)

addIdEnv :: Environment -> [UId] -> [UId] -> Environment
addIdEnv env [] _ = env
addIdEnv env (x:xs) (x':xs') = addIdEnv (updateEnv env x (EVar x' Nothing)) xs xs'
addIdEnv _   _       _       = error "addIdEnv: "

addHIdEnv :: Environment -> [(Bool,UId)] -> [(Bool,UId)] -> Environment
addHIdEnv env [] _ = env
addHIdEnv env ((_,x):xs) ((_,x'):xs') = addHIdEnv (updateEnv env x (EVar x' Nothing)) xs xs'
addHIdEnv _   _       _       = error "addHIdEnv: "

lookupE :: Env -> UId -> Maybe Value
-- Use lookupEnv for looking up the Value of a variable
lookupE env x = lookup x env


retrieveE :: Environment -> [UId] -> Environment
retrieveE env xs = env

--retrieveE (E (_,sigma)) []  =  E ([],sigma)
--retrieveE env (x:xs) = let env' = retrieveE env xs
--                           v = lookupE x env
--                       in updateEnv env' x v

domEnv :: Environment -> [UId]
domEnv (E (env,_)) = nub $ map fst env

accessible :: Environment -> [UId]
accessible (E (_,sigma)) = sigma

addAccessible :: Environment -> UId -> Environment
addAccessible (E (env,sigma)) c = E (env,(c:sigma))

resetAccessible (E (env,_)) = E (env,[])

emptyC :: Context
emptyC = []

addC :: Context -> UId -> Exp  -> Context
addC gamma x e = (x,e):gamma

addDeclC  :: Context -> Decl -> Context
addDeclC gamma (xs,a) = foldr (\(_,x) -> \gamma -> (x,a):gamma) gamma xs


domC :: Context -> [UId]
domC gamma = map fst gamma

lookupC :: UId -> Context -> Maybe Exp
lookupC x gamma = lookup x gamma

appendCT :: Context -> Tel -> Context
appendCT gamma [] = gamma
appendCT gamma (d:tel) =  appendCT (addDeclC gamma d) tel

typeOfJudg :: Judgement a -> Value
typeOfJudg (a :! v) = v
typeOfJudg _        = (ESort noPosition (Sort 1))

mapJudg :: (a -> b) -> Judgement a -> Judgement b
mapJudg f (IsType a) = IsType (f a)
mapJudg f (a :! v) = (f a) :! v


env :: TCEnv -> Environment
env (_,rho) = rho

ctx :: TCEnv -> Context
ctx (gamma,_) = gamma


-- The symbol table is for top-level definitions
emptyTCEnv :: TCEnv
emptyTCEnv = (emptyC,emptyEnv)


addAbsConst :: TCEnv -> UId -> TCEnv
addAbsConst (gamma,env) c = (gamma,addAccessible env c)

{- still used in (now broken) import -}
resetAbs :: TCEnv -> TCEnv
resetAbs (gamma,env) = (gamma,resetAccessible env)


breakTCEnv::TCEnv -> [UId] -> (TCEnv,TCEnv)
breakTCEnv ce@(g,E(r,sigma)) us = let
     (g2,g1) = (\ (x,y) -> (reverse x, reverse y))
             . break ((`elem` us). fst) . reverse  $ g
     dom1    = map fst g1
     (r1,r2) = partition ((`elem` dom1).fst) r
     (s1,s2) = partition (`elem` dom1) sigma
  in ((g1,E(r1,s1)),(g2,E(r2,s2)))

addBind::TCEnv -> Bind -> TCEnv
addBind (g,r) b@(hxs,_) = let (_,xs) = unzip hxs
                          in (addDeclC g b, addIdEnv r xs xs)

addBind1 (g,r) x a = (addC g x a, updateEnv r x (EVar x Nothing))


catEnv::Environment -> Environment -> Environment
catEnv (E(r1,s1)) (E( r2,s2)) = E (r1 ++ r2, s1 `union` s2)


listEnv::Environment -> [(UId,Value)]
listEnv (E(env, _)) = env



shrinkEnv:: Environment -> [UId] -> Environment
shrinkEnv (E (xvs, acs)) xs = E (xvs', acs \\ xs)
          where xvs' = filter (\(key,_) ->  key `notElem` xs) xvs


rangeEnv :: Environment -> [Value]
rangeEnv (E(xvs  ,_)) = map snd xvs
