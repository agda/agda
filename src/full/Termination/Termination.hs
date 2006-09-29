{-| 

  Termination checker, based on
    "A Predicative Analysis of Structural Recursion" by
    Andreas Abel and Thorsten Altenkirch.

-}

module Termination.Termination
  ( checkTerm
  ) where

import Prelude hiding (Ord)
import Termination.CallMatrix

-- | ...

type SCCInfo = [(String, String, CallMatrix)]

-- | Checks termination ...

checkTerm :: [SCCInfo] -> Maybe String
checkTerm = undefined

-- checkStrictlyPositive :: ?
-- checkStrictlyPositive = undefined

{-
import ISyntax
import CallMatrix
import Matrix(listMatrix)
import PPrint(pPrint, (~.), PPrint)
import Utilities(t)
import Util (remDup)
import Maybe(catMaybes)
import Array(range)
import List( (\\) )
--import AgdaTrace
            
terminatesAll :: [(UId,[CallMatrix])] -> [UId]
terminatesAll [] = []
terminatesAll ((f,ms):rb) 
    | terminates ms = terminatesAll rb
    | otherwise = f:terminatesAll rb


pr (x,m) = show x ++"\n"++(unlines (map show m)) ++"\n"

checkTermination :: [Call] -> [UId] 
checkTermination cs = terminatesAll cs' --  $ trace ("term "++ (unlines $ map pr cs')) cs'
           where cs' = funBehavior cs --trace ("term2 "++unlines (map printCall cs)) $ 


type OrderInfo = [(UId,UId)]

getOrder :: OrderInfo -> Exp -> UId -> TermOrder
getOrder os (EVar x _) y = if x == y then Equal else inOrder os x y
            where inOrder :: OrderInfo -> UId -> UId -> TermOrder
                  inOrder os x y 
                     | x == y = Lt
                     | otherwise =   case lookup x os of
                                        Just z -> inOrder os z y
                                        Nothing -> Gt
getOrder os (EApp e _) y = getOrder os e y
getOrder os (EMeta _ _ _ _ _ _) _ = Lt
getOrder _ _ _ = Gt






data FunInfo = FunInfo UId Int [UId]
     deriving Show
 -- Function names, arity and arguments

lookupFunInfo :: [FunInfo] -> UId -> Maybe (Int,[UId])
lookupFunInfo [] _ = Nothing
lookupFunInfo (FunInfo c i xs:fi) c'
             | c == c' = Just (i,xs)
             | otherwise  = lookupFunInfo fi c'

setVarsFunInfo :: [FunInfo] -> UId -> [UId] -> [FunInfo]
setVarsFunInfo fi f xs = FunInfo f (length xs) xs : fi

setArityFunInfo :: [FunInfo] -> UId -> Int -> [FunInfo]
setArityFunInfo [] _ _ = []
setArityFunInfo (i@(FunInfo c arityc xs) : fi) c' arityc' 
             | c == c' =  FunInfo c (max arityc arityc') xs : fi
             | otherwise = i : setArityFunInfo fi c' arityc'


initFunInfo :: UId -> FunInfo
initFunInfo c = FunInfo c 0 []


instance PPrint FunInfo where
    pPrint d p (FunInfo c n xs) = t"(TI "~.pPrint d p c~.t(" "++show n )~.t" "~.(pPrint d p xs) ~. t")"


buildMatrix :: OrderInfo -> (Int,Int) -> [Exp] -> [UId] -> CallMatrix
buildMatrix os (r,c) es xs = let m = listMatrix (r,c) rs 
                             in m -- trace ("\nbuild\n"++show m) m
          where rs :: [[TermOrder]]
                rs = buildRows os (r,c) es xs
                zs = zipWith (\ a b -> (a,b)) (range ((1,1),(r,c))) (foldl (++) [] rs)
                buildRows :: OrderInfo -> (Int,Int) -> [Exp] -> [UId] -> [[TermOrder]]
                buildRows os (0,_) _ _ = []
                buildRows _ (r,c) [] _ = replicate r (replicate c Gt)
                buildRows os (r,c) (e:es) xs = buildRow os c e xs : buildRows os (r-1,c) es xs
                buildRow :: OrderInfo -> Int -> Exp -> [UId] -> [TermOrder]
                buildRow os 0 _ _ = []
                buildRow os c _ [] = replicate c Gt
                buildRow os c e (x:xs) = getOrder os e x:buildRow os (c-1) e xs
                                       

type CorrInfo = ([FunInfo],OrderInfo)
-- Functions depending on each other, variable orders and call matrixes
-- for the functions

initCorrInfo = ([],[])

funInfo :: CorrInfo -> UId -> Maybe (Int,[UId])
funInfo (fi,_) c = lookupFunInfo fi c

orderInfo :: CorrInfo -> OrderInfo
orderInfo (_,oi) = oi

initFun :: UId -> CorrInfo -> CorrInfo
initFun c (fi,oi) = (initFunInfo c:fi,oi)

setVars :: CorrInfo -> UId -> [UId] -> CorrInfo
setVars (fi,os) c xs = (setVarsFunInfo fi c xs, os)

setArity :: CorrInfo -> UId -> Int -> CorrInfo
setArity (fi,os) c arityc = (setArityFunInfo fi c arityc, os)



addPatOrders :: CorrInfo -> UId -> [PatArg] -> CorrInfo
addPatOrders co _ [] = co
addPatOrders (fis,os) x (p:ps)= 
                           let os' = addPatOrder os x p
                           in addPatOrders (fis,os') x ps
            where addPatOrder os x (PArgT x' a) = (x',x):os
                  addPatOrder os x (PArg x') = (x',x):os
                         



buildCorrInfoLetDef ::  LetDef -> CorrInfo -> CorrInfo
buildCorrInfoLetDef d co  = buildCorrInfoDefs (flattenLetDef [d]) co
               

buildCorrInfoDefs :: [Def] -> CorrInfo ->  CorrInfo
buildCorrInfoDefs ds co = foldr buildCorrInfoDef co' ds --(trace (ppReadable co') co') ds
        where cxss = catMaybes $ map buildVarsDef ds
              co' = foldr (\cxs -> \co2 -> (uncurry (setVars co2)) cxs) co cxss


buildVarsDef ::  Def -> Maybe (UId,[UId])
buildVarsDef (Def _ _ _ c _ tel a (DExp e))  = Just (c,xs++xs')
                        where xs,xs' :: [UId]
                              xs = concatMap getVarsBind tel
                              xs' = leadingLambdaVars e
buildVarsDef (UnTypedDef _ _ _ c _ (DExp e)) = Just (c,xs)
                        where xs :: [UId]
                              xs = leadingLambdaVars e
buildVarsDef (Def _ _ _ c _ tel a PN)  = Just (c,xs)
                        where xs :: [UId]
                              xs = concatMap getVarsBind tel
buildVarsDef (Def _ _ _ c _ tel a Native)  = Just (c,xs)
                        where xs :: [UId]
                              xs = concatMap getVarsBind tel
buildVarsDef _ = Nothing

leadingLambdaVars :: Exp -> [UId]
leadingLambdaVars (EAbs (xs,a)  e) = (map snd xs) ++ leadingLambdaVars e
leadingLambdaVars (EDef _ e) = leadingLambdaVars e
leadingLambdaVars (EOpen _ _ e) = leadingLambdaVars e
leadingLambdaVars _ = []


buildCorrInfoDef :: Def -> CorrInfo -> CorrInfo
buildCorrInfoDef (Def _ _ _ c _ tel a rhs) co = co3
        where co1 = buildCorrInfoTel tel co 
              co2 = buildCorrInfo a co1
              co3 = buildCorrInfoRhs rhs co2
buildCorrInfoDef (UnTypedDef _ _ _ c _ rhs) co = buildCorrInfoRhs rhs co
buildCorrInfoDef (DOpen e oas) co = co2
         where co1 = buildCorrInfo e co
               co2 = buildCorrInfoOpenArgs oas co1

buildCorrInfoOpenArgs :: OpenArgs ->  CorrInfo -> CorrInfo
buildCorrInfoOpenArgs (OpenArgs oas _) co = 
          foldr buildCorrInfoOpenArg co oas

buildCorrInfoOpenArg :: OpenArg ->   CorrInfo -> CorrInfo
buildCorrInfoOpenArg (OpenConstT _ _ a) co = buildCorrInfo a co
buildCorrInfoOpenArg (OpenConstAsT _ _ _ a) co = buildCorrInfo a co
buildCorrInfoOpenArg _ co = co

buildCorrInfoRhs :: Drhs -> CorrInfo -> CorrInfo
buildCorrInfoRhs (DExp e) co = buildCorrInfo e co
buildCorrInfoRhs PN co = co
buildCorrInfoRhs Native co = co

buildCorrInfoTel :: Tel -> CorrInfo -> CorrInfo
buildCorrInfoTel tel co = foldr buildCorrInfo co (map snd tel)

buildCorrInfoSig :: ESigDef -> CorrInfo -> CorrInfo
buildCorrInfoSig (ESigAbs (_,a)) co = buildCorrInfo a co
buildCorrInfoSig (ESigDefn d) co = buildCorrInfoDefs [d] co



buildCorrInfo :: Exp -> CorrInfo -> CorrInfo
buildCorrInfo (EAbs  b e) co = buildCorrInfo e (buildCorrInfo (getTypeBind b) co) 
buildCorrInfo (EProd b e) co = buildCorrInfo e (buildCorrInfo (getTypeBind b) co) 
buildCorrInfo (EApp h es) co = 
            buildCorrInfo h (foldr buildCorrInfo co' (map snd es))
    where co' :: CorrInfo
          co' = case h of
                   (EConst c _) -> setArity co c (length es)
                   _ -> co
buildCorrInfo (EDef ds e) co = 
         buildCorrInfo e (foldr buildCorrInfoLetDef co ds)
buildCorrInfo (ECon _ es) co = foldr buildCorrInfo co (map snd es)
buildCorrInfo (EConF _ e es) co = buildCorrInfo e (foldr buildCorrInfo co (map snd es))
buildCorrInfo (EData cbs) co = 
             foldr buildCorrInfoTel co (map snd cbs)
buildCorrInfo (ECase e cbs) co = 
               buildCorrInfo e (foldr buildCorrInfo co' es)
       where (ps,es) = unzip cbs
             co' = foldr buildCorrInfoCaseBranch co ps
             buildCorrInfoCaseBranch :: CaseBranch -> CorrInfo -> CorrInfo
             --buildCorrInfoCaseBranch (CBCon _ pas) co = 
             buildCorrInfoCaseBranch (CBConM _ pas _) co = 
                      case e of
                          (EVar x _) -> addPatOrders co x pas
                          _ -> co
             buildCorrInfoCaseBranch _ co = co
buildCorrInfo (EProj e _) co = buildCorrInfo e co
buildCorrInfo (ESig _ ds) co = foldr buildCorrInfoSig co ds
buildCorrInfo (EStruct _ ds _ _ _ ) co = 
             foldr buildCorrInfoLetDef co ds
buildCorrInfo (Epackage _ ds _ _ _ ) co = foldr buildCorrInfoLetDef co ds
buildCorrInfo (EBinOp e1 e2 e3) co = buildCorrInfo (EApp e2 [(False,e1),(False,e3)]) co
buildCorrInfo (EOpen e1 oas e2) co = buildCorrInfo e2 co2
        where co1 = buildCorrInfo e1 co
              co2 = buildCorrInfoOpenArgs oas co1
buildCorrInfo _ co = co
 



newtype FunCall = FCall (UId,UId,[Exp])
     

instance PPrint FunCall where
    pPrint d p (FCall (f,g,es)) = pPrint d p (f,g,es)


mkFunCallsLetDef :: LetDef -> [FunCall]
mkFunCallsLetDef d = mkFunCallsDefs (flattenLetDef [d]) 

mkFunCallsDefs :: [Def]  -> [FunCall]
mkFunCallsDefs ds = concatMap (mkFunCallsDef cs)  ds
        where cs = concatMap idsDef ds
 
           
mkFunCallsDef :: [UId] ->  Def -> [FunCall]
mkFunCallsDef cs d@(Def _ rec _ c _ tel a rhs)  = 
     funCallsDef (cs,c) d 
mkFunCallsDef cs d@(UnTypedDef _ _ _ c _ rhs) = funCallsDef (cs,c) d
mkFunCallsDef cs (DOpen e oas)  = []  -- Gå ner här också ?!


mkFunCallsSig ::  ESigDef -> [FunCall]
mkFunCallsSig (ESigAbs (_,a)) = []
mkFunCallsSig (ESigDefn d) = mkFunCallsDef (idsDef d) d



funCallsLetDef ::  ([UId],UId) ->  LetDef -> [FunCall]
funCallsLetDef fs d = 
      funCallsDefs fs (flattenLetDef [d]) 
               

funCallsDefs ::  ([UId],UId) -> [Def] -> [FunCall]
funCallsDefs fs ds = concatMap (funCallsDef fs) ds


funCallsDef ::  ([UId],UId) -> Def -> [FunCall]
funCallsDef fs (Def _ _ _ c _ tel a rhs)  = 
    funCallsTel fs tel ++ funCalls fs a ++ funCallsRhs fs rhs
funCallsDef fs (UnTypedDef _ _ _ c _ rhs)  = funCallsRhs fs rhs
funCallsDef fs (DOpen e oas) = funCalls fs e  ++ funCallsOpenArgs fs oas 

funCallsOpenArgs ::([UId],UId) ->  OpenArgs -> [FunCall]
funCallsOpenArgs fs (OpenArgs oas _)  = 
          concatMap (funCallsOpenArg fs) oas

funCallsOpenArg :: ([UId],UId) -> OpenArg ->  [FunCall]
funCallsOpenArg fs (OpenConstT _ _ a) = funCalls fs a
funCallsOpenArg fs (OpenConstAsT _ _ _ a) = funCalls fs a
funCallsOpenArg fs _ = []

funCallsRhs :: ([UId],UId) -> Drhs -> [FunCall]
funCallsRhs fs (DExp e) = funCalls fs e
funCallsRhs fs PN = []
funCallsRhs fs Native = []

funCallsTel ::  ([UId],UId) -> Tel -> [FunCall]
funCallsTel fs tel = concatMap (\b -> funCalls fs (snd b)) tel

funCallsSig :: ([UId],UId) -> ESigDef -> [FunCall]
funCallsSig fs (ESigAbs (_,a)) = funCalls fs a
funCallsSig fs (ESigDefn d) = funCallsDefs fs [d]



funCalls ::  ([UId],UId) -> Exp -> [FunCall]
funCalls (fs,f) (EConst c _)
         | c `elem` fs = [FCall (f,c,[])]
         | otherwise = []
funCalls fs (EAbs b e) = funCalls fs e ++ funCalls fs (getTypeBind b) 
funCalls fs (EProd b e) = funCalls fs e ++ funCalls fs (getTypeBind b)
funCalls (fs,f) (EApp (EConst c _) es) 
         | c `elem` fs = [FCall (f,c,(map snd es))] ++ concatMap (funCalls (fs,f)) (map snd es)
         | otherwise = concatMap (funCalls (fs,f)) (map snd es)

funCalls fs (EApp h es) =
            concatMap (funCalls fs) (h:map snd es)
funCalls fs (EDef ds e) = 
         funCalls fs e ++ concatMap (funCallsLetDef fs) ds ++ concatMap mkFunCallsLetDef ds
funCalls fs (ECon _ es) = concatMap (funCalls fs) (map snd es)
funCalls fs (EConF _ e es)  = concatMap (funCalls fs) (e:map snd es)
funCalls fs (EData cbs) = 
             [] --concatMap (funCallsTel fs) (map snd cbs)
funCalls fs (ECase e cbs) = 
               funCalls fs e ++  concatMap (funCalls fs) es
       where (ps,es) = unzip cbs

funCalls fs (EProj e _) = funCalls fs e
funCalls fs (ESig _ ds) = concatMap (funCallsSig fs) ds ++ concatMap mkFunCallsSig ds
funCalls fs (EStruct _ ds _ _ _) = 
           concatMap (funCallsLetDef fs) ds ++ concatMap mkFunCallsLetDef ds
funCalls fs (Epackage _ ds _ _ _)  = concatMap (funCallsLetDef fs) ds ++ concatMap mkFunCallsLetDef ds 
funCalls fs (EBinOp e1 e2 e3) = funCalls fs (EApp e2 [(False,e1),(False,e3)])
funCalls fs (EOpen e1 oas e2) = funCalls fs e1 ++ funCallsOpenArgs fs oas 
funCalls _ _ = []



buildCalls ::  CorrInfo -> [FunCall] -> [Call]
buildCalls co fs = map (buildCallMatrix co) fs
      where buildCallMatrix ::  CorrInfo ->  FunCall ->  Call
            buildCallMatrix co (FCall (f,g,es)) =
                 let (arityf,xs) = getFunInfo f co
                     (arityg,_)  = getFunInfo g co
                     oi          = orderInfo co
                 in (f,g,(buildMatrix oi (arityg,arityf) es) xs)
               
            getFunInfo :: UId -> CorrInfo -> (Int,[UId])
            getFunInfo f co = maybe (error "Internal error getFunInfo") id (funInfo co f)


occurCheck ::  [UId] -> Exp -> [([UId],UId)]
occurCheck fs (EProd b e) = occurs fs (getTypeBind b) ++ occursSimple e
        where occursSimple e = 
                   case e of
                        EApp h es -> occursSimple h ++ concatMap (occurs fs) (map snd es)
                        EConst _ _ -> []
                        _ -> occurCheck fs e
occurCheck fs (EApp h es) =
            occurCheck fs h ++ concatMap (occurs fs) (map snd es)
occurCheck fs (EBinOp e1 e2 e3) = occurCheck fs (EApp e2 [(False,e1),(False,e3)])
occurCheck _ (EConst _ _) = []
occurCheck fs e = occurs fs e


occurs :: [UId] -> Exp -> [([UId],UId)]
occurs fs (EConst c _) = if c `elem` fs then [(fs,c)] else []
occurs fs (EAbs b e) = occursBind fs b ++ occurs fs e
occurs fs (EProd b a) = occursBind fs b ++ occurs fs a
occurs fs (EApp h es) = occurs fs h ++ concatMap (occurs fs) (map snd es)
occurs fs (EDef ds e) = concatMap (occursLetDef fs) ds ++ occurs fs e
occurs fs (ECon _ es) = concatMap (occurs fs) (map snd es)
occurs fs (EConF _ e es) = occurs fs e ++ concatMap (occurs fs) (map snd es)
occurs fs (EData cbs) = concatMap (occursConBind fs) cbs
occurs fs (ECase e cbs) = occurs fs e ++ concatMap (\(cb,e) -> occursCaseBranch fs cb ++ occurs fs e) cbs
occurs fs (EProj e _) = occurs fs e
occurs fs (ESig _ sds) = concatMap (occursSigDef fs) sds
occurs fs (EStruct _ ds _ _ _ ) = concatMap (occursLetDef fs) ds
occurs fs (Epackage _ ds _ _ _) = concatMap (occursLetDef fs) ds
occurs fs (EBinOp e1 e2 e3)     = concatMap (occurs fs) [e1,e2,e3]
occurs fs (EOpen e1 (OpenArgs oas _) e2) = 
    occurs fs e1 ++ concatMap (occursOpenArg fs) oas ++ occurs fs e2
occurs _ _                      = []

occursLetDef :: [UId] -> LetDef -> [([UId],UId)]
occursLetDef fs (DSimple d)  = occursDef fs d
occursLetDef fs (DMutual ds) = concatMap (occursDef fs) ds

occursDef :: [UId] -> Def -> [([UId],UId)]
occursDef fs (Def _ _ _ _ _ tel e rhs) = 
          concatMap (occursBind fs) tel ++ occurs fs e ++ occursRhs fs rhs
occursDef fs (UnTypedDef _ _ _ _ _ rhs) = occursRhs fs rhs
occursDef fs (DOpen e (OpenArgs oas _)) = occurs fs e ++ concatMap (occursOpenArg fs) oas

occursRhs :: [UId] -> Drhs -> [([UId],UId)]
occursRhs fs (DExp e) = occurs fs e
occursRhs _ _ = []

occursBind :: [UId] -> Bind -> [([UId],UId)]
occursBind fs (_,a) = occurs fs a

occursOpenArg :: [UId] -> OpenArg -> [([UId],UId)]
occursOpenArg fs (OpenConstT _ _ e)     = occurs fs e
occursOpenArg fs (OpenConstAsT _ _ _ e) = occurs fs e

occursSigDef :: [UId] -> ESigDef -> [([UId],UId)]
occursSigDef fs (ESigDefn d) = occursDef fs d
occursSigDef fs (ESigAbs b)  = occursBind fs b

occursConBind :: [UId] -> ConBind -> [([UId],UId)]
occursConBind fs (_,tel) = concatMap (occursBind fs) tel


occursCaseBranch :: [UId] -> CaseBranch -> [([UId],UId)]
--occursCaseBranch fs (CBCon _ pas) = concatMap (occursPatArg fs) pas
occursCaseBranch fs (CBConM _ pas _) = concatMap (occursPatArg fs) pas
occursCaseBranch _ _                 = []

occursPatArg :: [UId] -> PatArg -> [([UId],UId)]
occursPatArg fs (PArgT _ e) = occurs fs e
occursPatArg _ _            = []


checkPosLetDef :: LetDef -> [([UId],UId)]
checkPosLetDef (DSimple d) = checkPosDefs [d]
checkPosLetDef (DMutual ds) = checkPosDefs  ds

checkPosDefs :: [Def] -> [([UId],UId)]
checkPosDefs ds = concatMap (checkPosDef fs) ds
           where fs = concatMap idsDef ds     

checkPosDef :: [UId] -> Def -> [([UId],UId)]
checkPosDef fs (Def _ _ _ _ _ tel a rhs) = 
     concatMap checkPosBind tel ++ checkPosExp [] a ++ checkPosRhs fs rhs
checkPosDef fs (UnTypedDef _ _ _ _ _ rhs) = checkPosRhs fs rhs
checkPosDef fs (DOpen e (OpenArgs oas _)) = 
     checkPosExp [] e ++ concatMap checkPosOpenArg  oas

checkPosRhs :: [UId] -> Drhs -> [([UId],UId)]
checkPosRhs fs (DExp e) = checkPosExp fs e
checkPosRhs _ _         = []

checkPosOpenArg :: OpenArg -> [([UId],UId)]
checkPosOpenArg (OpenConstT _ _ e)     = checkPosExp []  e
checkPosOpenArg (OpenConstAsT _ _ _ e) = checkPosExp [] e
checkPosOpenArg _                      = []

checkPosBind :: Bind -> [([UId],UId)]
checkPosBind (_,a) = checkPosExp [] a

checkPosCaseBranch :: CaseBranch -> [([UId],UId)]
--checkPosCaseBranch (CBCon _ pas) = concatMap checkPosPatArg pas
checkPosCaseBranch (CBConM _ pas _) = concatMap checkPosPatArg pas
checkPosCaseBranch _                = []

checkPosPatArg :: PatArg -> [([UId],UId)]
checkPosPatArg (PArgT _ e) = checkPosExp [] e
checkPosPatArg _           = []


checkPosSigDef :: ESigDef -> [([UId],UId)]
checkPosSigDef (ESigDefn d) = checkPosDef [] d
checkPosSigDef (ESigAbs b)  = checkPosBind b

checkPosExp :: [UId] -> Exp -> [([UId],UId)] 
checkPosExp fs (EAbs b e)            = checkPosBind b ++ checkPosExp fs e
checkPosExp fs (EProd b a)           = checkPosBind b ++ checkPosExp [] a
checkPosExp fs (EApp h es)           = checkPosExp [] h ++ concatMap (checkPosExp []) (map snd es)
checkPosExp fs (EDef ds e)           = concatMap checkPosLetDef ds ++ checkPosExp [] e
checkPosExp _  (ECon _ es)           = concatMap (checkPosExp []) (map snd es)
checkPosExp _  (EConF _ e es)        = checkPosExp [] e ++ concatMap (checkPosExp []) (map snd es)
checkPosExp fs (EData cbs)           = concatMap (occurCheck fs) es ++ concatMap (checkPosExp []) es
              where es :: [Exp]
                    es = concatMap (\cb -> map snd (snd cb)) cbs
checkPosExp fs (ECase e cbs)         = checkPosExp [] e ++ 
                                       concatMap (\(cb,e) -> checkPosCaseBranch cb ++ 
                                                             checkPosExp [] e         ) cbs
checkPosExp _ (EProj e _)            = checkPosExp [] e
checkPosExp _ (ESig _ sds)           = concatMap checkPosSigDef  sds
checkPosExp _ (EStruct _ ds _ _ _ )  = concatMap checkPosLetDef ds
checkPosExp _ (Epackage _ ds _ _ _ ) = concatMap checkPosLetDef ds
checkPosExp _ (EBinOp e1 e2 e3)      = concatMap (checkPosExp []) [e1,e2,e3]
checkPosExp _ (EOpen e1 (OpenArgs oas _) e2) = 
    checkPosExp [] e1 ++ concatMap checkPosOpenArg  oas ++ checkPosExp [] e2
checkPosExp _ _                      = []

--checkPosDefs :: [UId] -> Def -> [UId]
--checkPosDefs fs  


checkTermLetDef :: LetDef -> [UId]
checkTermLetDef d = checkTermination calls
     where co    = buildCorrInfoLetDef d initCorrInfo
           cs    = mkFunCallsLetDef d
           calls = buildCalls co cs

--checkTermination cs 

checkTermLetDefs :: [LetDef] -> [UId]
checkTermLetDefs ds = concatMap checkTermLetDef ds

checkPosLetDefs :: [LetDef] -> [([UId],UId)]
checkPosLetDefs ds = concatMap checkPosLetDef ds
-}