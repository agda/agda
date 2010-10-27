module CITrans where
--import UIdInfo
import Position(noPosition)
import Id(Id, UId, getIdPosition, addId, remId, SymTab, rangeST, initST, lookupST,toId)
import Monads
import Error
import PPrint(ppReadable)

type CITrans = (SymTab,   -- free + case-bound vars
                SymTab,   -- consts
                [UId],    -- case-bound vars
                Maybe     -- if in the rhs ... (not quite.) ..
                (UId,     -- current const being defined.
                 [UId]))  -- its tel vars + lambda vars after it
                          -- i.e, those vars whose values are to be printed
                          -- together with the const.  IN TEL ORDER.

-- CONSIDER UNIFYING CITrans and CtxInfo in a global table.

freeVarScope :: CITrans -> [UId]
freeVarScope (vst,cst,cb,_) =   [x | x <- rangeST vst, x `notElem` cb]


varScope :: CITrans -> [UId]
varScope (vst,cst,cb,_) =  rangeST vst


cstScope :: CITrans -> [UId]
cstScope (vst,cst,cb,_) =  rangeST cst

caseVarScope :: CITrans -> [UId]
caseVarScope (vst,cst,cb,_) = cb

currentConstPV :: CITrans -> Maybe (UId,[UId])
currentConstPV (_,_,_,cpvs) = cpvs


scope :: CITrans -> [UId]
scope (vst,cst,cb,_) =  rangeST vst ++ rangeST cst

addVar :: Id -> UId -> CITrans -> CITrans
addVar x x' (vst,cst,cb,cpvs) = let vst' = addId x x' vst
                                    cst' = remId x cst
                           in (vst',cst',cb,cpvs)

addCst ::  Id ->  UId -> CITrans -> CITrans
addCst c c' (vst,cst,cb,cpvs) = let cst' = addId c c' cst
                                    vst' = remId c vst
                           in (vst',cst',cb,cpvs)

addCsts ::  [(Id,UId)] -> CITrans -> CITrans
addCsts ccs cit = foldr (uncurry addCst) cit ccs



addCaseVar :: UId -> CITrans -> CITrans
addCaseVar x (vst,cst,cb,cpvs) = (vst,cst,x:cb,cpvs)

updateCCPV :: UId -> [UId] -> CITrans -> CITrans
updateCCPV cc pvs (vst,cst,cb,_) = (vst,cst,cb, Just (cc,pvs))

addPV :: [UId] -> CITrans -> CITrans
addPV xs (vst,cst,cb, Just (cc,pvs)) = (vst,cst,cb, Just (cc,pvs++xs))
addPV xs cit@(_,_,_,Nothing) = cit
  -- this happens when Clam is in the lhs.

lookupId :: CITrans -> Id -> Error (Either UId UId)
lookupId (vst,cst,cb,_) i = case lookupST vst i of
                           Just x -> return (Left x)
                           Nothing -> case lookupST cst i of
                                         Just c -> return (Right c)
                                         Nothing -> raise (scopeError i)

lookupVar :: CITrans -> Id -> Error UId
lookupVar (vst,cst,_,_) x = liftMaybeE (lookupST vst x) (scopeError x)

lookupCst :: CITrans -> Id -> Error UId
lookupCst (vst,cst,_,_) c = liftMaybeE (lookupST cst c) (scopeError c)



scopeError :: Id -> EMsg
scopeError i = eMsg (getIdPosition i) (EUnbound (ppReadable i))


getCstSymTab :: CITrans -> SymTab
getCstSymTab (_,cst,_,_) = cst

getVarSymTab :: CITrans -> SymTab
getVarSymTab (vst,_,_,_) = vst

getCaseBoundVar :: CITrans -> [UId]
getCaseBoundVar (_,_,cb,_) = cb

initCIT :: CITrans
initCIT = (initST,initST,[],dummyCCPV "initCIT:")

initCIT_CST :: SymTab -> CITrans
initCIT_CST st = (initST,st,[],dummyCCPV "initCIT:")



dummyCCPV::String -> Maybe (UId,[UId])
dummyCCPV s = Nothing


inScopeVar :: CITrans -> UId -> Bool
inScopeVar (vst,_,_,_) x = maybe False (x==) (lookupST vst (toId x))


inScopeCst :: CITrans -> UId -> Bool
inScopeCst (_,cst,_,_) x = maybe False (x==) (lookupST cst (toId x))
