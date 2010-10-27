{-|

  ISyntax abstract syntax.

  Properties:

  * Names are unique.
  * Equipped with position information.

  CITranslate translates CSyntax.CExpr into Exp

-}

module ISynType where
import Data.Maybe(catMaybes)
import Literal(Literal)
import Id(Id,UId,dummyUId,toId,toDummyUId,dummyId,SymTab)
import Position(Position,noPosition)
import MetaVars(MetaVar,Visibility)
import CITrans(CITrans)
import Util(apSnd)
import Data.Map ( Map )
import PluginType
--import ClassEnv

data Program = Program [LetDef]
data LetDef  = DSimple Def | DMutual [Def]                     deriving (Eq,Show)
                                                     --  | DOpen Exp OpenArgs
-- PJ 041015: Not all [EProp] combinations are allowed (private public ??)
data Def     =  Def Bool  Bool    [EProp] UId FCVars  Tel Exp Drhs
                 -- ^ REMOVE
                      --- ^ is recursive
             |  UnTypedDef Bool  Bool [EProp] UId FCVars          Drhs
             |  DOpen Exp OpenArgs                             deriving (Eq,Show)
data Drhs    = DExp Exp | PN | Native   deriving (Eq,Show)

data Exp =
   EMeta     MetaVar Position Bool TransClass Int Visibility
 | EMetaV    MetaVar Bool FCVars TransClass
 | EVar      UId (Maybe TransClass)
 | EConst    UId (Maybe TransClass)
 | EConstV   UId FCVars
 | ESort     Position Sort
 | EProd     Bind  Exp
 | EArrow    Bool Exp Exp -- kept for nicer pretty printing and easier to
                          -- automatically
 | EAbs      Bind  Exp
 | EApp      Exp  [(Bool,Exp)]
 | EBinOp    Exp   Exp Exp                                -- EBinOp e1 op e2
 | EIf       Exp Exp Exp -- kept for nicer pretty printing
 | EDef      [LetDef] Exp
 | EOpen     Exp OpenArgs Exp
 | ESig      Position [ESigDef]
 | EStruct   Position [LetDef] FCVars [(Id,UId)] [UId]       -- pub and abs const
 | EPackageType
 | Epackage  Position [LetDef] FCVars [(Id,UId)] [UId]      -- pub and abs const
 | EProj     Exp Id
 | EData     [ConBind]
 | EIndData  Tel [IndConBind]          -- Tel is [] when used for 1.
 | ECon      Id     [(Bool,Exp)]
 | EConF     Id Exp [(Bool,Exp)]
 | ECase     Exp [(CaseBranch,Exp)]
 | PreMeta
 | EStop MetaVar Exp
 | EClos Environment Exp
 | ELiteral Position Literal
 | EExternal (Plugin Exp TransClass)

--- | EClass Position [Id] [ESigDef]
--- | EInstance Position [LetDef] FCVars [UId] [UId]       -- pub and abs const

                                       ---  |  ETheory  Position [LetDef] [UId]
                                       ---  |  ETheoryV Position [UId] [UId]
   deriving (Eq,Show)

type Head = Exp

data ESigDef = ESigAbs Decl | ESigDefn Def                     deriving (Eq,Show)

type Bind       = ([(Bool,UId)],Exp)
type Decl       = Bind
type Tel        = [Decl]
type ConBind    = (Id,Tel)
type IndConBind = (ConBind,[(Bool,Exp)])
                       ---  ^ substitution from cb to tel of EIndData

data PatArg = PArgT UId Exp | PArg UId                         deriving (Eq,Show)

data CaseBranch = CBConM Id  [PatArg]  {- constructor name, args -}
                         (Maybe (UId,FCVars))
                                {- NOW NOT USED. just Nothing.
                                   see CITranslate.hs
                                   if the cased exp is a var, its uid
                                   as a constant in this branch, and its
                                   free vars (incl. patarg)
                                -}

                 | CBLit Position Literal   -- defunct
          deriving (Eq,Show)

data OpenArg  = OpenConst    [EProp]    UId
              | OpenConstAs  [EProp] Id UId
              | OpenConstT   [EProp]    UId Exp
              | OpenConstAsT [EProp] Id UId Exp                deriving (Eq,Show)
data OpenArgs = OpenArgs [OpenArg] FCVars                      deriving (Eq,Show)

data Sort = Sort Int                                  deriving (Show,Eq,Ord)

data EProp = Eprivate | Epublic | Eabstract | Econcrete
                                                    deriving (Eq, Ord, Show)


mapLetDef :: (Def -> Def) -> LetDef -> LetDef
mapLetDef f (DSimple d)  = DSimple (f d)
mapLetDef f (DMutual ds) = DMutual (map f ds)
--mapLetDef _ d = d

letDefToDefList :: LetDef -> [Def]
letDefToDefList (DSimple d) = [d]
letDefToDefList (DMutual ds) = ds

flattenLetDef :: [LetDef] -> [Def]
flattenLetDef = concatMap letDefToDefList

updateRhsDef :: Def -> Drhs -> Def
updateRhsDef (Def blocked rec p c xs tel a _) rhs = Def blocked rec p c xs tel a rhs
updateRhsDef _ _ = error "updateRhsDef: "


absRhs :: Tel -> Drhs -> Drhs
absRhs tel (DExp  e) = DExp (eAbs tel e)
absRhs _ d          = d
-- absRhs _ PN          = PN
-- absRhs _ Native = Native

mkDef  :: Bool -> Bool -> [EProp] -> UId -> FCVars -> Tel -> Exp -> Drhs -> Def
mkEDef :: Bool -> Bool -> [EProp] -> UId -> FCVars -> Tel -> Exp -> Exp  -> Def
mkDef  blocked rec p c xs tel a rhs = Def blocked rec p c xs tel a rhs
mkEDef blocked rec p c xs tel a e   = Def blocked rec p c xs tel a (DExp e)

mkAbstract :: Def -> Def
mkAbstract (Def blocked rec ps c xs tel a (DExp  e)) = Def blocked rec ps c xs tel a PN
mkAbstract (UnTypedDef blocked rec ps c xs (DExp  e)) = UnTypedDef blocked rec ps c xs PN
mkAbstract d = d

mkUnTyped :: Bool -> Bool -> [EProp] -> UId -> FCVars -> Exp -> Def
mkUnTyped blocked rec p c xs e = UnTypedDef blocked rec p c xs (DExp e)

unTypeDef :: Def -> Def
unTypeDef (Def blocked rec ps c xs [] a (DExp  e))
     = mkUnTyped blocked rec ps c xs e
unTypeDef d = d


mkPN ::  Bool -> Bool -> [EProp] -> UId -> FCVars -> Tel -> Exp -> Def
mkPN blocked rec p c xs tel a = Def blocked False  p c xs tel a PN

mkNative ::  Bool -> Bool -> [EProp] -> UId -> FCVars -> Tel -> Exp -> Def
mkNative blocked rec p c xs tel a = Def blocked False p c xs tel a Native


nameOfDef :: Def -> UId
nameOfDef (Def _ _ _ c _ _ _ _) = c
nameOfDef (UnTypedDef _ _ _ c _ _) = c

rhsOfDef :: Def -> Drhs
rhsOfDef (Def _ _ _ _ _ tel _ rhs) = absRhs tel rhs
rhsOfDef (UnTypedDef _ _ _ _ _ rhs) = rhs
      --  | Eabstract `elem` ps = PN
      --  | otherwise = absRhs tel rhs

typeOfDef :: Def -> Exp
typeOfDef (Def _ _ _ _ _ tel a _) = eProd tel a
typeOfDef _ = error "typeOfDef: "

telOfDef :: Def -> Tel
telOfDef (Def _ _ _ _ _ tel _ _) = tel
telOfDef (UnTypedDef _ _ _ _ _ _) = []
telOfDef d = error ("telOfDef")


varScopeDef :: Def -> FCVars
varScopeDef (Def _ _ _ _ xs _ _ _) = xs
varScopeDef (UnTypedDef _ _ _ _ xs _) = xs
varScopeDef (DOpen _ (OpenArgs _ xs)) = xs


isRecDef :: Def -> Bool
isRecDef (Def _ rec _ _ _ _ _ _) = rec
isRecDef (UnTypedDef _ rec _ _ _ _ ) = rec
isRecDef _ = False

isBlockedDef :: Def -> Bool
isBlockedDef (Def blocked _ _ _ _ _ _ _) = blocked
isBlockedDef (UnTypedDef blocked _ _ _ _ _ ) = blocked
isBlockedDef _ = False

mkVars :: [UId] -> [Exp]
mkVars xs = [EVar x Nothing | x <- xs]

isVar :: Exp -> Bool
isVar (EVar x _) = True
isVar _        = False

eType :: Position -> Exp
eType p = ESort p (Sort 1)

eSet ::  Position -> Exp
eSet p  = ESort p (Sort 0)



eApp' :: Exp -> [(Bool,Exp)] -> Exp
eApp' e [] = e
eApp' e es = eApp e es
       where eApp :: Exp -> [(Bool,Exp)] -> Exp
             eApp (EApp e es) es' = eApp e (es ++ es')
             eApp (ECon c es) es' = ECon c (es ++ es')
             eApp (EConF c e es) es' = EConF c e (es++ es')
             eApp e es = EApp e es


eArrow :: Bool -> Exp -> Exp -> Exp
eArrow h a b = EProd ([(h,toDummyUId dummyId)],a) b



eAbs :: [Bind] -> Exp -> Exp
eAbs [] e           = e
eAbs (([],_):tel) e = eAbs tel e
eAbs (b:bs) e       = EAbs b (eAbs bs e)

eProd :: Tel -> Exp -> Exp
eProd [] e           = e
eProd (([],_):tel) e = eProd tel e
eProd (b:tel) e      = EProd b (eProd tel e)



eLiteral :: Literal -> Exp
eLiteral l = ELiteral noPosition l

expToLiteral :: Exp -> Maybe Literal
expToLiteral (ELiteral _ l) = Just l
expToLiteral _ = Nothing

isStopped :: Exp -> Bool
isStopped (EStop _ e) = True
isStopped _           = False


stoppedBy:: [Exp] -> Maybe MetaVar
stoppedBy [] = Nothing
stoppedBy (EStop m _:_) = Just m
stoppedBy (_:es) = stoppedBy es

initEAbs :: Decl -> Exp -> Exp
initEAbs d e = EAbs d e

domESigDefs :: [ESigDef] -> [UId]
domESigDefs []                   = []
domESigDefs (ESigAbs (xs,_):sds) = (map snd xs) ++ domESigDefs sds
domESigDefs (_:sds)              = domESigDefs sds

typeD :: Decl -> Exp
typeD (_,a) = a

domTel :: Tel -> [UId]
domTel tel = concatMap getVarsBind tel

addBindTel :: Tel -> Decl -> Tel
addBindTel tel ([],_)  = tel
addBindTel tel b       = b:tel

getUIdPatt (PArgT x _) = x
getUIdPatt (PArg  x  ) = x

getIdBr (CBConM c _ _) = c
getIdBr _              = error "getIdBr: CBLit is defunct."

telCB :: ConBind -> Tel
telCB (_,tel) = tel

idCB :: ConBind -> Id
idCB (i,_) = i


lookupConstr :: Id -> [ConBind] -> Maybe Tel
lookupConstr c cbs = lookup c cbs

getVarsBind :: Bind -> [UId]
getVarsBind (hxs,_) = map snd hxs

getTypeBind :: Bind -> Exp
getTypeBind (_,a) = a



addToSort :: Int -> Sort -> Sort
addToSort n (Sort k) = Sort (n+k)

idOpenArg :: OpenArg -> UId
idOpenArg (OpenConst _ c)        = c
idOpenArg (OpenConstAs _ _ c)    = c
idOpenArg (OpenConstT _ c _)     = c
idOpenArg (OpenConstAsT _ _ c _) = c

propOpenArg :: OpenArg -> [EProp]
propOpenArg (OpenConst ps _)        = ps
propOpenArg (OpenConstAs ps _ c)    = ps
propOpenArg (OpenConstT ps c _)     = ps
propOpenArg (OpenConstAsT ps _ c _) = ps



isAbstract :: Def -> Bool
isAbstract (Def _ _ ps _ _ _ _ _) = Eabstract `elem` ps
isAbstract (UnTypedDef _ _ ps _ _ _) = Eabstract `elem` ps
isAbstract _ = False


abstractLetDef :: [LetDef] -> [UId]
abstractLetDef []                 = []
abstractLetDef (DSimple d : ds)   = abstractDef d ++ abstractLetDef ds
abstractLetDef (DMutual ds : ds') = concatMap abstractDef ds ++
                                    abstractLetDef ds'

abstractDef :: Def -> [UId]
abstractDef (Def _ _ ps c _ _ _ _)
    | Eabstract `elem` ps  = [c]
    | otherwise = []
abstractDef (UnTypedDef _ _ ps c _ _)
    | Eabstract `elem` ps  = [c]
    | otherwise            = []
abstractDef (DOpen _ (OpenArgs oas _))
                           = catMaybes (map visibleOpenArg oas)

isPrivate :: Def -> Bool
isPrivate (Def _ _ ps _ _ _ _ _) = Eprivate `elem` ps
isPrivate (UnTypedDef _ _ ps _ _ _) = Eprivate `elem` ps
isPrivate _ = False

domVisibleLetDef :: [LetDef] -> [UId]
domVisibleLetDef []                 = []
domVisibleLetDef (DSimple d : ds)   = domVisibleDef d ++ domVisibleLetDef ds
domVisibleLetDef (DMutual ds : ds') = concatMap domVisibleDef ds ++
                                      domVisibleLetDef ds'
--domVisibleLetDef (DOpen _ oas : ds) = exportConsts oas++domVisibleLetDef ds
domVisibleDef :: Def -> [UId]
domVisibleDef (Def _ _ ps c _ _ _ _)
    | Eprivate `elem` ps  = []
    | otherwise = [c]
domVisibleDef (UnTypedDef _ _ ps c _ _)
    | Eprivate `elem` ps  = []
    | otherwise           = [c]
domVisibleDef (DOpen _ (OpenArgs oas _))
                          = catMaybes (map visibleOpenArg oas)

visibleOpenArg :: OpenArg -> Maybe UId
visibleOpenArg (OpenConst ps c)
    | Eprivate `elem` ps = Nothing
    | otherwise          = Just c
visibleOpenArg (OpenConstAs ps i c)
    | Eprivate `elem` ps = Nothing
    | otherwise          = Just c
visibleOpenArg (OpenConstT ps c _)
    | Eprivate `elem` ps = Nothing
    | otherwise          = Just c
visibleOpenArg (OpenConstAsT ps i c _)
    | Eprivate `elem` ps = Nothing
    | otherwise          = Just c

abstractOpenArg :: OpenArg -> Maybe UId                  -- used in import.
abstractOpenArg (OpenConst ps c)
    | Eabstract `elem` ps  = Just c
    | otherwise = Nothing
abstractOpenArg (OpenConstAs ps i c)
    | Eabstract `elem` ps = Just c
    | otherwise           = Nothing
abstractOpenArg (OpenConstT ps c _)
    | Eabstract `elem` ps = Just c
    | otherwise           = Nothing
abstractOpenArg (OpenConstAsT ps i c _)
    | Eabstract `elem` ps = Just c
    | otherwise           = Nothing

abstractOpenArgs :: OpenArgs -> [UId]
abstractOpenArgs (OpenArgs os _) = catMaybes (map abstractOpenArg os)

type OpenArgG = ([EProp],      {- modifieres -}
                 Id,           {- label name, default toId of the next -}
                 UId,          {- UId as a const defed by this open    -}
                 Maybe Exp)    {- possibly given type                  -}
toOpenArgG:: OpenArg -> OpenArgG
toOpenArgG oa = case oa of
    (OpenConst    ps   c  ) -> (ps, toId c, c, Nothing)
    (OpenConstAs  ps n c  ) -> (ps,      n, c, Nothing)
    (OpenConstT   ps   c a) -> (ps, toId c, c, Just a )
    (OpenConstAsT ps n c a) -> (ps,      n, c, Just a )



idsDef :: Def -> [UId]
idsDef (Def _ _ _ c _ _ _ _) = [c]
idsDef (UnTypedDef _ _ _ c _ _) = [c]
idsDef _ = []

idsLetDef :: LetDef -> [UId]
idsLetDef (DSimple d)  = idsDef d
idsLetDef (DMutual ds) = concatMap idsDef ds

{- want to put it in ISynEnv ... -}

type Value = Exp
-- terms of this type should only be created with the operations in Eval,
-- but this invariant has been broken on some places which needs to be fixed
-- Possible values are (I need to think this through CC)
--  v  = EVar x | ECon i [(h1,v11),...,(hn,vn) |  EConF i e [(h1,v1),...,(hn,vn) |
--     | EApp  v [(h1,v1),...,(hn,vn) ] (where v is not a lambda)
--     | EProj v n   (where v is not EStructV or Eackage)
--     | ELiteral | EStop m v | ESort _ _ | EPackageType
--     | EClos eclos env
--  eclos = EConstV c xs | Eackage _ _ _ _ _ | EStructV _ _ _ _ _ | EMetaV _ _ _
--        | EAbs _ _ | EProd _ _
--        | EData _ _ | EIndData _ _ _ | ECase _ _ | ESig _ _

newtype Environment = E (Env,[UId])  deriving (Eq,Show)
                         --  ^^^ accessibles ...

type Env = [(UId,Value)] --FiniteMap UId Value

{- ---- -}
type FCVars = [UId]

{-
Instead of backtracking in the unfold, one could instead
decorate all expressions that has  name equality
such as data, idata and sig (+ related metas) with
appropiate information so that backtracking is not needed
but it still behaves as equality on name. Makoto had
started this, but I took it away to do a more complete
revision later (CC).
                         -- preparing for switching among
                         -- 1. free+cased vars (as it is now;
                         --    inefficient for Equals)
                         -- 2. (free,free+cased)
                         -- 3. free vars only (with cased var as consts)



{- Static context info for an ocurrence of exps -}
{- Will be used in
   1. equality check
   2. garbage collection (retrieveEnv)
   3. printing
   4. solve? -}
{- all those 'isProbLam' things will be decorated by this in future.
   I'm starting with just EIndData. -}
type CtxInfo = (UId,     -- of this occurrence (strange for const?)
                [UId],   -- free vars, for 1 (4?)
                [UId],   -- free+cased vars, for 2
                (UId,    -- const in whose def this occurrence is and
                 [UId])) -- def tel vars and lambda bound vars after them, for3

getCtxOcc :: CtxInfo -> UId
getCtxOcc (ou,_,_,_) = ou

getCtxFV :: CtxInfo -> [UId]
getCtxFV (_,xs,_,_) = xs

getCtxFCV :: CtxInfo -> [UId]
getCtxFCV (_,_,ys,_) = ys

getCtxCCPV :: CtxInfo -> (UId,[UId])
getCtxCCPV (_,_,_,ccpvs) = ccpvs

{- --- -}
-}

appnormalized :: Value -> (Value,[(Bool,Value)])
appnormalized (EStop _ v) = appnormalized v
appnormalized (EApp h vs) = apSnd (++ vs) (appnormalized h)
appnormalized (EBinOp v1 op v2) = (op,[(False,v1),(False,v2)])
appnormalized h           = (h,[])


transInfoExp :: Exp -> Maybe TransClass
transInfoExp (EConst _ cit) = cit
transInfoExp (EVar _ cit) = cit
transInfoExp (EApp h es ) = transInfoExp h
transInfoExp (EBinOp _ op _) = transInfoExp op
transInfoExp (EProj h n) = transInfoExp h
transInfoExp (EIf e _ _ ) = transInfoExp e
transInfoExp (EMeta _ _ _ cit _ _) = Just cit
transInfoExp (EMetaV _ _ _ cit) = Just cit
transInfoExp (EStop m e ) = transInfoExp e
transInfoExp (EClos _ e) = transInfoExp e
transInfoExp _ = Nothing

mkHiddenBind :: Bind -> Bind
mkHiddenBind (hxs,a) = ([(True,x) | (_,x) <- hxs],a)

mkVisibleBind :: Bind -> Bind
mkVisibleBind (hxs,a) = ([(False,x) | (_,x) <- hxs],a)

{- Class environment definition -}

type ClassEnv = (ClassTable,InstanceTable)

initClassEnv = (initSuperClasses,initInstTable)

initSuperClasses = []
initInstTable = []

type SuperClass = (UId,UId)
type SuperClasses = [SuperClass]

type ClassTable = [(UId,SuperClasses)]   -- list of superclasses together with the "path" projections to
                                         -- reach them

type InstancePath = (UId,[UId])
type InstanceInfo = (UId,InstancePath)
                --- ^ Class name
type InstanceTable = [(UId,[InstanceInfo])]   -- type name and it's instances together with the name of
                                           -- the instance


type TransClass = (CITrans,ClassEnv)
