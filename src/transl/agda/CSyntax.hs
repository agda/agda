{-|
  Agda abstract syntax which is produced by the parser

  The name CSyntax originates from `Cayenne Syntax´, which served as a
  starting point for Agda. (Lennart says it actually meant `concrete syntax´.)
-}

module CSyntax(module CSyntax, pprId,module MetaVars) where
import BinParse(Fixity(..),prec)
import Error
import Position
import Id
import Literal
import MetaVars
import PluginType(Plugin(..))
import Data.List (groupBy)

data CProgram
        = CProgram [CModule]
    --  | ErrProgram EMsg
        deriving (Eq, Ord)

data CModule
        = CModule Id [CArg] CPackageBody
        deriving (Eq, Ord)


type Comment = String

data CExpr =
     CVar Id
   | CStar Position Int Int  -- ^ #0 = Set, #1 = Type ... (second Int unused)
   | Clam (Bool,CBind) CExpr
   | CUniv CArg CExpr
   | CArrow Bool CExpr CExpr
   | Clet [CLetDef] CExpr
   | CProduct Position [CSign]
   | CRecord [CProp] Position [CLetDef]
   | Copen CExpr COpenArgs CExpr
   | CSelect CExpr Id
   | CSum CSummands
   | CCCon Id CType  -- Remove!
   | CCConS Id       -- Remove!
   | Ccase CExpr CCaseArms
   | CApply CExpr [(Bool,CExpr)]
   | CBinOp CExpr Id CExpr
   | CMeta Position  Bool Visibility MetaVar -- first Bool indicates what is allowed
                                       -- in the metaexp, snd if should be automatically solvable or not
   | CClos CEnv CExpr         -- Only for printing
   | Ccomment Bool Comment CExpr -- True if comment is to the left
   | CPackageType   -- Just for printing
   | CIndSum [CArg] CIndSummands
         --  ^ the telescope over which this is inductive
   | CExternal (Plugin CExpr ())
   | Cif CExpr CExpr CExpr
   | CLit Position Literal
   | CDo Position [CDoBind]
   | CList Position [CExpr]
        deriving (Ord,Show)


type CEnv = [(Id,CExpr)]

cApply e [] = e
cApply (CApply e []) as = CApply e as
cApply e as = CApply e as

cVar v = CVar v

cLam :: [(Bool,CBind)] -> CExpr -> CExpr
cLam args e = foldr Clam e args

clam :: CArg -> CExpr -> CExpr
clam (CArg xs (CMeta _ _ vis _)) e |(not (isVisible vis))
     = cLam (toCBind xs Nothing) e
clam (CArg xs a) e = cLam (toCBind xs (Just a)) e

toCBind :: [(Bool,Id)] -> Maybe CExpr -> [(Bool,CBind)]
toCBind bs mt = map trans part
      where part = groupBy (\p1 -> \p2 -> fst p1 == fst p2) bs
            trans :: [(Bool,Id)] -> (Bool,CBind)
            trans bxs = (fst (head bxs),CBind (map snd bs) mt)


cUniv1 :: CArg -> CExpr -> CExpr
cUniv1 (CArg ((hidden,x):xs) a) b | isDummyId x =
    CArrow hidden a (cUniv1 (CArg xs a) b)
cUniv1 (CArg [] a) b  = b
cUniv1 cb b = CUniv cb b

cUniv :: [CArg] -> CExpr -> CExpr
cUniv cb b = foldr cUniv1 b cb



cSet :: Position -> CExpr
cSet pos = CStar pos 0 (-1)

cType :: Position -> CExpr
cType pos = CStar pos 1 (-1)

cBinOp :: Id -> [CExpr] -> CExpr
cBinOp op es = foldr1 (\e1 -> \e2 -> CBinOp e1 op e2) es

type CType = CExpr
type CArgs = [CArg]
type CSummand = (Id, CArgs)
type CSummands = [CSummand]
type CCaseArms = [(CPat, CExpr)]
data CIndSummand = CIndExpl CSummand Id [(Bool,CExpr)]
                                    --  ^ substitution
                 | CIndImpl CSummand [(Bool,CExpr)]
                                 --  ^ substitution
           deriving (Eq,Ord,Show)
type CIndSummands = [CIndSummand]


data CProp
        = Cprivate
        | Cpublic
        | Cabstract
        | Cconcrete
        deriving (Eq, Ord, Show)

data COArg
        = COArgT [CProp] Id CType
        | COArg [CProp] Id
        | COArgAs [CProp] Id Id
        | COArgAsT [CProp] Id CType Id
        deriving (Eq, Ord,Show)


type COArgs = [COArg]
data COpenArgs
        = COpenArgs [COArg]
--      | COpenAll
        deriving (Eq, Ord,Show)


data CDef = CDef [CProp] CDefn | CDefComment Comment
        deriving (Eq, Ord,Show)

data CLetDef = CSimple CDef | CMutual [CDef] | CLetDefComment Comment
--             | CErrDef EMsg
         deriving (Ord,Eq,Show)

mapCLetDef :: (CDef -> CDef) -> CLetDef -> CLetDef
mapCLetDef f (CSimple d) = CSimple (f d)
mapCLetDef f (CMutual ds) = CMutual (map f ds)
mapCLetDef _ d = d


flattenCLet :: CLetDef -> [CDef]
flattenCLet (CSimple d) = [d]
flattenCLet (CMutual ds) = ds
flattenCLet _ = []

data CDefn
        = CValueT Id [CArg] CType CExpr
        | CValueS Id [CArg] CType CClause
--  | CValueP Id [CClause]
        | Ctype Id CArgs CType
        | Cnewtype Id CArgs CType CSummand
        | Cdata Id CArgs (Maybe CType) CSummands
        | Cidata Id CArgs CType CIndSummands
        | CValue Id CExpr
        | CAxiom Id [CArg] CType
        | CNative Id CType
       --  | CPackage Id [CArg] [CProp] Position [CLetDef]
        | CPackage Id [CArg] CPackageBody
        | COpen CExpr COpenArgs
        | CClass CClassArg Bool [CSign] -- should maybe rather be a CDef?
        | CInstance Id [CArg] CInstanceArg [CLetDef]

       --  | CDSign Id CType               -- Used only while type checking
         deriving (Eq, Ord,Show)




data CPackageBody =
       CPackageDef [CProp] Position [CLetDef]
     | CPackageInstance CExpr
    deriving (Eq, Ord,Show)



data CClause
        =   CClause [(Bool,CPat)] CExpr
         deriving (Eq, Ord,Show)

data CPatArg = CPatT Id CExpr
             | CPatId Id
           deriving (Eq, Ord,Show)

getCPatArgPos :: CPatArg -> Position
getCPatArgPos (CPatT x _) = getIdPosition x
getCPatArgPos (CPatId x) = getIdPosition x


data CPat
        = CPCon Id [CPat]
        | CPVar CPatArg
--        | CPAs Id CPat
--        | CPLit Position Literal
        deriving (Eq, Ord,Show)

cPatVar :: Id -> CPat
cPatVar x = CPVar (CPatId x)

getCPatPos :: CPat -> Position
getCPatPos (CPCon c _) = getIdPosition c
getCPatPos (CPVar x) = getCPatArgPos x

data CBind = CBind [Id] (Maybe CType)
        deriving (Eq, Ord,Show)

data CArg = CArg [(Bool,Id)] CType
        deriving (Eq, Ord,Show)

data CSign
        = CSign [Id] CType
        | CSignDef CDefn
--      | CSignType Id CArgs  ???
        deriving (Eq, Ord,Show)

data CClassArg = CClassArg Id CArgs CExpr CArgs deriving (Eq,Show,Ord)
data CInstanceArg = CInstanceArg CExpr deriving (Eq,Show,Ord)

data CDoBind
      = CDoBind Id CExpr
      | CDoBind_ CExpr
      | CDoLet [CLetDef]
         deriving (Eq, Ord,Show)


{- moved to Id
ppId :: PDetail -> Id -> IText
ppId d i =
    case getIdString i of
    s@(c:_) | isAlpha c || c == '_' -> t s
    s -> t ("("++s++")")

pprId :: Id -> String
pprId i = pIText (ppId PDReadable i)
-}

{-
ppConId :: PDetail -> Id -> IText
ppConId d i =
    (case getIdString i of
       s@(c:_) | isAlpha c -> t ('@':s)
       s -> t ('@':("("++s++")")))

-}

{- moved to Id
ppInfix :: PDetail -> Id -> IText
ppInfix d i =
    (case getIdString i of
      s@(c:_) | isAlpha c -> t("`"++s++"`")
      s -> t s)




idCDefn :: CDefn -> Maybe Id
idCDefn (CValueT c _ _ _) = Just c
idCDefn (CValueS c _ _ _) = Just c
--idCDefn (CValueP c _) = Just c
idCDefn (Ctype c _ _) = Just c
idCDefn (Cnewtype c _ _ _) = Just c
idCDefn (Cdata c _ _ _) = Just c
idCDefn (Cidata c _ _ _) = Just c
idCDefn (CValue c _) = Just c
idCDefn (CAxiom c _ _) = Just c
idCDefn (CNative c _) = Just c
idCDefn (CPackage c _ _) = Just c
idCDefn (COpen e as) = Nothing
idCDefn (CClass (CClassArg c _ _ _) _ _) = Just c
idCDefn (CInstance c _ _ _) = Just c
--idCDefn (CNative c _ _) = Just c
--idCDefn (CDSign c _) = Just c               -- Used only while type checking



idCDef :: CDef -> Maybe Id
idCDef (CDefComment _) = Nothing
idCDef (CDef ps d) = idCDefn d
-}

class Identifiers a where
    identifiers :: a -> [Id]


instance Identifiers CLetDef where
   identifiers (CSimple d) = identifiers d
   identifiers (CMutual ds) = concatMap identifiers ds
   identifiers _ = []


instance Identifiers CDef where
    identifiers (CDefComment _) = []
    identifiers (CDef _ d) = identifiers d


instance Identifiers CDefn where
    identifiers (CValueT c _ _ _) = [c]
    identifiers (CValueS c _ _ _) = [c]
    identifiers (Ctype c _ _) = [c]
    identifiers (Cnewtype c _ _ (c',_)) = [c,c']
    identifiers (Cdata c _ _ sums) = c:map fst sums
    identifiers (Cidata c _ _ sums) = c: (concatMap identifiers sums)
    identifiers (CValue c _) = [c]
    identifiers (CAxiom c _ _) = [c]
    identifiers (CNative c _) = [c]
    identifiers (CPackage c _ _) = [c]
    identifiers (COpen e as) = identifiers as
    identifiers (CClass (CClassArg c _ _ _) _ _) = [c]
    identifiers (CInstance c _ _ _) = [c]
    identifiers _ = []


instance Identifiers COpenArgs where
    identifiers (COpenArgs oas) = concatMap identifiers oas

instance Identifiers COArg where
    identifiers (COArgT _ c _) = [c]
    identifiers (COArg _ c) = [c]
    identifiers (COArgAs _ _ c) = [c]
    identifiers (COArgAsT _ _ _ c) = [c]


instance Identifiers CSign where
    identifiers (CSign is t) = is
    identifiers (CSignDef d) = []


instance Identifiers CIndSummand where
    identifiers (CIndExpl sum _ _) = [fst sum]
    identifiers (CIndImpl sum _) = [fst sum]

instance Identifiers CArg where
    identifiers (CArg xs e) = map snd xs


addModifiers :: [CProp] -> CDef -> CDef
addModifiers ps (CDef ps' ds)  = CDef (addMod' ps ps') ds
          where  addMod' [] ps = ps
                 addMod' (p:ps) ps' =
                    let ps2 = addMod' ps ps'
                    in if elem p ps2
                        then ps2
                        else case p of
                                Cabstract | elem Cconcrete ps' -> ps2
 --raise (noPosition,EConflictingModifiers (ppReadable p) "concrete")
                                Cconcrete | elem Cabstract ps' -> ps2
 --raise (noPosition,EConflictingModifiers (ppReadable p) "abstract")
                                Cpublic | elem Cprivate ps' -> ps2
 --raise (noPosition,EConflictingModifiers (ppReadable p) "private")
                                Cprivate |  elem Cpublic ps' -> ps2
--raise (noPosition,EConflictingModifiers (ppReadable p) "public")
                                _ -> (p:ps2)
addModifiers ps d = d

data CConstraint = CEq CExpr CExpr
                 | CJudg (CJudgement CExpr)

data CJudgement a =  CIsType a
                  | HasType a  CExpr
                  --deriving Show

precCExpr :: CExpr -> Int
precCExpr (CVar _) = 12
precCExpr (CStar _ _ _) = 12
precCExpr (CMeta _ _ _ _) = 12
precCExpr (CSelect _ _) = 12
precCExpr (CSum _) = 12
precCExpr (CIndSum _ _ ) = 12
precCExpr (CCConS _ ) = 12
precCExpr (CCCon _ _ ) = 12
precCExpr (CLit _ _) = 12
precCExpr (CBinOp _ op _) = prec $ getFixity op
precCExpr (CClos _ e) = precCExpr e
precCExpr (CArrow _ _ _) = 0
precCExpr (CUniv _ _) = 0
precCExpr (CDo _ _) = 0
precCExpr  (Cif _ _ _) = 1
precCExpr (CList _ _) = 12
precCExpr (CExternal _) = 12
precCExpr (CApply _ _) = 9
precCExpr _ = 8

type CMetaSubst = (Bool,MetaVar,CExpr)

-- Gives an approx. position
getCExprPos :: CExpr -> Position
getCExprPos e = case e of
    CVar n -> getIdPosition n
    CStar pos _ _  -> pos
    Clam as e -> getCExprPos e
    CUniv as e -> getCExprPos e
    CArrow _ e1 _ -> getCExprPos e1
    Clet _ e -> getCExprPos e
    CProduct pos _ -> pos
    CRecord _ pos _ -> pos
    Copen m _ _ -> getCExprPos m
    CSelect _ n -> getIdPosition n
    CSum [] -> noPosition
    CSum ((n,_):_) -> getIdPosition n
    CCCon n _  -> getIdPosition n
    CCConS n -> getIdPosition n
    Ccase e _ -> getCExprPos e
    CApply e _ -> getCExprPos e
    CBinOp e1 _ _ -> getCExprPos e1
    CMeta pos _ _ _ -> pos
    CClos _ e -> getCExprPos e
    Ccomment _ _ e -> getCExprPos e
    CPackageType  -> noPosition
    --CIndSum _ [] -> noPosition
    --CIndSum _ (((n,_),_):_) -> getIdPosition n
    CDo pos cbinds   -> pos
    CList pos _   -> pos
    CExternal plug -> pluginPos plug



boundVars :: CArg -> [Id]
boundVars (CArg hxs _) = map snd hxs

{-- ------------------- -}

instance Eq CExpr where
   (CVar x) == (CVar x') = x == x'
   (CStar _ i _) == (CStar _ i' _) = i == i'
   (Clam b e) == (Clam b' e') = b == b' && e == e'
   (CUniv b e) == (CUniv b' e') = b == b' && e == e'
   (CArrow b e1 e2) == (CArrow b' e1' e2') =  b == b' && e1 == e1'&& e2 == e2'
   (Clet ds e) == (Clet ds' e') = ds == ds' && e == e'
   (CProduct _ cs) == (CProduct _ cs') = cs == cs'
   (CRecord ps _ ds) == (CRecord ps' _ ds') = ps == ps' && ds == ds'
   (Copen e1 oas e2) == (Copen e1' oas' e2') = e1 == e1' && oas == oas' && e2 == e2'
   (CSelect e i) == (CSelect e' i') = e == e' && i == i'
   (CSum cs) == (CSum cs') = cs == cs'
   (CCCon i e) == (CCCon i' e') = e == e' && i == i'
   (CCConS i) == (CCConS i') = i == i'
   (Ccase e as) == (Ccase e' as') = e == e' && as == as'
   (CApply e es) == (CApply e' es') = e == e' && es == es'
   (CBinOp e1 i e2) == (CBinOp e1' i' e2') =  i == i' && e1 == e1'&& e2 == e2'
   (CMeta _ _ _ m) == (CMeta _ _ _ m') = m == m'
   (Ccomment _ _ e) == (Ccomment _ _ e') = e == e'
   CPackageType  ==  CPackageType = True
   (CExternal p) == (CExternal p') = p == p'
   (CIndSum as cs) == (CIndSum as' cs') = as == as' && cs == cs'
   (Cif e1 e2 e3) == (Cif e1' e2' e3') = e1 == e1' && e2 == e2' && e3 == e3'
   (CLit _ l) == (CLit _ l') = l == l'
   (CDo _ bs) == (CDo _ bs') = bs == bs'
   (CList _ es) == (CList _ es') = es == es'

   _ == _ = False



substNaiveCExpr :: [(CExpr,Id)] -> CExpr -> CExpr
substNaiveCExpr subst e = sub e
   where sub e = maybe (sub' e) CVar (lookup e subst)
         sub' (Clam bs e) = Clam bs (sub e)
         sub' (CUniv bs e) = CUniv bs (sub e)
         sub' (CArrow b e1 e2) = CArrow b (sub e1) (sub e2)
         sub' (CSelect e i) = CSelect (sub e) i
         sub' (CApply e es) = CApply (sub e) (map (\(h,e') -> (h,sub e'))  es)
         sub' (CBinOp e1 op e2) = CBinOp (sub e1) op (sub e2)
         sub' (Cif b te fe) = Cif (sub b) (sub te) (sub fe)
         sub' (CList p l) = CList p (map sub l)
         sub' e = e
