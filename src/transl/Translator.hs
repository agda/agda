-- Translator from Agda 1 to Agda 2
--
-- $Id: Translator.hs,v 1.6 2006/11/07 12:23:53 ulfn Exp $
--

module Translator where

import Control.Monad.State
import Data.Char
import Data.List
import Data.Maybe
import Debug.Trace
import System
import System.IO

-- Agda
import Position
import Id
import Monads
import Error
import Parse
import qualified NewCParser as New
import qualified OldCParser as Old
import Lex
import CSyntax
import FString
import PreStrings

-- Agda 2
import Utils.Pretty
import Syntax.Common
import Syntax.Concrete
import Syntax.Concrete.Pretty
import Syntax.Literal
import Syntax.Position

----------------------------------------------------------------------
-- Interfaces
----------------------------------------------------------------------

agda1Lexer :: Bool -> FilePath -> String -> [Token]
agda1Lexer alfa file = lexStart alfa file preStrTable 

agda1Parser :: Bool -> [Token] -> Error ([CLetDef],StrTable)
agda1Parser True  = New.finalP New.pLetDefs
agda1Parser False = Old.finalP Old.pLetDefs

agda1to2 :: ([CLetDef] -> StrTable -> IO ())
         -> Error ([CLetDef],StrTable) -> IO ()
agda1to2 _  (Err e) = hPutStrLn stderr $ prEMsg e
agda1to2 io (Done (ctree,tab)) = io ctree tab


----------------------------------------------------------------------
-- normalise functions from Agda 1 to Agda 1
----------------------------------------------------------------------

-- eliminate top level lambda abstraction ----------------------------

elimTopLam :: CLetDef -> CLetDef
elimTopLam = mapCLetDef elimTopLamCDef

elimTopLamCDef :: CDef -> CDef
elimTopLamCDef (CDef props cdefn) = CDef props $ elimTopLamCDefn cdefn
elimTopLamCDef def                = def

elimTopLamCDefn :: CDefn -> CDefn
elimTopLamCDefn (CValueS i args ty clause)
 = CValueS i args ty (elimLamCClause clause)
elimTopLamCDefn defns = defns

elimLamCClause :: CClause -> CClause
elimLamCClause (CClause pats (Clam (flg,CBind [i] mctype) cexpr))
 = elimLamCClause (CClause (pats++[pat]) (elimLamCExpr cexpr))
   where pat = case mctype of
                 Nothing -> (flg,CPVar (CPatId i))
                 Just e  -> (flg,CPVar (CPatT i e))
elimLamCClause cclause = cclause

elimLamCExpr :: CExpr -> CExpr
elimLamCExpr (Clam b e)
 = Clam b (elimLamCExpr e)
elimLamCExpr (Clet defs e)
 = Clet (map elimTopLam defs) (elimLamCExpr e)
elimLamCExpr (Ccase e arms) 
 = Ccase e [(pat,elimLamCExpr expr) | (pat,expr) <- arms]
elimLamCExpr (CApply f args)
 = CApply (elimLamCExpr f) [(b,elimLamCExpr e) | (b,e) <- args]
elimLamCExpr e = e

-- eliminate top level case 

elimTopCase :: CLetDef -> [CLetDef]
elimTopCase = (:[])                       -- do nothing

convCase :: CLetDef -> State StrTable [CLetDef]
convCase = return . (:[])                 -- do nothing

-- replace free occurrence of "x" with CExpr -------------------------

substdfn :: Id -> CExpr -> Bool -> CLetDef -> (Bool,CLetDef)
substdfn i new True ldf = (True,ldf)
substdfn i new _    ldf = substLetDef i new ldf

substLetDef :: Id -> CExpr -> CLetDef -> (Bool,CLetDef)
substLetDef i new ld@(CSimple d)
 = case substcdef i new d of
     (b,d') -> (b,CSimple d')    
substLetDef i new ld@(CMutual ds)
 = case unzip $ map (substcdef i new) ds of
     (bs,ds') -> if or bs then (True,CMutual ds) else (False,CMutual ds')
substLetDef _ _ ld = (False,ld)

substcdef :: Id -> CExpr -> CDef -> (Bool,CDef)
substcdef i new (CDef cprops cdefn) 
 = case substcdefn i new cdefn of
     (b,cdefn') -> (b,CDef cprops cdefn')
substcdef i new cdef = (False,cdef)

substcdefn :: Id -> CExpr -> CDefn -> (Bool,CDefn)
substcdefn i new (CValueS i' cargs ctype cclause)
 = (i == i', CValueS i' cargs ctype $ substcclause i new cclause)
substcdefn _ _ cdefn = (False, cdefn)

substcclause :: Id -> CExpr -> CClause -> CClause
substcclause i new (CClause bcps cexpr)
 = if elem i (concatMap (exid . snd) bcps) 
      then CClause bcps cexpr
      else CClause bcps (substcexpr i new cexpr)

   where exid (CPCon i cpats) = i : concatMap exid cpats
         exid (CPVar (CPatT i _)) = [i]
         exid (CPVar (CPatId i))  = [i]

substcexpr :: Id -> CExpr -> CExpr -> CExpr
substcexpr i new (CVar x)
 | i == x         = new
substcexpr i new (Clam b@(_,CBind is _) e)
 | notElem i is   = Clam b (substcexpr i new e)
substcexpr i new (Clet dfs e)
 = case mapAccumL (substdfn i new) False dfs  of
     (True, dfs') -> Clet dfs' e
     (_   , dfs') -> Clet dfs' (substcexpr i new e)
substcexpr i new (Ccase e arms)
 = Ccase (substcexpr i new e) [(pat,substcexpr i new expr) | (pat,expr) <- arms]
substcexpr i new (CApply f args)
 = CApply (substcexpr i new f) [(b,substcexpr i new x) | (b,x) <- args ]
substcexpr _ _  e = e

exchcpat :: CPat -> Int -> [(Bool,CPat)] -> [(Bool,CPat)]
exchcpat pat i cpats
 = case splitAt i cpats of
     (xs,y:ys) -> xs++(fst y, pat):ys
     _         -> error "exchcpat: impossible pattern"

-- Kludge!
-- CValueT --> CValueS ; not valid in Agda

valueT2valueS :: CLetDef -> CLetDef
valueT2valueS = mapCLetDef t2sCDef

t2sCDef :: CDef -> CDef
t2sCDef (CDef props cdefn) = CDef props $ t2sCDefn cdefn
t2sCDef def                = def

t2sCDefn :: CDefn -> CDefn
t2sCDefn (CValueT i args ctype cexpr)
 = CValueS i args ctype (CClause [] $ t2sCExpr cexpr)
t2sCDefn cdefn = cdefn

t2sCExpr :: CExpr -> CExpr
t2sCExpr (CUniv arg expr) = CUniv arg (t2sCExpr expr)
t2sCExpr (Clam bnd expr)  = Clam bnd (t2sCExpr expr)
t2sCExpr (Clet defs expr) = Clet (map valueT2valueS defs) (t2sCExpr expr)
t2sCExpr (CProduct pos signs) = CProduct pos $ map t2sCSign signs
t2sCExpr (CRecord props pos defs) = CRecord props pos $ map valueT2valueS defs
t2sCExpr (CSelect expr i) = CSelect (t2sCExpr expr) i
t2sCExpr (Ccase expr arms) = Ccase (t2sCExpr expr) [(pat,t2sCExpr e)| (pat,e) <- arms]
t2sCExpr (CApply expr args) = 
  case expr of
    (CVar i) | isSym (head (getIdString i))
             -> CApply (CBinOp (snd $ head args) i (snd $ head $ tail  args))
                       [(flg,t2sCExpr e) | (flg,e) <- tail (tail args)]
    _        -> CApply (t2sCExpr expr) [(flg,t2sCExpr e) | (flg,e) <- args ]
t2sCExpr (CBinOp e1 op e2) = CBinOp (t2sCExpr e1) op (t2sCExpr e2)
t2sCExpr (Cif e0 e1 e2) = Cif (t2sCExpr e0) (t2sCExpr e1) (t2sCExpr e2)
t2sCExpr (CDo pos dbnds) = CDo pos $ map t2sCDoBind dbnds
t2sCExpr (CList pos exprs) = CList pos $ map t2sCExpr exprs
t2sCExpr cexpr             = cexpr

t2sCSign :: CSign -> CSign
t2sCSign (CSignDef defn) = CSignDef (t2sCDefn defn)
t2sCSign csign = csign

t2sCDoBind :: CDoBind -> CDoBind
t2sCDoBind (CDoBind i expr) = CDoBind i (t2sCExpr expr)
t2sCDoBind (CDoBind_ expr) = CDoBind_ (t2sCExpr expr)
t2sCDoBind (CDoLet defs) = CDoLet (map valueT2valueS defs)

----------------------------------------------------------------------
-- translator from Agda1 definition syntax to Agda2 declaration syntax
----------------------------------------------------------------------

translate :: [CLetDef] -> [Declaration]
translate = concatMap transCLetDef

transCLetDef :: CLetDef -> [Declaration]
transCLetDef (CSimple cdef)  = transCDef cdef
transCLetDef (CMutual cdefs) = [Mutual noRange (concatMap transCDef cdefs)]
transCLetDef (CLetDefComment cs)
 | not ("--#include" `isPrefixOf` cs) = []
 | otherwise = maybe []
                     (\ md -> [Import noRange
 				    (QName (Name noRange [Id noRange md]))
 				    Nothing
				    DontOpen
 				    (ImportDirective noRange (Hiding []) [] False) ])
                     mdlname
   where 
     trim str = case break ('\"'==) str of 
                    (_,[])   -> Nothing
                    (_,_:xs) -> Just xs
     mdlname = trim cs >>= trim . reverse >>= return . takeWhile ('.'/=) . reverse . takeWhile ('/'/=)

transCDef :: CDef -> [Declaration]
transCDef (CDef cprops cdefn)
  | elem Cprivate  cprops = [Private  noRange (transCDefn cdefn)]
  | elem Cabstract cprops = [Abstract noRange (transCDefn cdefn)]
  | otherwise             = transCDefn cdefn
transCDef _               = []

transCDefn :: CDefn -> [Declaration]
transCDefn (CValueT i args ctype cexpr)
 = transCDefn (CValueS i args ctype (CClause [] cexpr))
transCDefn (CValueS i [] ctype cclause) 
 = ctype2typesig flg i [] ctype : cclause2funclauses i flg cclause
   where flg = isInfixOp i
transCDefn (CValueS i args ctype cclause) 
 = transCDefn (CValueS i [] ctype' cclause)
   where ctype' = foldr (\ carg e -> CUniv carg e) ctype args
transCDefn (Ctype i args ctype) 
 = transCDefn (CValueT i args (CStar undefined 0 undefined) ctype)
transCDefn (Cnewtype i args ctype csum) 
 = transCDefn (Cdata i args (Just ctype) [csum])
transCDefn (Cdata i args mctype csums)
 = [Data noRange (id2name i) tls t (map (csummand2constructor ot) csums)]
   where
    t = maybe (Set noRange) transCExpr mctype 
    tls = concatMap carg2telescope args
    n = id2name i
    ot = foldl (\ f (TypedBindings _ _ [TBind _ [x] _]) -> RawApp noRange [f, Ident (QName x)]) (Ident (QName n)) tls
transCDefn (Cidata i args ctype csum)
-- = transCDefn (Cdata i args (Just ctype) (sind2s csum))
 = errorDecls "transCDefn: cannot translate: (Cidata i args ctype csum)"
transCDefn (CValue i cexpr)
 = cclause2funclauses i (isInfixOp i) (CClause [] cexpr)
transCDefn (CAxiom i args ctype)
 = [Postulate noRange [ctype2typesig flg i [] ctype']]
   where ctype' = foldr (\ carg e -> CUniv carg e) ctype args
         flg = isInfixOp i
transCDefn (CNative i ctype)
 = errorDecls "transCDefn: cannot translate: (CNative i ctype)"
transCDefn (CPackage i args pkgbody)
 = case pkgbody of
     CPackageDef [] _ cletdefs 
       -> [Module noRange (QName (id2name i)) (concatMap carg2telescope args)
	   (concatMap transCLetDef cletdefs)]
     _ -> errorDecls "Cannot translate: package definition other than (CPackageDef [] _ cletdefs)"
transCDefn (COpen cexpr (COpenArgs coargs))
 = case cexpr of
     (CVar i)
       -> [Open noRange (QName (id2name i)) (copenargs2importdirective coargs)]
     (CApply (CVar i) bces)
       -> [Open noRange (QName (id2name i)) (copenargs2importdirective coargs)]
     _ -> errorDecls ("cannot translate: COpen ("++show cexpr++") coargs")
transCDefn (CClass classargs b csigns)
 = errorDecls "transCDefn: cannot translate: (CClass classargs b csigns)"
transCDefn (CInstance i cargs cinsarg cletdefs)
 = errorDecls "transCDefn: cannot translate: (CInstance i cargs cinsarg cletdefs)"


-- Utilities

mkInfixName :: Id -> Name
mkInfixName i = Name noRange [Hole,Id noRange (getIdString i),Hole]

mkInfixName' :: Id -> Name
mkInfixName' i = Name noRange [Id noRange (getIdString i)]

ctype2typesig :: InfixP -> Id -> CArgs -> CType -> Declaration
ctype2typesig flg i args ctype
  | flg = TypeSig (mkInfixName i) ys   
  | otherwise = TypeSig (id2name i) ys
  where xs = concatMap (\ (CArg bns ct) -> bns) args
        ys = foldr (\ (b,i) e -> Fun noRange ((if b then HiddenArg noRange . unnamed else id) (Ident $ QName $ id2name i)) e)
		   (transCExpr ctype) xs

carg2telescope :: CArg -> Telescope
carg2telescope (CArg bis ctype)
  = map (\ (b,i) -> TypedBindings noRange (bool2hiding b) [TBind noRange [id2name i] (transCExpr ctype)]) bis

csummand2constructor :: Expr -> CSummand -> Constructor
csummand2constructor otype (i,cargs)
 = TypeSig (id2name i)
 $ foldr (\ (b,i,t) e -> Fun noRange (transCExpr t) e) otype (concatMap excargs cargs)

copenargs2importdirective :: [COArg] -> ImportDirective
copenargs2importdirective coargs 
 = case unzip $ map coarg2urm coargs of
     (ns, rns) -> ImportDirective noRange (Using (map ImportedName (catMaybes ns)))
                                             (catMaybes rns) False
  where coarg2urm (COArgT _ i t)     = (Just $ id2name i,Nothing)
        coarg2urm (COArg _ i)        = (Just $ id2name i,Nothing)
        coarg2urm (COArgAs _ i j)    = (Nothing,Just (ImportedName $ id2name i,id2name j))
        coarg2urm (COArgAsT _ i t j) = (Nothing,Just (ImportedName $ id2name i,id2name j))

-- Translator from Agda1 expression syntax to Agda2 expression syntax

transCExpr :: CExpr -> Expr
transCExpr (CVar i)
 = Ident (QName (id2name i))
transCExpr (CStar _ 0 _)
 = Set noRange
transCExpr (CStar _ n _)
 = SetN noRange n
transCExpr (Clam (flg,CBind [x] Nothing) e)
 = Lam noRange [DomainFree (bool2hiding flg) (id2name x)] (transCExpr e)
transCExpr (Clam (flg,CBind xs (Just t)) e)
 = Lam noRange [DomainFull (TypedBindings noRange (bool2hiding flg) [TBind noRange (map id2name xs) (transCExpr t)])] (transCExpr e)
transCExpr (CUniv a e)
 = case a of
     (CArg bis ctype)
       -> foldr (\ (b,i) expr -> Pi [TypedBindings noRange (bool2hiding b) [TBind noRange [(id2name i)] (transCExpr ctype)]] expr) (transCExpr e) bis 
transCExpr (CArrow flg ce1 ce2)
 = Fun noRange (parenExpr (transCExpr ce1)) (transCExpr ce2)
transCExpr (Clet defs cexpr) 
 = Let noRange (translate defs) (transCExpr cexpr)
transCExpr ce@(CProduct pos csigs)
 = errorExpr $ "Cannot translate (" ++ show ce ++")"
transCExpr ce@(CRecord cprops pos cletdefs)
 = errorExpr $ "Cannot translate (" ++ show ce ++")"
transCExpr ce@(Copen cexpr1 coargs cexpr2)
 = errorExpr $ "Cannot translate (" ++ show ce ++")"
transCExpr (CApply f args)
 = case f of
    (CVar i) | isSym (head (getIdString i)) 
             -> transCExpr $
                CApply (CBinOp (snd $ head args) i (snd $ head $ tail  args))
                       [(flg,t2sCExpr e) | (flg,e) <- tail (tail args)]
    _        -> foldl (\ e (flg,cexpr) -> App noRange e
                       (Arg { argHiding =(bool2hiding flg), unArg = unnamed (parenExpr (transCExpr cexpr)) }))
                (parenExpr (transCExpr f))
	        args
transCExpr (CBinOp o1 b o2)
 | isSym (head (getIdString b)) = OpApp noRange (mkInfixName b) (map (parenExpr . transCExpr) [o1,o2])
 | otherwise = transCExpr (CApply (CVar b) [(False,o1),(False,o2)])

transCExpr (CMeta _ _ _ _)
 = QuestionMark noRange Nothing
transCExpr (Cif ec et ee)
 = RawApp noRange (Ident ifQName : map (parenExpr . transCExpr) [ec,et,ee])
transCExpr (CCConS i) = transCExpr (CVar i)
-- transCExpr ce
-- = errorExpr ("Cannot translate ("++ show ce ++")")
-- = notyet $ "transCExpr ("++show ce++")"



ifQName :: QName
ifQName = str2qname "iF"

excargs :: CArg -> [(Bool,Id,CType)]
excargs (CArg bis ctype) = [ (b,i,ctype) | (b,i) <- bis ]

parenExpr :: Expr -> Expr
parenExpr e@(Ident _)          = e
parenExpr e@(Lit _)            = e
parenExpr e@(QuestionMark _ _) = e
parenExpr e@(Underscore _ _)   = e
parenExpr e@(Set _)            = e
parenExpr e@(Prop _)           = e
parenExpr e@(SetN _ _)         = e
parenExpr e                    = Paren noRange e

-- Utilities

---- for non-supported translation 

errorDecls :: String -> [Declaration]
errorDecls msg 
 = [TypeSig (Name noRange [Id noRange "<error>"])
    (Ident (str2qname msg))
   ]

errorExpr :: String -> Expr
errorExpr s = Lit (LitString noRange ("<error> : " ++ s))

str2qname :: String -> QName
str2qname s = QName (Name noRange [Id noRange s])

----

isInfixOp :: Id -> Bool
isInfixOp = all (not . isAlphaNum) . getIdString

id2name :: Id -> Name
id2name i
    | isSym (head (getIdString i)) = mkInfixName' i
    | otherwise			   = Name noRange [Id noRange (getIdString i)]

bool2hiding :: Bool -> Hiding
bool2hiding True = Hidden
bool2hiding _    = NotHidden

bool2isinfix :: Bool -> IsInfix
bool2isinfix True = InfixDef
bool2isinfix _    = PrefixDef

type InfixP = Bool

cclause2funclauses
 :: Id -> InfixP -> CClause -> [Declaration]
cclause2funclauses i flg (CClause cpats expr)
 | isCcase  expr = liftCcase i flg cpats expr
--  | isCBinOp expr
--      = [FunClause (RawAppP noRange (intersperse op pats)) 
-- 		              (RHS (transCExpr expr))
-- 		              (localdefs expr)]
 | flg
     = [FunClause (LHS (RawAppP noRange (intersperse op pats)) [] [])
		  (RHS (transCExpr expr))
                  (localdefs expr)]
 | otherwise = [FunClause (LHS (RawAppP noRange (op : pats)) [] [])
	                  (RHS (transCExpr expr))
		          (localdefs expr)]
  where twoargs = 2 == length cpats
        op  = IdentP $ str2qname $ getIdString i
        pats = map (parenPattern . 
                    (\(b, p) -> if b == Hidden
                                  then HiddenP noRange $ unnamed p
                                  else p)) (map cpat2pat cpats)

cclause2funclause _ _ = error "Never apply cclause2funclause any but CClause"

localdefs :: CExpr -> WhereClause
localdefs cexpr = NoWhere

isCcase :: CExpr -> Bool
isCcase (Ccase _ _) = True
isCcase _           = False

isCBinOp :: CExpr -> Bool
isCBinOp (CBinOp _ _ _) = True
isCBinOp _              = False

liftCcase :: Id -> Bool -> [(Bool,CPat)] -> CExpr -> [Declaration]
liftCcase n flg pats (Ccase cexpr ccasearms)
  = case cexpr of
      CVar x -> case within x (zip [0..] pats) of
                  Just iv
                    -> case ccasearms of
                         [] -> absurdcc n flg pats iv
                         _  -> concatMap (liftcc n flg pats iv) ccasearms
                  _ -> error (show cexpr ++ " not in args")
      _      -> errorDecls "now liftCcase pats can be applied on simple variable"
    where
      within x ((i,(_,CPVar (CPatId x'))):_)  | x == x' = Just i
      within x ((i,(_,CPVar (CPatT x' _))):_) | x == x' = Just i
      within x (_:ps)                                   = within x ps
      within _ _                                        = Nothing
      liftcc n flg pats i (pat,expr@(Ccase e arms))
       = liftCcase n flg (exchcpat pat i pats) expr'
         where expr' = substcexpr x (cpat2cexpr pat) expr
               x = case cexpr of {CVar v -> v; _ -> error "Never"}
      liftcc n flg pats i (pat,expr)
             | flg = [FunClause (LHS (RawAppP noRange (intersperse (IdentP (QName (id2name n))) (cpat2pattern pat i pats))) [] [])
                                (RHS (transCExpr expr')) (localdefs expr')]
             | otherwise = [FunClause (LHS (RawAppP noRange (IdentP (QName (id2name n)):cpat2pattern pat i pats)) [] [])
                                      (RHS (transCExpr expr')) (localdefs expr')]
         where expr' = substcexpr x (cpat2cexpr pat) expr
               x = case cexpr of {CVar v -> v; _ -> error "Never"}
      absurdcc n flg pats i
             | flg = [FunClause (LHS (RawAppP noRange (intersperse (IdentP (QName (id2name n))) [abpat])) [] [])
                                AbsurdRHS NoWhere]
             | otherwise = [FunClause (LHS (RawAppP noRange (IdentP (QName (id2name n)):[abpat])) [] [])
                                      AbsurdRHS NoWhere]
         where abpat = AbsurdP noRange
liftCcase _ _ _ _ = error "Never apply liftCcase to any but Ccase"

cpat2cexpr :: CPat -> CExpr
cpat2cexpr (CPCon i pats) = CApply (CVar i) (map ((,) False . cpat2cexpr) pats)
cpat2cexpr (CPVar (CPatT i _)) = CVar i
cpat2cexpr (CPVar (CPatId i )) = CVar i

cpat2pattern :: CPat -> Int -> [(Bool,CPat)] -> [Pattern]
cpat2pattern pat i cpats
 = map (\(b, p) -> if b == Hidden 
                      then HiddenP noRange $ unnamed p
                      else p) $ map cpat2pat $ exchcpat pat i cpats

cpat2arg :: (Bool,CPat) -> Arg Pattern
cpat2arg bcpat = uncurry Arg $ cpat2pat bcpat

cpat2pat :: (Bool,CPat) -> (Hiding, Pattern)
cpat2pat (flg,CPVar (CPatId i))
 = (bool2hiding flg,IdentP (QName (id2name i)))
cpat2pat (flg,CPVar (CPatT i _))
 = (bool2hiding flg,IdentP (QName (id2name i)))
cpat2pat (flg,CPCon i pats)
 = (h
   , parenPattern 
   $ foldl (\ p a -> RawAppP noRange [p, (snd $ cpat2pat (flg, a))])
           (IdentP (QName (id2name i))) 
           pats
   )
   where h = bool2hiding flg

parenPattern :: Pattern -> Pattern
parenPattern (AppP p1 p2) = ParenP noRange (AppP p1' (Arg {argHiding = argHiding p2, unArg = unnamed p2'}))
  where [p1',p2'] = map parenPattern [p1,namedThing $ unArg p2]
parenPattern (OpAppP r n ps) = ParenP r (OpAppP r n ps')
  where ps' = map parenPattern ps
parenPattern (RawAppP r ps) = ParenP r (RawAppP r ps')
  where ps' = map parenPattern ps
parenPattern p = p

-- Dummy

