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
import System.Environment
import System.IO
import System.IO.Unsafe

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
import Literal
import PPrint
import CPrinter

-- Agda 2
import Agda.Utils.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.Literal
import Agda.Syntax.Position

starling :: (a -> b -> c) -> (a -> b) -> (a -> c)
starling f g x = f x (g x)

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
agda1to2 _  (Err e)            = hPutStrLn stderr $ prEMsg e
agda1to2 io (Done (ctree,tab)) = io ctree tab


----------------------------------------------------------------------
-- normalise functions from Agda 1 to Agda 1
----------------------------------------------------------------------

-- eliminate top level lambda abstraction ----------------------------

elimTopLam :: CLetDef -> CLetDef
elimTopLam = mapCLetDef elimTopLamCDef

elimTopLamCDef :: CDef -> CDef
elimTopLamCDef cdef = case cdef of
  CDef props cdefn -> CDef props $ elimTopLamCDefn cdefn
  _                -> cdef

elimTopLamCDefn :: CDefn -> CDefn
elimTopLamCDefn cdefn = case cdefn of
  CValueS i args ty clause -> CValueS i args ty (elimLamCClause clause)
  _                        -> cdefn

elimLamCClause :: CClause -> CClause
elimLamCClause cclause = case cclause of
  CClause pats (Clam (flg,CBind [i] mctype) cexpr)
    -> elimLamCClause (CClause (pats++[pat]) (elimLamCExpr cexpr))
         where pat = case mctype of
                 Nothing -> (flg,CPVar (CPatId i))
                 Just e  -> (flg,CPVar (CPatT i e))
  _ -> cclause

elimLamCExpr :: CExpr -> CExpr
elimLamCExpr ce = case ce of
  Clam b e        -> Clam b (elimLamCExpr e)
  Clet defs e     -> Clet (map elimTopLam defs) (elimLamCExpr e)
  Ccase e arms    -> Ccase e [(pat,elimLamCExpr expr) | (pat,expr) <- arms]
  CApply f args   -> CApply (elimLamCExpr f) [(b,elimLamCExpr e) | (b,e) <- args]
  _               -> ce

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
substLetDef i new ld = case ld of
  CSimple d  -> case substcdef i new d of
		  (b,d') -> (b,CSimple d')
  CMutual ds -> case unzip $ map (substcdef i new) ds of
                  (bs,ds') -> if or bs then (True,CMutual ds) else (False,CMutual ds')
  _          -> (False,ld)

substcdef :: Id -> CExpr -> CDef -> (Bool,CDef)
substcdef i new cdef = case cdef of
  CDef cprops cdefn -> case substcdefn i new cdefn of
		         (b,cdefn') -> (b,CDef cprops cdefn')
  _                 -> (False,cdef)

substcdefn :: Id -> CExpr -> CDefn -> (Bool,CDefn)
substcdefn i new cdefn = case cdefn of
  CValueS i' cargs ctype cclause
    -> (i == i', CValueS i' cargs ctype $ substcclause i new cclause)
  _ -> (False, cdefn)

substcclause :: Id -> CExpr -> CClause -> CClause
substcclause i new (CClause bcps cexpr)
 = if elem i (concatMap (exid . snd) bcps)
      then CClause bcps cexpr
      else CClause bcps (substcexpr i new cexpr)
   where exid (CPCon i cpats) = i : concatMap exid cpats
         exid (CPVar (CPatT i _)) = [i]
         exid (CPVar (CPatId i))  = [i]

substcexpr :: Id -> CExpr -> CExpr -> CExpr
substcexpr i new ce = case ce of
  CVar x | i == x  -> new
  Clam b@(_,CBind is _) e
    | notElem i is -> Clam b (substcexpr i new e)
  Clet dfs e       -> case mapAccumL (substdfn i new) False dfs  of
                        (True, dfs') -> Clet dfs' e
                        (_   , dfs') -> Clet dfs' (substcexpr i new e)
  Ccase e arms     -> Ccase (substcexpr i new e)
                            [(pat,substcexpr i new expr) | (pat,expr) <- arms]
  CApply f args    -> CApply (substcexpr i new f) [(b,substcexpr i new x) | (b,x) <- args ]
  CBinOp e1 o e2   -> CBinOp (substcexpr i new e1) o (substcexpr i new e2)
  _                -> ce

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
t2sCDef cdef = case cdef of
  CDef props cdefn -> CDef props $ t2sCDefn cdefn
  _                -> cdef

t2sCDefn :: CDefn -> CDefn
t2sCDefn cdefn = case cdefn of
  CValueT i args ctype cexpr -> CValueS i args ctype (CClause cpats $ t2sCExpr cexpr)
                                  where cpats = concatMap carg2bcpat args
                                        carg2bcpat (CArg bis _) = map f bis
                                        f (b,i) = (b, CPVar (CPatId i))
  _                          -> cdefn

t2sCExpr :: CExpr -> CExpr
t2sCExpr ce = case ce of
  CUniv arg expr   -> CUniv arg (t2sCExpr expr)
  Clam bnd expr    -> Clam bnd (t2sCExpr expr)
  Clet defs expr   -> Clet (map valueT2valueS defs) (t2sCExpr expr)
  CProduct pos signs
                   -> CProduct pos $ map t2sCSign signs
  CRecord props pos defs
                   -> CRecord props pos $ map valueT2valueS defs
  CSelect expr i   -> CSelect (t2sCExpr expr) i
  Ccase expr arms  -> Ccase (t2sCExpr expr) [(pat,t2sCExpr e)| (pat,e) <- arms]
  CApply expr args -> case expr of
			CVar i | isSym (head $ getIdString i)
		          -> CApply (CBinOp (snd $ head args) i (snd $ head $ tail  args))
                                    [(flg,t2sCExpr e) | (flg,e) <- tail (tail args)]
                        _ -> CApply (t2sCExpr expr) [(flg,t2sCExpr e) | (flg,e) <- args ]
  CBinOp e1 op e2  -> CBinOp (t2sCExpr e1) op (t2sCExpr e2)
  Cif e0 e1 e2     -> Cif (t2sCExpr e0) (t2sCExpr e1) (t2sCExpr e2)
  CDo pos dbnds    -> CDo pos $ map t2sCDoBind dbnds
  CList pos exprs  -> CList pos $ map t2sCExpr exprs
  _                -> ce

t2sCSign :: CSign -> CSign
t2sCSign csign = case csign of
  CSignDef defn -> CSignDef (t2sCDefn defn)
  _             -> csign

t2sCDoBind :: CDoBind -> CDoBind
t2sCDoBind cdobind = case cdobind of
  CDoBind i expr -> CDoBind i (t2sCExpr expr)
  CDoBind_ expr  -> CDoBind_ (t2sCExpr expr)
  CDoLet defs    -> CDoLet (map valueT2valueS defs)

----------------------------------------------------------------------
-- translator from Agda1 definition syntax to Agda2 declaration syntax
----------------------------------------------------------------------

translate :: [CLetDef] -> [Declaration]
translate = concatMap transCLetDef

transCLetDef :: CLetDef -> [Declaration]
transCLetDef cletdef = case cletdef of
  CSimple cdef  -> transCDef cdef
  CMutual cdefs -> [Mutual noRange (concatMap transCDef cdefs)]
  CLetDefComment cs
    | not ("--#include" `isPrefixOf` cs)
                -> commentDecls cs
    | otherwise -> maybe []
                     (\ md -> [Import noRange
 		                      (QName (Name noRange [Id md]))
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
transCDefn cdefn = case cdefn of
  CValueT i args ctype cexpr
    -> transCDefn (CValueS i args ctype (CClause cpats cexpr))
         where cpats = concatMap carg2bcpat args
               carg2bcpat (CArg bis _) = map f bis
	       f (b,i) = (b, CPVar (CPatId i))
  CValueS i [] ctype cclause@(CClause cpats cexpr)
    -> case cexpr of
         CProduct pos csigs
           -> case ctype of
                CUniv carg e
                  -> [Record noRange name
                             (carg2telescope carg)
                             (transCExpr e)
                             (concatMap csig2fields csigs)]
                CStar _ 0 _
                  -> [Record noRange name [] (Set noRange) (concatMap csig2fields csigs)]
                CStar _ n _
                  -> [Record noRange name [] (SetN noRange $ fromIntegral n) (concatMap csig2fields csigs)]
                _ -> errorDecls $ pp "" cdefn
         CRecord cprops pos cletdefs
           -> ctype2typesig flg i [] ctype
           :  [FunClause (LHS (RawAppP noRange (op : pats)) [] [] [])
                         (RHS (Rec noRange $ map decls2namexpr decls))
                         (localdefs undefined)]
               where
                 decls = map transCLetDef cletdefs
                 op  = IdentP $ str2qname $ getIdString i
	         pats = ctype2pats ctype
         _ -> ctype2typesig flg i [] ctype : cclause2funclauses i flg cclause
       where flg = isInfixOp i
             name = if flg then id2infixName i else id2name i
  CValueS i args ctype cclause
    -> transCDefn (CValueS i [] ctype' cclause)
       where ctype' = foldr (\ carg e -> CUniv carg e) ctype args
  Ctype i args ctype
    -> transCDefn (CValueT i args (CStar undefined 0 undefined) ctype)
  Cnewtype i args ctype csum
    -> transCDefn (Cdata i args (Just ctype) [csum])
  Cdata i args mctype csums
    -> [Data noRange Inductive n tls t (map (csummand2constructor ot) csums)]
       where
        t = maybe (Set noRange) transCExpr mctype
        tls = concatMap carg2telescope args
        n = id2name i
        ot = foldl (\ f (TypedBindings _ _ [TBind _ [BName x _] _]) -> RawApp noRange [f, Ident (QName x)]) (Ident (QName n)) tls
  Cidata i args ctype cindsums
    -> if not (isLastSet ctype) || any (not . isSet) args then errorDecls $ pp "" cdefn
       else -- errorDecls $ pp (show cdefn) cdefn
            [Data noRange Inductive n (concatMap carg2telescope args) (transCExpr ctype) (mapMaybe cindsum2constructor cindsums)]
       where
         isLastSet (CStar _ 0 _)   = True
         isLastSet (CUniv ca cty)  = not (isSet' ca) && isLastSet cty
         isLastSet _               = False
         isSet (CArg bis (CStar _ 0 _)) = not (any fst bis)
         isSet _                        = False
         isSet' (CArg _ (CStar _ _ _))  = True
         isSet' _                       = False
         n = id2name i
  CValue i cexpr
    -> cclause2funclauses i (isInfixOp i) (CClause [] cexpr)
  CAxiom i args ctype
    -> [Postulate noRange [ctype2typesig flg i [] ctype']]
       where ctype' = foldr (\ carg e -> CUniv carg e) ctype args
             flg = isInfixOp i
  CNative i ctype
    -> errorDecls $ pp "" cdefn
  CPackage i args pkgbody
    -> case pkgbody of
         CPackageDef [] _ cletdefs
           -> [Module noRange (QName (id2name i)) (concatMap carg2telescope args)
	       (concatMap transCLetDef cletdefs)]
         _ -> errorDecls $ pp "" cdefn
  COpen cexpr (COpenArgs coargs)
    -> case cexpr of
         (CVar i)
           -> [Open noRange (QName (id2name i)) (copenargs2importdirective coargs)]
         (CApply (CVar i) bces)
           -> [Open noRange (QName (id2name i)) (copenargs2importdirective coargs)]
         _ -> errorDecls $ pp "" cdefn
  CClass classargs b csigns
    -> errorDecls $ pp "" cdefn
  CInstance i cargs cinsarg cletdefs
    -> errorDecls $ pp "" cdefn

-- Utilities

cletdef2bind :: CLetDef -> Maybe (Name,Expr)
cletdef2bind cletdef = case cletdef of
  CSimple cdef
    -> case [ (lhs,rhs) | FunClause lhs rhs ld <- transCDef cdef ] of
         (LHS p _ _ _,RHS e):_
           -> case p of
                IdentP    qn            -> Just (qn2n qn, e)
                RawAppP _ (IdentP qn:_) -> Just (qn2n qn, e)
                _ -> Nothing
         _ -> Nothing
  _ -> Nothing
  where
    qn2n (QName n)  = n
    qn2n (Qual n _) = n

ctype2pats :: CType -> [Pattern]
ctype2pats (CUniv carg cexpr)
  = map (IdentP . QName. id2name) (exIds carg) ++ ctype2pats cexpr
    where exIds (CArg bis _) = map snd $ filter (not . fst) bis
ctype2pats _ = []

ctype2typesig :: InfixP -> Id -> CArgs -> CType -> Declaration
ctype2typesig flg i args ctype
  | flg = TypeSig (id2infixName i) ys
  | otherwise = TypeSig (id2name i) ys
  where xs = concatMap (\ (CArg bns ct) -> bns) args
        ys = foldr (\ (b,i) e -> Fun noRange ((if b then HiddenArg noRange . unnamed else id) (Ident $ QName $ id2name i)) e)
		   (transCExpr ctype) xs

csig2fields :: CSign -> [TypeSignature]
csig2fields (CSign is ctype)
 = map (f ctype) is
   where f cty i = TypeSig (name i) (transCExpr cty)
         name i = if isSym $ head $ getIdString i then id2infixName i
                  else id2name i
csig2fields csign
 = errorDecls $ "csig2fields cannot translate ("++pp "" csign++")"

carg2telescope :: CArg -> Telescope
carg2telescope (CArg bis ctype)
  = map (\ (b,i) -> TypedBindings noRange (bool2hiding b) [TBind noRange [mkBoundName_ $ id2name i] (transCExpr ctype)]) bis

csummand2constructor :: Expr -> CSummand -> Constructor
csummand2constructor otype (i,cargs)
 = TypeSig (id2name i)
 $ foldr (\ (b,i,t) e -> Fun noRange (transCExpr t) e) otype (concatMap excargs cargs)

csummand2constructor' otype (i,cargs)
 = TypeSig (id2name i)
 $ foldr (\ carg e -> Pi (carg2telescope carg) e) otype cargs

cindsum2constructor :: CIndSummand -> Maybe Constructor
cindsum2constructor (CIndExpl csum i bexps)
 = Just $ csummand2constructor' otype csum
   where otype = RawApp noRange (Ident (QName (id2name i)):map (paren . transCExpr . snd) bexps)
cindsum2constructor _ = Nothing

paren :: Expr -> Expr
paren e = case e of
 RawApp r _    -> Paren r e
 App r _ _     -> Paren r e
 OpApp r _ _   -> Paren r e
 WithApp r _ _ -> Paren r e
 Lam r _ _     -> Paren r e
 Fun r _ _     -> Paren r e
 Rec r _       -> Paren r e
 Let r _ _     -> Paren r e
 _             -> e

copenargs2importdirective :: [COArg] -> ImportDirective
copenargs2importdirective coargs
 = case unzip $ map coarg2urm coargs of
     (ns, rns) -> ImportDirective noRange (Using (map ImportedName (catMaybes ns)))
                                             (map mkRenaming $ catMaybes rns) False
  where coarg2urm (COArgT _ i t)     = (Just $ id2name i,Nothing)
        coarg2urm (COArg _ i)        = (Just $ id2name i,Nothing)
        coarg2urm (COArgAs _ i j)    = (Nothing,Just (ImportedName $ id2name i,id2name j))
        coarg2urm (COArgAsT _ i t j) = (Nothing,Just (ImportedName $ id2name i,id2name j))

        mkRenaming (i, x) = Renaming i x noRange

-- Translator from Agda1 expression syntax to Agda2 expression syntax

transCExpr :: CExpr -> Expr
transCExpr ce = case ce of
  CVar i      -> Ident (QName (id2name i))
  CStar _ 0 _ -> Set noRange
  CStar _ n _ -> SetN noRange (fromIntegral n)
  Clam (flg,CBind [x] Nothing) e
              -> Lam noRange [DomainFree (bool2hiding flg) (mkBoundName_ $ id2name x)] (transCExpr e)
  Clam (flg,CBind xs (Just t)) e
              -> Lam noRange
                     [DomainFull (TypedBindings
                                    noRange
                                    (bool2hiding flg)
                                    [TBind noRange (map (mkBoundName_ . id2name) xs) (transCExpr t)]
                                 )
                     ]
                     (transCExpr e)
  Clam _ _    -> error $ "transCExpr: Never!! "++pp' ce
  CUniv a e   -> case a of
		   CArg bis ctype
                     -> foldr (\ (b,i) expr
                               -> Pi [TypedBindings noRange
                                                    (bool2hiding b)
                                                    [TBind noRange
                                                           [mkBoundName_ $ id2name i]
                                                           (transCExpr ctype)]
                                     ]
                                     expr)
                              (transCExpr e) bis
  CArrow flg ce1 ce2
              -> Fun noRange (parenExpr (transCExpr ce1)) (transCExpr ce2)
  Clet defs cexpr
              -> Let noRange (translate defs) (transCExpr cexpr)
  CProduct pos csigs
              -> errorExpr $ pp' ce
  CRecord cprops pos cletdefs
              -> let len   = length cletdefs
                     binds = mapMaybe cletdef2bind cletdefs
                     len'  = length binds
                 in if len /= len' then errorExpr $ pp (show (len,len')) ce
                    else Rec noRange binds
  Copen cexpr1 coargs cexpr2
              -> errorExpr $ pp' ce
  CApply f args
              -> case f of
                   CVar i | isSym (head (getIdString i))
                     -> transCExpr
                     $  CApply (CBinOp (snd $ head args) i (snd $ head $ tail  args))
                               [(flg,t2sCExpr e) | (flg,e) <- tail (tail args)]
                   _        -> foldl (\ e (flg,cexpr)
                                      -> App noRange
                                             e
                                             (Arg { argHiding = bool2hiding flg
                                                  , unArg = unnamed (parenExpr (transCExpr cexpr)) }))
                                     (parenExpr (transCExpr f))
                                     args
  CBinOp o1 b o2
    | isSym (head (getIdString b))
              -> OpApp noRange (id2infixName b) (map (parenExpr . transCExpr) [o1,o2])
    | otherwise
              -> transCExpr (CApply (CVar b) [(False,o1),(False,o2)])
  CMeta _ _ _ _
              -> QuestionMark noRange Nothing
  Cif ec et ee-> RawApp noRange (Ident ifQName : map (parenExpr . transCExpr) [ec,et,ee])
  CCConS i    -> transCExpr (CVar i)
  CSelect _ _ -> errorExpr $ pp' ce
  CSum _      -> errorExpr $ pp' ce
  CCCon _ _   -> errorExpr $ pp' ce
  Ccase _ _   -> errorExpr $ pp' ce
  CClos _ _   -> errorExpr $ pp' ce
--  Ccomment _ c e -> App noRange (commentExpr c) (transCExpr e)
  Ccomment _ c e
              -> transCExpr e
  CPackageType-> errorExpr $ pp' ce
  CIndSum _ _ -> errorExpr $ pp' ce
  CExternal _ -> errorExpr $ pp' ce
  CLit _ l    -> case l of
      LString s   -> Lit (LitString noRange s)
      LChar c     -> Lit (LitChar noRange c)
      LInt i      -> Lit (LitInt noRange (fromInteger i))
      LRational r -> Lit (LitFloat noRange (fromRational r))
      _           -> errorExpr $ pp' ce
  CDo _ _     -> errorExpr $ pp' ce
  CList _ _   -> errorExpr $ pp' ce

----

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

---- for non-supported translation and for comment (all of these kluges !)
-- debugFlg = True
debugFlg = elem "-D" $ unsafePerformIO getArgs

pp :: (PPrint a) => String -> a -> String
pp s = if debugFlg then (++ (" (D-> "++s++" <-D) ")) . ppAll else ppAll

pp' = starling (flip pp) show

errorDecls :: String -> [Declaration]
errorDecls msg
 = [TypeSig (str2name "{- translation error! ") (errorExpr' msg)]

errorExpr :: String -> Expr
errorExpr s = Ident $ str2qname $ "{! "++ s ++ " !}"

errorExpr' :: String -> Expr
errorExpr' s = Ident $ str2qname $ s ++ " -}"

commentDecls :: String -> [Declaration]
commentDecls msg
 = [TypeSig (str2name "{- ") (commentExpr' msg)]

commentExpr :: String -> Expr
commentExpr s = Ident (str2qname $ "{- " ++ s ++ " -}")

commentExpr' :: String -> Expr
commentExpr' s = Ident (str2qname $ s ++ " -}")

str2qname :: String -> QName
str2qname = QName . str2name

str2name :: String -> Name
str2name s = Name noRange [Id s]

----

isInfixOp :: Id -> Bool
isInfixOp = all (not . isAlphaNum) . getIdString

id2name :: Id -> Name
id2name i = str2name (getIdString i)

id2infixName :: Id -> Name
id2infixName i = Name noRange [Hole,Id (getIdString i),Hole]

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
 = case expr of
     Ccase _ _
       -> liftCcase i flg cpats expr
     _ | flg
       -> [FunClause (LHS (RawAppP noRange (intersperse op pats)) [] [] [])
		     (RHS (transCExpr expr))
                     (localdefs expr)]
     _ | otherwise
       -> [FunClause (LHS (RawAppP noRange (op : pats)) [] [] [])
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
                  _ -> errorDecls ("cannot translate this case: "
                                  ++ show cexpr ++ " not in args")
      _      -> errorDecls "cannot translate 'case' on any but simple variable"
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
             | flg = [FunClause (LHS (RawAppP noRange (intersperse (IdentP (QName (id2name n))) (cpat2pattern pat i pats))) [] [] [])
                                (RHS (transCExpr expr')) (localdefs expr')]
             | otherwise = [FunClause (LHS (RawAppP noRange (IdentP (QName (id2name n)):cpat2pattern pat i pats)) [] [] [])
                                      (RHS (transCExpr expr')) (localdefs expr')]
         where expr' = substcexpr x (cpat2cexpr pat) expr
               x = case cexpr of {CVar v -> v; _ -> error "Never"}
      absurdcc n flg pats i
             | flg = [FunClause (LHS (RawAppP noRange (intersperse (IdentP (QName (id2name n))) [abpat])) [] [] [])
                                AbsurdRHS NoWhere]
             | otherwise = [FunClause (LHS (RawAppP noRange (IdentP (QName (id2name n)):[abpat])) [] [] [])
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

decls2namexpr :: [Declaration] -> (Name,Expr)
decls2namexpr ds
 = case head $ reverse ds of
     FunClause (LHS (IdentP (QName name)) _ _ _) (RHS e) w
       -> (name, e)
     FunClause (LHS pat _ _ _) (RHS e) w
       -> case pat of
           RawAppP _ [IdentP (QName n)] -> (n,e)
           _                            -> (str2name "%%var%%", e)
     _ -> (str2name "", errorExpr "in translating CRecord")
