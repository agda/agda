{-# OPTIONS -cpp #-}
#include "config.h"
{-| Pretty-printer for CSyntax
-}

module CPrinter where
import CSyntax
import PPrint
import Utilities (pp,t,pre)
import Id(Id,ppId,isBinOp,ppInfix,getFixity)
import BinParse(Fixity(..))
import MetaVars(MetaVar,preMetaVar)
import Data.List(groupBy)
import MiscId
import Literal
import Data.Maybe(fromMaybe,mapMaybe)

instance PPrint CProgram where
    pPrint d _ (CProgram ms) = vcat (map (pp d) ms)

instance PPrint CModule where     --Förbättra
    pPrint d p (CModule i [] e) = separate [t"module "~. ppId d i,nest 2 (pPrint d p e)]
    pPrint d p (CModule i as e) = separate [separate [t"module "~. ppId d i, ppCArgs d 10 as], nest 2 (pPrint d p e)]

ppComments :: Comment -> IText
ppComments cs = t cs

ppOp d pd i p1 p2 =
        let (p, lp, rp) =
                case getFixity i of
                FInfixl p -> (p, p, p+1)
                FInfixr p -> (p, p+1, p)
                FInfix  p -> (p, p+1, p+1)
        in pparen (d > PDReadable || pd>p)
                  (pPrint d lp p1 ~. t" " ~.ppInfix d i ~. t" " ~. pPrint d rp p2)    -- Ett hack


ppBinCExpr d pd e p1 p2 =
  case e of
   CVar x -> ppOp d pd x p1 p2
   _          -> t"Internal error"



ppHiddenId d (False,i) = ppId d i
ppHiddenId d (True,i)  = t"|"~. ppId d i


instance PPrint CExpr where
    pPrint d p (CVar i) | i == nilId  = t"[]"
    pPrint d p (CVar i) = ppId d i
    pPrint d p (CStar _ 0 _) = t"Set"
    pPrint d p (CStar _ 1 _) = t"Type"
    pPrint d p (CStar _ n m) = t("#" ++ (if n > 0 then show n else "") ++ if n /= m then "."++show m else "")
    pPrint d p e@(CApply _ _) = ppApp d p e
    pPrint d p e@(CUniv _ _ ) = ppQuant d p e
    pPrint d p e@(Clam _ _) = ppLam d p e
    pPrint d p (CArrow b a r) = pparen (p > 0) (separate [pPrint d 1 a ~. t(if b then " |->" else " ->"), pPrint d 0 r])
    pPrint d p (Clet [] e) = pparen (p > 8) $
        (t"let in " ~. pp d e)
    pPrint d p (Clet ds e) = pparen (p > 8) $
        (t"let " ~. layout d ds) ^.
        (t"in  " ~. pp d e)
    pPrint d p (CProduct _ []) =
        pparen (p>8) $ t"sig {}"
    pPrint d p (CProduct _ as)
        =  if p > 8 then
              pparen True $  t"sig " ~. nolayout d as
           else t"sig " ^.   nest 2 (layout d as)
    pPrint d p (CRecord ps _ []) =
        pparen (p>8) $ t"struct {}"
    pPrint d p (CRecord ps _ ds) =
         if p > 8 then
              pparen True $ separate (ppProps ps ~. t"struct " ~.  t"{" : [nest 2 (vcat (map (\s -> s~.text ";")(map (\def -> pp d def ) ds)))])~. t "}"
        else separate (map (pp d) ps) ~. t"struct " ^.
                nest 2 (layout d ds) -- vcat (map (pp d) ds)
    pPrint d p (Copen e as b) = pparen (p > 8) $ (t"open " ~. pp d e ~. pp d as ~. t" in ") ^. (pp d b)
    pPrint d p (CSelect e i) = pparen (p > 12) $ pPrint d 12 e ~. t"." ~. ppId d i
--    pPrint d p (CSelectT e i) = pparen (p > 12) $ pPrint d 12 e ~. t"#" ~. ppId d i
    pPrint d p (CSum cs) = pparen (p > 12) $
        t"data " ~. ppSummands d cs
#ifdef NEWSYNTAX
    pPrint d p (CCCon  i ty) =
        ppId d i
    pPrint d p (CCConS i) =  ppId d i
#else
    pPrint d p (CCCon  i ty) =
        pparen (p > 12) $ ppId d i ~. t"@" ~. pPrint d 12 ty
    pPrint d p (CCConS i) = pparen (p > 12) $ ppId d i ~. t"@_"
#endif
    pPrint d p (Ccase e arms) = ppCase d p e arms
    pPrint d p (Cif c tr e) = pparen (p>1) (separate [t"if " ~. pp d c ~. t" then", nest 4 (pp d tr), t"else", nest 4 (pp d e)])
    pPrint d p (CLit _ l) = pPrint d p l
    pPrint d p e@(CBinOp e1 i e2) =
         fromMaybe (fromMaybe (ppOp d p i e1 e2) (ppCList d e)) (ppStr e)
        --pparen (p>0) $ pPrint d 1 e1 ~. t" " ~. ppInfix d i ~. t" " ~. pPrint d 1 e2
    pPrint d p (CMeta pos _ aut m)
               | isVisAut aut  = t("_")
               | m == preMetaVar = t"?"
               | otherwise = t("?"++(show m))
    pPrint d p (CClos [] e) =  pPrint d p e
    pPrint d p (CClos env e) = pparen (p > 0)$ separate [pPrint d p e,nest 2 (ppCEnv d env)]
    pPrint d p (Ccomment left cs e)
                  | left =  ppComments cs ~. pPrint d p e
                  | otherwise = pPrint d p e ~. ppComments cs
    pPrint d p CPackageType =  t"<package>"
    -- share with CProduct later.
    pPrint d p (CIndSum ctel cs) = pparen (p > 12) $
        nseparate [t"idata "~.ppCArgs d 10 ctel, nest 2 (ppIndSummands d cs)]
    pPrint d p (CDo _ bs) = pparen (p>0) $
        t"do " ~. -- pPrint d 11 e ~. t" " ~.
        separate [t"{", nest 2 (separate (map (pp d) bs)), t"}"]
    pPrint d p (CList _ l) = ppList d l
    pPrint d p (CExternal ext) = t"external " ~. pPrint d p ext

    --pPrint d p e = error (ppr d e)

--     pPrint d p (Cdo e bs) =
--         pparen (p>0) $
--      t"do " ~. pPrint d 11 e ~. t" " ~.
--      separate [t"{", nest 2 (separate (map (pp d) bs)), t"}"]
--    pPrint d p (CWarn _ e) = pPrint d p e
--    pPrint d p (CHasType e t) = pparen (p>0) $ pPrint d 10 e ~. text "::" ~. pPrint d 10 t

ppEqCEnv d (x,e) = ppId d x ~. t"= " ~. pPrint d 0 e

--ppApArg :: PDetail -> Int -> (Bool,CExpr) -> IText
ppApArg d p (False, e) = pPrint d p e
ppApArg d p (True,  e) = text "|" ~. pPrint d p e

ppCEnv PDDebug [] = t"{}"
ppCEnv d@PDDebug env = t" where {" ~. (vcat (map (ppEqCEnv d) env)) ~. t"}"
ppCEnv d [] = t""
ppCEnv d env = t"where " ~. vcat (map (ppEqCEnv d) env)


ppApp d p e = fromMaybe (fromMaybe (fromMaybe (ppApp' d p e) (ppCList d e)) (ppStr e)) (ppPair d e)
    where
          ppApp' :: PDetail -> Int -> CExpr -> IText
          ppApp' PDReadable p (CApply e []) = pPrint PDReadable p e
          ppApp' PDReadable p (CApply e [e1]) = pparen (p>9) $  pPrint PDReadable p e ~. t" " ~. (ppApArg PDReadable 10 e1)
          ppApp' d p (CApply h@(CVar x) [e1,e2])
              | isBinOp x = ppOp d p x (snd e1) (snd e2)
              | otherwise = pparen (p>9) $ pPrint d 9 h  ~. t" " ~. (ppApArg d 10 e1) ~. t" " ~. (ppApArg d 10 e2)
          --ppApp' d p (CApply e [e1,e2]) = pparen (p>9) $  pPrint d 9 e  ~. t" " ~. (ppApArg d 10 e1) ~. t" " ~. (ppApArg d 10 e2)
          --ppApp' d p (CApply e [e1,e2,e3]) = pparen (p>9) $  pPrint d 9 e  ~. t" " ~.(ppApArg d 10 e1) ~. t" " ~. (ppApArg d 10 e2) ~. t" " ~. (ppApArg d 10 e3)
          --ppApp' d p (CApply e [e1,e2,e3,e4]) = pparen (p>9) $  pPrint d 9 e  ~. t" " ~. (ppApArg d 10 e1) ~. t" " ~.  (ppApArg d 10 e2) ~. t" " ~. (ppApArg d 10 e3)~. t" " ~. (ppApArg d 10 e4)
#ifdef NEWSYNTAX
          ppApp' d p (CApply h@(CCConS x) [e1,e2])
              | isBinOp x = ppOp d p x (snd e1) (snd e2)
              | otherwise = pparen (p>9) $ pPrint d 9 h  ~. t" " ~. (ppApArg d 10 e1) ~. t" " ~. (ppApArg d 10 e2)
#endif
          ppApp' d p (CApply e es) = pparen (p>9) $
                  cseparate (pPrint d 9 e : map (ppApArg d 10) es)


ppQuant d p e =  pparen (p > 0) $  separate (ppQuants d e)
        where ppQuants :: PDetail -> CExpr -> [IText]
              ppQuants d (CUniv cb e) =
                 let cbs = groupHidden cb
                 in map pparg cbs ++  ppQuants d e
              ppQuants d e = [pPrint d 0 e]
              groupHidden :: CArg -> [(Bool,[Id],CExpr)]
              groupHidden (CArg hxs a) =
                let hxss = groupBy (\(h,_) -> \(h',_) -> h == h') hxs
                    liftHidden :: [(Bool,Id)] -> (Bool,[Id],CExpr)
                    liftHidden hxs' = let (hs,xs) = unzip hxs'
                                      in (head hs,xs,a)
                in map liftHidden hxss
              pparg :: (Bool,[Id],CExpr) -> IText
              pparg (hidden,is,ty) = (pparen True ( (nsepList (map (ppId d) is) (t","))  ~. t"::" ~. pPrint d 0 ty)) ~. t(if hidden  then " |->" else " ->")
              -- pparg' d p (h,is,CMeta _ _ _ _) = (nsepList (map (\i -> t " \\" ~.ppId d i) is) (if h then t" |->" else t"->")) ~. (if h then t" |->" else t"->")
ppLam d p e =  pparen (p > 8) $ separate (pplams e)
        where pplams (Clam (h,CBind xs mt) e)= (pparg (h,xs,mt)) : pplams e
              pplams e = [pPrint d 0 e]
              pparg :: (Bool,[Id],Maybe CExpr) -> IText
              pparg  (hidden,is,Nothing) = t"\\" ~. (nsepList (map (ppId d) is) (t" ")) ~. t(if hidden  then " |->" else " ->")
              pparg (hidden,is,Just ty) = t"\\" ~. pparen True ( (nsepList (map (ppId d) is) (t","))  ~. t"::" ~. pPrint d 0 ty) ~. t(if hidden  then " |->" else " ->")

ppCase d p e [] = t"case " ~. pp d e ~. t" of { }"
ppCase d p e arms  =
      if p > 8 then   pparen True $ separate [t"case " ~. pp d e ~. t" of {", nest 2 (vcat  (map (\br -> (ppBranch d br) ~. t";") arms) ~. t"}")]
      else (t"case " ~. pp d e ~. t" of ") ^.   (nest 4 (vcat (map (ppBranch d) arms)))
   ---  | otherwise =
   --(
  where ppBranch d (br,e) = separate [pPrint d 10 br ~. t" ->", nest 2 (pp d e)]

instance PPrint CProp where
    pPrint _ _ p = t (tail (show p))


ppProps :: [CProp] -> IText
ppProps [] = t""
ppProps ps = separate (map (pp PDReadable) ps) ~. t" "


instance PPrint COArg where
    pPrint d p (COArg ps i) = separate (map (pp d) ps) ~. t" "~. ppId d i
    pPrint d p (COArgAs ps i1 i2) = separate (map (pp d) ps)  ~. t" "~.ppId d i2 ~. t" = " ~.ppId d i1
    pPrint d p (COArgT ps i ty) = separate (map (pp d) ps) ~. t" " ~. ppId d i ~. t" :: " ~.pp d ty
    pPrint d p (COArgAsT ps i1 ty i2) = separate (map (pp d) ps) ~. t" " ~. ppId d i2 ~. t" :: " ~.pp d ty ~. t" = "~.ppId d i1

instance PPrint COpenArgs where
    pPrint d p (COpenArgs us) = t " use "~.csepList (map (pp d) us) (t",")


--    pPrint d p COpenAll = t"*"

instance PPrint CDef where
    pPrint d p (CDef [] def) =  pPrint d p def
    pPrint d p (CDef ps def) =  ppCDefn d (map ((\s -> s ~. t" ") . pp d) ps) def
    pPrint d p (CDefComment cs) = ppComments cs

ppCDefn ::  PDetail -> [IText] -> CDefn -> IText
ppCDefn d ps (CValueT i [] ty e) =
        (foldr (~.) (separate [ppId d i~.t"::", nest 2 (pp d ty )]) ps) ^.
                  (separate [{-ppId d i,-}nest 2 (t"= " ~. pp d e)])
ppCDefn d ps (CValueT i as ty e) =
        foldr (~.) (separate [ppId d i~.t" "~. ppCArgs' d 10 as~.t" :: ",
                     (nest 2 (pp d ty))]) ps ^.
            separate [{-ppId d i,-}nest 2 (t"= "~.pp d e)]
ppCDefn d ps (CValueS i [] ty c) =
        foldr (~.) (separate[ppId d i~.t" :: " ,nest 2 ( pp d ty )~.t";"]) ps  ^.
        (ppId d i ~. t" " ~. pp d c)
ppCDefn d ps (CValueS i as ty c) =
        foldr (~.) (separate [ppId d i~.t" "~. ppCArgs' d 10 as~.
                     t" :: " , nest 2 (pp d ty)]~.t";") ps  ^.
          (ppId d i ~. t" " ~. pp d c)
ppCDefn d ps def = foldr (~.) (pp d def) ps

instance PPrint CLetDef where
    pPrint d p (CSimple def) = pp d  def
    pPrint d p (CMutual ds) = t"mutual " ~. layout d ds
    pPrint d p (CLetDefComment cs) = ppComments cs
  --  pPrint d p (CErrDef msg) =  pre msg


--ppBA :: PDetail -> Int -> CArg ->  IText
--ppBA d p (False,a) = pPrint d p a
--ppBA d p (True,a) = t"|" ~. pPrint d p a

-- I need this in Alfa. /TH
-- (Incidentally, it appears to be useful in a lot of places here too... :-)

--ppCArgBs d p = nest 2 . nseparate . map (ppBA d p)


instance PPrint CDefn where
    pPrint d _ (CValueT i [] ty e) =
        separate [ppId d i~.t" ::" ~. nest 2 (pp d ty )]^.
                  separate [{-ppId d i,-}nest 2 (t"= " ~. pp d e)]
    pPrint d _ (CValueT i as ty e) =

            separate [ppId d i~.t" "~. ppCArgs' d 10 as~.t" ::",
                     nest 2 (pp d ty)]^.
            separate [{-ppId d i,-}nest 2 (t"= "~.pp d e)]
    pPrint d p (CValueS i [] ty c) =
        separate[ppId d i~.t" :: " ,nest 2 (pp d ty )~.t";"] ^.
        (ppId d i ~. t" " ~. pp d c)
    pPrint d p (CValueS i as ty c) =
        separate [ppId d i~.t" "~. ppCArgs' d 10 as~.
                     t" :: ",nest 2 (pp d ty)~.t";"] ^.
          (ppId d i ~. t" " ~. pp d c)
--    pPrint d p (CValueP i cs) =
--      vcat (map (\ cl -> ppClause d p [ppId d i] cl ~. t";") cs)
    pPrint d p (Ctype i [] ty) =
        separate [ (t"type " ~. ppId d i), nest 2 (t"= "~.pp d ty)]
    pPrint d p (Ctype i as ty) =
        separate [t"type " ~. ppId d i ~. t" " ~.nest 2 (nseparate (map (pPrint d 10) as)) ,
                  nest 2 (t" = "~.pp d ty)]
    pPrint d _ (Cnewtype i [] ty e) =
        separate [t"newtype "~.ppId d i~.t" ::" ~. nest 2 (pp d ty )]^.
                  separate [{-ppId d i,-}nest 2 (t"= " ~. pp d e)]
    pPrint d _ (Cnewtype i as ty e) =

            separate [t"newtype "~.ppId d i~.t" "~. ppCArgs d 10 as~.t" ::",
                     nest 2 (pp d ty)]^.
            separate [{-ppId d i,-}nest 2 (t"= "~.pp d e)]
    pPrint d p (Cdata i as Nothing cs) =
        separate [t"data " ~. ppId d i ~. t" " ~. nest 2 (nseparate (map (pPrint d 10) as)) ,
                  t" = " ~. ppSummands d cs ]
    pPrint d p (Cdata i as (Just e) cs) =
        separate [t"data " ~. ppId d i ~. t" " ~. nest 2 (nseparate (map (pPrint d 10) as)) ,
                  t" :: "~.pp d e, t" = " ~. ppSummands d cs ]
    pPrint d p (Cidata i as e cs) =
        separate [t"idata " ~. ppId d i ~. t" " ~. nest 2 (nseparate (map (pPrint d 10) as)) ,
                  t" :: "~.pp d e, t" = " ~. ppIndSummands d cs]
    pPrint d p (CValue i e) =
        separate [ppId d i ~. t" =",
                  nest 2 (pp d e)]
    pPrint d p (CAxiom i [] b) =  separate [t"postulate "~.ppId d i~.t" ::",nest 2 (pp d b)]
    pPrint d p (CAxiom i as b) =  separate [t"postulate "~.ppId d i~.t" " ~. ppCArgs d 10 as~. t" ::",nest 2 (pp d b)]
    pPrint d p (CNative i b) =  separate [t"native "~.ppId d i~.t" ::",nest 2 (pp d b)]
    pPrint d p (CClass (CClassArg i as ty exts) exports csign) =
          separate [separate [t"class "~. ppId d i ~. ppCArgs d 10 as ~. t" :: ", nest 2 (pp d ty ~. (if null exts then t"" else t" extends " ~. ppCArgs d 10 exts) ~. (if exports then t" exports" else t " where"))],nest 2 (layout d csign)]
    pPrint d p (CInstance i as (CInstanceArg e) ds) =
        separate [t"instance "~. ppId d i ~. ppCArgs d 10 as ~. t" :: " ~. pp d e ~. t" where",
                  nest 2 (layout d ds)]

    pPrint d p (CPackage i [] (CPackageDef ps _ [])) =
           separate [ t"package "~. ppId d i ~. ppProps ps ~. t" where ;"]
    pPrint d p (CPackage i [] (CPackageDef ps _ ds)) =
           separate [ t"package "~. ppId d i ~. ppProps ps ~. t" where",nest 2 (layout d ds)]
    pPrint d p (CPackage i as  (CPackageDef ps _ [])) =
                 separate [ t"package "~. ppId d i, ppCArgs d 10 as,ppProps ps ~. t" where ;"]
    pPrint d p (CPackage i as  (CPackageDef ps _ ds)) =
                  separate [separate [ t"package "~. ppId d i, ppCArgs d 10 as,ppProps ps ~. t" where"],  nest 2 (layout d ds)]

    pPrint d p (CPackage i [] e) = separate [t"package "~. ppId d i,nest 2 (pPrint d p e)]
    pPrint d p (CPackage i as e) = separate [separate [t"package "~. ppId d i, ppCArgs d 10 as], nest 2 (pPrint d p e)]
    pPrint d p (COpen e as) = separate [t"open "~.pPrint d p e,pPrint d p as]

    --pPrint d p dn = error (ppr d  dn)

--    pPrint d p (CNative i ty s) =
--      ppId d i ~. t" :: " ~. pp d ty ~. t" = " ~. t (show s) ~. t";"
--    pPrint d p (CDSign i ty) =
--      separate [ppId d i ~. t" ::", nest 2 (pp d ty ~. t";")]

ppSummands d cs = sepList (map ppCon cs) (t" |")
  where ppCon (i, ts) = separate (ppId d i : map (nest 2 . pPrint d 10) ts)

ppIndSummands d cs = sepList (map ppIndCon cs) (t" |")
  where ppIndCon (CIndExpl (i,ts) n es) = separate
          [ separate (ppId d i : map (nest 2 . pPrint d 10) ts)
          , nest 2 ((t ":: ") ~. (pp d (cApply (CVar n) es)))]
	ppIndCon (CIndImpl (i, ts) es) = separate
          [ separate (ppId d i : map (nest 2 . pPrint d 10) ts)
          , nest 2 . separate $ t":: _" : map (ppApArg d 10) es]

instance PPrint CPackageBody where
       pPrint d p (CPackageDef ps _ []) =  ppProps ps ~. t" where ;"
       pPrint d p (CPackageDef ps _ ds) =  ppProps ps ~. t" where" ^. nest 2 (layout d ds)
       pPrint d p (CPackageInstance e) = t"= " ~. pp d e

instance PPrint CDoBind where
     pPrint d p (CDoBind a e) = pp d a ~. t" <- " ~. pp d e ~. t";"
     pPrint d p (CDoBind_ e) = pp d e ~. t";"
     pPrint d p (CDoLet ds) = t"let " ~. foldr1 (^.) (map (pp d) ds) ~. t";"


instance PPrint CClause where
    pPrint d p cl = ppClause d p [] cl

ppClause d p xs (CClause ps e) =
        separate (xs ++ map f ps) ~. t" = " ~. nest 2 (pp d e)
        --   t"= " ~. nest 2 (pp d e)
        where f (False, p) = pPrint d 10 p
              f (True,  p) = t"|" ~. pPrint d 10 p


instance PPrint CPatArg where
       pPrint d p (CPatT i a) = pparen (p > 0) (ppId d i ~. t"::" ~. pPrint d 6 a)
       pPrint d p (CPatId i) = ppId d i

instance PPrint CPat where
    pPrint d p (CPVar a) = pPrint d p a
    pPrint d p (CPCon i as@[a1,a2])
         | isBinOp i = ppOp d p i a1 a2
         | otherwise = pparen (p>9) $ separate (ppId d i : map (pPrint d 10) as)
    pPrint d p (CPCon i as) = pparen (p>9) $ separate (ppId d i : map (pPrint d 10) as)
    --pPrint d p (CPAs a pp) = ppId d a ~. t"@" ~. pPrint d 10 pp
--    pPrint d p (CPLit _ l) = pPrint d p l

instance PPrint CArg where
           pPrint d p (CArg his ty) = pparen (p > 0)( (nsepList (map (ppHiddenId d) his) (t","))  ~. t"::" ~. pPrint d 6 ty)

ppCArgs d p = nest 2 . nseparate . map (pPrint d p)

#if (NEWSYNTAX || TRANSLATE)
ppCArgs' d p = nest 2 . nseparate . map (printArg d p)
printArg d p (CArg his ty) =
  pparen (p > 0)( (nsepList (map printB his) (t","))  ~. t"::" ~. pPrint d 6 ty) where
   printB (True,i) = ppId d i
   printB (False,i) = t"!"~.ppId d i

#else
ppCArgs' d p = nest 2 . nseparate . map (pPrint d p)
#endif



instance PPrint CSign where
    pPrint d _ (CSign is ty) =  separate [(nsepList (map (ppId d) is) (t",") )~. t" ::", nest 2 (pp d ty )]
    pPrint d p (CSignDef def) = pPrint d 0 def
--    pPrint d p (CSignType i as) =
--      separate ((t"type " ~. ppId d i) : map (nest 2 . pPrint d 10) as) ~. t";"


instance PPrint CConstraint where

     pPrint d _ (CEq e1 e2) = separate [pp d e1 ,t"=",pp d e2]
     pPrint d _ (CJudg j) = pPrintCJudgE d j


pPrintCJudgE :: PDetail -> CJudgement CExpr -> IText
pPrintCJudgE d (HasType e e') = pp d e ~. t" :: " ~. pp d e'
pPrintCJudgE d (CIsType e) = pp d e ~. t" Type"

pPrintCJudg :: PDetail -> CJudgement MetaVar -> IText
pPrintCJudg d (HasType m e) = t("?"++show m++" :: ")~. pp d e
pPrintCJudg d (CIsType m) = t("?"++show m++" Type")


isStringType :: CExpr -> Bool
isStringType e = e == CApply (CVar listId) [(False,CVar charId)] || e == CVar stringId


isCons :: CExpr -> Bool
isCons (CCCon i _) = i == consId
isCons (CCConS i) = i == consId
isCons (CVar i) = i == consId
isCons _ = False

isNil :: CExpr -> Bool
isNil (CCCon i _) = i == nilId
isNil (CCConS i) = i == nilId
isNil (CVar i) = i == nilId
isNil (CApply (CVar i) [(True,_)]) = i == nilId
isNil _ = False


mkPair :: CExpr -> Maybe [CExpr]
mkPair (CApply (CVar i) [(False,e),(False,e')]) | i == commaId =
         Just$ e: (maybe [e'] id (mkPair e') )

mkPair (CApply (CVar i) [(True,_),(False,e),(False,e')]) | i == commaId =
         Just$ e: maybe [e'] id (mkPair e')

mkPair (CApply (CVar i) [(True,_),(True,_),(False,e),(False,e')]) | i == commaId =
         Just$ e: maybe [e'] id (mkPair e')

mkPair (CApply (CCCon i _) es) = mkPair (CApply (CVar i) es)
mkPair (CApply (CCConS i) es) = mkPair (CApply (CVar i) es)
mkPair _ = Nothing

ppPair :: PDetail -> CExpr -> Maybe IText
ppPair d e = fmap ppPair' (mkPair e)
     where ppPair' xs = let (y:ys) = reverse $ map (pPrint d 0) xs
                            f =  \s -> (~.) s (text ",")
                            ys' = map f ys
                            xs' = reverse (y:ys')
                        in  text "(" ~. separate xs' ~. text ")"
--                    in  text "[" ~. cseparate xs' ~. text "]"

mkCList :: CExpr -> Maybe [CExpr]
mkCList e | isNil e = Just$ []

mkCList (CApply (CCCon i ty) [(_,x),(_,e')]) | i == consId = do
           es <- mkCList e'
           return (x:es)
mkCList (CApply (CCConS i) [(_,x),(_,xs)])| i == consId = do
           xs' <- mkCList xs
           return (x:xs')

mkCList (CApply (CVar i) [_,(_,x),(_,xs)])| i == consId = do
           xs' <- mkCList xs
           return (x:xs')

mkCList (CApply (CVar i) [(False,x),(False,xs)])| i == consId = do
           xs' <- mkCList xs
           return (x:xs')
mkCList (CBinOp x i xs)| i == consId =  do
           xs' <- mkCList xs
           return (x:xs')
mkCList _ = Nothing

ppList :: PDetail -> [CExpr] -> IText
ppList d es = pPrint d 0 es

{-
ppList d [] = t "[]"
ppList d (e:es) = separate (t"[" ~. pp d e :  ppList' es)
     where ppList' [] = [t"]"]
           ppList' (e:es) = t"," : pp d e : ppList' es
-}




ppCList :: PDetail -> CExpr -> Maybe IText
ppCList d e = fmap (ppList d) (mkCList e)



mkString e = mkString' False e
   where mkString' :: Bool -> CExpr -> Maybe String
 	 mkString' True (CCCon i ty)|i==nilId = Just$ ""
 	 mkString' True (CCConS i)  |i==nilId = Just$ ""
         mkString' True (CVar i)| i == nilId = Just$ ""
	 mkString' _ (CApply (CVar i) [(True,ty)]) | i == nilId && isStringType ty = Just$ ""
	 mkString' _ (CLit _ (LString l)) =  Just l

         mkString' False (CCCon i ty) |i==nilId && isStringType ty  = Just$ ""
	 mkString' _ (CApply (CCCon i ty) [(_,CLit _ (LChar x)),(_,xs)])| i == consId = do
           xs' <- mkString' True xs
           return (x:xs')
	 mkString' _ (CApply (CCConS i) [(_,CLit _ (LChar x)),(_,xs)]) | i == consId = do
           xs' <- mkString' True xs
           return (x:xs')
	 mkString' _ (CApply (CVar i) [_,(_,CLit _ (LChar x)),(_,xs)])| i == consId = do
           xs' <- mkString' True xs
           return (x:xs')
	 mkString' _ (CApply (CVar i) [(False,CLit _ (LChar x)),(False,xs)])| i == consId = do
           xs' <- mkString' True xs
           return (x:xs')
	 mkString' _ (CBinOp (CLit _ (LChar x)) i xs)| i == consId =  do
           xs' <- mkString' True xs
           return (x:xs')
	 mkString' _ _ = Nothing

ppStr :: CExpr -> Maybe IText
ppStr e = maybe Nothing (\s -> Just $ t (show s)) (mkString e)

-- Used for error messages


layout d = vcat . map (pp d)

nolayout d ds = t"{" ~. vcat (map ((~.t";").pp d) ds) ~. t"}"

vcat = foldr1 (^.)
