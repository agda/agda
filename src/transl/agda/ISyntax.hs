{-# OPTIONS -cpp #-}
#include "config.h"
{-|

  Pretty printer for ISyntax (as def. in ISynType)
-}
module ISyntax( module ISynType
              , module ISynEnv
              --,       module ISynPP
              , noPar, getExpPos, getExpPosLast -- , pprId
              , module Id
              , module MetaVars
              , module PluginType
  ) where

import Id
import MetaVars
import ISynType
import ISynEnv
import Data.List(groupBy)
import PluginType

-- import ISynPP

-- This is silly, but hbc does not import instance decl otherwise.

import PPrint
import BinParse (Fixity(..))
import Utilities(t,pp)
import Literal()
import Position
import CITrans(varScope)


instance PPrint Exp where
  pPrint = ppExp

ppExp :: PDetail -> Int -> Exp -> IText
ppExp d p = go where
  go e0 = case e0 of
      (EVar    x   _ )-> ppUId d x
      (EConst  c _  )-> ppUId d c
      (EConstV c xs)-> debFCV xs (ppUId d c)
      (ESort   _ n )-> pPrint d p n

      (EAbs  _ _      )->       ppQuant d p e0
      (EProd _ _      )->       ppQuant d p e0
      (EArrow h e1 e2) ->  pparen (p > 8) (separate [pPrint d 9 e1 ~. t(if h then " |->" else " ->"), pPrint d 8 e2])
      (EApp h [e1,e2] ) | isBinExp h -> ppBinExp d p h (snd e1) (snd e2)
      (EApp h      es )->      ppar 9 $ go10 h `appArgs` es
      (EBinOp e1 op e2)->               ppBinExp d p op e1 e2
      (EIf b e1 e2)    -> pparen (p>0) (separate [t"if " ~. pp d b ~. t" then", nest 4 (pp d e1), t"else", nest 4 (pp d e2)])
      (EDef ds e)-> ppar 8 $ if null ds && not deb
            then go10 e
            else (t"let "~. foldr1 (^.) (map (pp d) ds))^. t"in  " ~. go10 e
#ifdef NEWSYNTAX
      (ECon  c  [e1, e2] )
              | isBinOp c -> ppOp'' d p c (-666) (snd e1) (snd e2)
#endif
      (ECon  c   es      )-> ppCon c (t""         ) es
      (EConF c e es      )-> ppCon c (t"") es
      (EData          cbs)-> ppar 0 $ t"data  " ~.           ppCbs d cbs
      (EIndData _ cbs)-> ppar 0 $ t"idata " `sepnest` ppIndCbs d cbs
      (ECase e cbes      )-> ppEcase d p e cbes

      (EProj e i            )-> ppar 12 $ go12 e ~. t"." ~. ppId d i
      (ESig _ esigdefs      )-> taggedblock "sig" esigdefs []
      (EPackageType             )-> t"Package "
      (Epackage  _ ds xs  _ _  )-> taggedblock "package" ds xs
      --(EpackageV _ ds xs _ _)-> taggedblock "package" ds xs
      (EStruct   _ ds xs _ _ )-> taggedblock "struct"  ds xs
      --(EStructV  _ ds xs _ _)-> taggedblock "struct"  ds xs
      (EOpen e as b)-> (t"open " ~. go10 e ~. pp d as ~. t" in") ^. go10 b

      (PreMeta            )-> t"?"
      (EMetaV m _ xs _ )-> debFCV xs (t("?"++show m))
      (EMeta  m _ _ cit pi maut) -> (if (isVisAut maut) then t"_" else t"?") ~. optnum where
        optnum = if  m==preMetaVar || readable then t""
                 else t("("++show m)~.pp PDDebug pi~.t")"

      (EStop m e)-> if deb then pparen True (t(show m++"!")~.go e) else go e

      (EClos env e)
        | deb       -> pparen True $ go e `sepnest` ppEnv d env
	| readable  -> go e
        | otherwise -> case env `reducedFor` e of
            (E (r,_))| null r ->           go e
            env'          -> ppar  0 $ go e `sepnest` ppEnv d env'
      (ELiteral _ l) -> t(ppReadable l)
      (EExternal plugin) ->
          t" external " ~. pp d plugin



      ( _ ) -> error "ppExp: unprintable"

  ppQuant d p e =  pparen (p > 8) $  separate (ppQuants d e)
        where ppQuants :: PDetail -> Exp -> [IText]
              ppQuants d (EAbs cb e) =
                let cbs :: [(Bool,[UId],Exp)]
                    cbs = groupHidden cb
                    pcbs :: [IText]
                    pcbs = map (\cb -> t "\\" ~. pparg d 9 cb) cbs
                in pcbs ++ ppQuants d e
              ppQuants d (EProd cb e) =
                 let cbs = groupHidden cb
                 in map (pparg d 9) cbs ++  ppQuants d e
              ppQuants d e = [pPrint d 8 e]
              groupHidden :: ([(Bool,UId)],Exp)-> [(Bool,[UId],Exp)]
              groupHidden (hxs,a) =
                let hxss = groupBy (\(h,_) -> \(h',_) -> h == h') hxs
                    liftHidden :: [(Bool,UId)] -> (Bool,[UId],Exp)
                    liftHidden hxs' = let (hs,xs) = unzip hxs'
                                      in (head hs,xs,a)
                in map liftHidden hxss
              pparg :: PDetail -> Int -> (Bool,[UId],Exp) -> IText
              pparg d p (hidden,is,ty) = (pparen (p > 0)( (nsepList (map (ppUId d) is) (t","))  ~. t"::" ~. pPrint d 6 ty)) ~. t(if hidden  then " |->" else " ->")



  pplmds (EAbs bd e1) = t"\\"~.ppBind d 9 bd~.t" ->" : pplmds e1
  pplmds e1           = [ppExp d 8 e1]

  ppCon c pAt es | null es   = ppar 12 $ ppc
                 | otherwise = ppar  9 $ ppc `appArgs` es
    where ppc = ppId d c ~. pAt


  taggedblock :: PPrint a => String -> [a] -> [UId] -> IText
  taggedblock tag ds xs = debFCV xs $ ppar 8 $ if null ds then t(tag++" {}")
    else separate $ [ t(tag++" {")
                    , nest 2 $ separate $ map ((~.(t";")) . pp d) ds , t"}"]
  debFCV xs q = q  -- if deb then q ^. t"FCVars="~. pp d xs else q

  ppar n   = pparen (p > n)
  deb      = d == PDDebug
  readable = d == PDReadable
  go10     = ppExp d 10
  go12     = ppExp d 12
  prArg (True,e) = text "|" ~. ppExp d 10 e
  prArg (False,e) =  ppExp d 10 e
  appArgs q es = separate (q:map (nest 2 . prArg) es)
  andargs q es = separate (q:map (nest 2 . go10) es)
  sepnest q r  = separate [q, nest 2 r]

reducedFor :: Environment -> Exp -> Environment
-- not correct, since indcase may insert free vars in a gamma.
env `reducedFor` e = case e of
      (EStruct   _ _ xs _ _   )-> remwith xs
      --(EStructV  _ _ xs _ _)-> remwith xs
      (EConstV   _   xs    )-> remwith xs
      (Epackage  _ _ xs  _ _  )-> remwith xs
      --(EpackageV _ _ xs _ _)-> remwith xs
      (EMeta  _ _ _ (cit,_) _  _)-> remwith (varScope cit)
      (EMetaV  _  _ xs _   )-> remwith xs
      ( _ )-> removeEq env
  where remwith xs = removeEq (retrieveE env xs)

{- still to go -}

instance PPrint Sort where
    pPrint _ _ (Sort 0) = t"Set"
    pPrint _ _ (Sort 1) = t"Type"
    pPrint _ _ (Sort n) = t("#"++show n)

instance PPrint EProp where
    pPrint _ _ p = t (tail (show p))

instance PPrint LetDef where
    pPrint d p (DSimple def) = pPrint d p def
    pPrint d p (DMutual ds) = (t"mutual " ~. foldr1 (^.) (map (pp d) ds))

instance PPrint Def where
    pPrint d@PDDebug p (Def blocked _ ps c xs tel a (DExp e)) =
      cseparate [sepList (map (pPrint d 0) ps) (t" "),
                 (if blocked then t"newtype " else t"")~.ppUId d c~.ppTel d 10 tel,
                 nest 4 $ t"::"~.pp d a~.t"=",
                 nest 2 $ pp d e,
                 t"fv="~.pPrint d 0 xs]


    pPrint d p (Def blocked _ ps c _ [] a (DExp e)) =
          separate [
             separate [
                separate ((map ((\s -> s ~. t" ") . pp d) ps)++ [(if blocked then t"newtype " else t"") ~. ppUId d c])  ,
                         nest 2 (t" :: " ~. pp d a)],
                    nest 2 (t"= " ~. pp d e)]
    pPrint d p (Def blocked  _ ps c _ tel a (DExp e)) =
          separate [
             separate [
                      separate [separate ((map ((\s -> s ~. t" ") . pp d) ps)
                                          ++[(if blocked then t"newtype " else t"") ~. ppUId d c]),
                                nest 2 (separate (map (ppBind d 12) tel))],
                      nest 2 (t" :: " ~. pp d a)],
             nest 2 (t"= " ~. pp d e)]
    pPrint d p (Def _ _ ps c _ tel a PN) =
          separate[
          separate [cseparate ((map ((\s -> s ~. t" ") . pp d) ps)++ [(t"postulate ")~.ppUId d c]), nest 2 (separate (map (ppBind d p) tel))],
                    nest 2 (t" :: " ~.pp d a)]


    pPrint d p (Def _ _ ps c _ _ a Native) =
          separate[
          cseparate ((map ((\s -> s ~. t" ") . pp d) ps)++ [(t"native")~.ppUId d c]),
                    nest 2 (t" :: " ~.pp d a)]
    pPrint d p (UnTypedDef blocked _ ps c _ (DExp e)) =
          separate [
            separate ((map ((\s -> s ~. t" ") . pp d) ps)++ [(if blocked then t"newtype " else t"") ~. ppUId d c]),
                    nest 2 (t"= " ~. pp d e)]
    pPrint d p (UnTypedDef blocked _ ps c _ PN) =
       cseparate ((map ((\s -> s ~. t" ") . pp d) ps)++ [(t"postulate ")~.ppUId d c])
    pPrint d p (UnTypedDef _ _ ps c _ Native) =
       cseparate ((map ((\s -> s ~. t" ") . pp d) ps)++ [(t"native ")~.ppUId d c])

    pPrint d p (DOpen m as) = t"open " ~. pp d m ~. pp d as

instance PPrint Program where
   pPrint d _ (Program ds) = foldr1 (^.) (map (pp d) ds)


ppBind :: PDetail -> Int -> Bind -> IText
ppBind d p (xs,a) = pparen (p > 0) ( nsepList (map (ppHUId d) xs) (t"," ) ~. t":: " ~. pPrint d 6 a)
   where ppHUId d (hidden,x) = (if hidden then t"|" else t"") ~. ppUId d x


ppTel::PDetail -> Int -> Tel -> IText
ppTel d p ts = nseparate (map (ppBind d p) ts)

--ppSign:: PDetail -> Bind -> IText
--ppSign d (xs,a) = separate [nsepList (map (ppUId d) xs) (t"," )  ~. t" ::", nest 2 (pp d a )]


instance PPrint ESigDef  where
           pPrint d p (ESigAbs (xs,a)) = separate [nsepList (map (ppUId d.snd) xs) (t"," )  ~. t" ::", nest 2 (pp d a )]
           pPrint d p (ESigDefn d') = pp d d'

ppCbs :: PDetail -> [ConBind] -> IText
ppCbs d cbs = sepList (map ppCon cbs) (t" |")
  where ppCon (i, ts) = --separate (ppId d i : map (nest 2 . ppBind d 10) ts)
                        separate [ppId d i, nest 2 $ ppTel d 10 ts]

ppIndCbs :: PDetail -> [IndConBind] -> IText
ppIndCbs d indcbs = sepList (map ppIndCon indcbs) (t" |")
  where ppIndCon ((i,ts),es) = separate
          [ separate (ppId d i : map (nest 2 . pPrint d 10) ts)
          , nest 2 . separate $ t":: _" : map (pPrint d 10) es]



instance PPrint OpenArg where
    pPrint d _ (OpenConst ps c) = separate [separate (map (pp d) ps),ppUId d c]
    pPrint d _ (OpenConstAs ps c1 c2) = sepList (map (pp d) ps) (t " ") ~. ppId d c1 ~. t" = " ~.ppUId d c2
    pPrint d _(OpenConstT ps c a) = sepList (map (pp d) ps) (t " ") ~.  ppUId d c ~. t" :: " ~. pPrint d 6 a
    pPrint d _(OpenConstAsT ps i c a) = sepList (map (pp d) ps) (t " ") ~.  ppUId d c ~. t" :: " ~. pPrint d 6 a ~. t" = "~. ppId d i



instance PPrint OpenArgs where
    pPrint d p (OpenArgs us _) =  t " use "~.sepList (map (pp d) us) (t",")


ppEq' d (x,e) = ppUId d x ~. t" = " ~. pPrint d 0 e
ppEq d (x,e) = case e of
  EVar y _ | x == y -> (ppUId d x)
  _               -> (ppUId d x ~. t"=" ~. pPrint d 0 e)

removeEq :: Environment -> Environment   --- NOT CORRECT
removeEq (E (env,sigma)) = E ( removeEq' env,sigma)
    where removeEq' env =  filter uninteresting env
          uninteresting (x,(EVar x' _)) =  (toId x) /= (toId x')
          uninteresting _          = True

instance PPrint PatArg where
    pPrint d p (PArgT i a) = pparen (p > 0) $ ppUId d i ~.t"::"~. pp d a
    pPrint d _ (PArg i) = ppUId d i


instance PPrint CaseBranch where
   --pPrint PDDebug _ (CBCon i []) = ppId PDDebug i~.t"()"
   --pPrint d p (CBCon i pas) =  pparen (p>9) $ separate (ppId d i : map (pPrint d 10) pas)
     pPrint d p (CBConM i pas _) =
        pparen (p>9) $ separate (ppId d i : map (pPrint d 10) pas)
     pPrint d p (CBLit _ l) =  pPrint d p l


ppEcase :: PDetail -> Int -> Exp -> [(CaseBranch,Exp)] -> IText
ppEcase d p e [] = t"case " ~. pp d e ~. t" of { }"
ppEcase d p e arms
      = pparen (p > 8) $ separate (t"case " ~. pp d e  ~. t" of {" : [nest 2 (separate (map (\arm -> (ppBranch d arm) ~. t";") arms)), t"}"])
 --   | otherwise = (t"case " ~. pp d e ~. t" of ") ^.
 --    (nest 4 (foldr1 (^.) (map (ppBranch d) arms)))
  where ppBranch d (br,e) = separate [pPrint d 10 br ~. t" -> ", nest 2 (pp d e)]

ppAbs :: PDetail -> Exp -> IText
ppAbs d e =  separate (ppLmds d e)
        where ppLmds d (EAbs b e) = (t "\\" ~. ppBind d 9 b ~. t(" ->") )
                                    : (ppLmds d e)
              ppLmds d e = [pPrint d 8 e]


ppProd p d e = pparen (p > 8) $ separate (ppProds p d e)
        where ppProds p d (EProd b'@([(_,x)],b) a) =
                 if isDummyUId x
                     then (pPrint d 9 b ~. t(" ->")) : (ppProds 1 d a)
                     else (ppBind d 9 b' ~. t(" ->")) :  (ppProds 8 d a)
              ppProds p d (EProd b'@(x,b) a) =
                 (ppBind d 9 b' ~. t(" ->")) :  (ppProds 8 d a)
              ppProds _ d e = [pPrint d 8 e]

ppEnv :: PDetail -> Environment -> IText
ppEnv d env = pp d env


{-
instance PPrint Env where
   pPrint PDDebug _ (Env []) = t"{}"
   pPrint d@PDDebug _ (Env env) = t" where {" ~. csepList (map (ppEq d) env) (t",") ~. t"}"
   pPrint d _ (Env []) = t""
   pPrint d _ (Env env) =  t" where " ~. foldr1 (^.) (map (ppEq d) env)
   pPrint d p  (EComp env1 env2) = pPrint d p env1
-}

instance PPrint Environment where
    pPrint d p env =
          if null xes then
                if d == PDDebug then t"{}" else t""
          else if d == PDDebug then t" where {" ~. csepList (map (ppEq d) xes) (t",") ~. t"}"
                  else t" where " ~. foldr1 (^.) (map (ppEq d) xes)
      where xes = listEnv env


ppBinExp d pd e p1 p2 =
  case e of
   EVar x _ -> ppOp' d pd x p1 p2
   EConst c _ -> ppOp' d pd c p1 p2
   _          -> t"Internal error"


-- can't care less.

ppOp'' d@PDDebug pd i no p1 p2 =
         let (p, lp, rp) =
                case getFixity i of
                FInfixl p -> (p, p, p+1)
                FInfixr p -> (p, p+1, p)
                FInfix  p -> (p, p+1, p+1)
         in pparen (d > PDReadable || pd>p)
                  (pPrint d lp  p1 ~. t" " ~. ppInfix d i ~.t("#"++show no)~. t" " ~. pPrint d rp p2)
ppOp'' d pd i no p1 p2 =
         let (p, lp, rp) =
                case getFixity i of
                FInfixl p -> (p, p, p+1)
                FInfixr p -> (p, p+1, p)
                FInfix  p -> (p, p+1, p+1)
         in pparen (d > PDReadable || pd>p)
                  (pPrint d lp p1 ~. t" " ~. ppInfix d i ~. t" " ~. pPrint d rp p2)

ppOp' d pd x = ppOp'' d pd (toId x) (getUIdNo x)

instance PPrint Drhs where
       pPrint d _ (DExp e) = pp d e
       pPrint d _ PN = t"PN"
       pPrint _ _ Native = t"Native"

instance PPrint a => PPrint (Judgement a) where
       pPrint d _ (IsType a) = t"type "~. pp d a
       pPrint d _ (a :! v) = pp d a ~. t" :: " ~. pp d v



pPrintMJudg :: PDetail -> Judgement MetaVar -> IText
pPrintMJudg d (m :! v) = t("?"++show m++" :: ")~. pp d v
pPrintMJudg d (IsType m) = t("?"++show m++" Type")
-- Used for error messages


isBinExp :: Exp -> Bool
isBinExp (EVar x _) = isBinOp (toId x)
isBinExp (EConst c _) = isBinOp (toId c)
isBinExp (EConstV c _) = isBinOp (toId c)
isBinExp otherwise = False

precExp :: Exp -> Int
precExp (EVar _ _) = 12
precExp (EConst  _ _) = 12
precExp (ESort _ _) = 12
precExp (EMeta _ _ _ _ _ _) = 12
precExp PreMeta = 12
precExp (EProj _ _) = 12
--precExp (EProjT _ _) = 12
precExp (EStruct _ _ _ _ _) = 12
precExp (Epackage _ _ _ _ _ ) = 12
precExp (ESig _ _) = 12
precExp (ECon _ [] ) = 12
precExp (EConF _  _ [] ) = 12
precExp (EStop _ e) = precExp e
precExp (EClos _ e) = precExp e
precExp (EProd ([(_,p)],_) _)
     | isDummyUId p = 1
     | otherwise = 9
precExp (EProd (p,_) _) = 9
precExp (EArrow _ e1 e2) = 1
precExp _ = 9


noPar :: Int
noPar = 0


getExpPos :: Exp -> Position
getExpPos (EVar x _) = getUIdPosition x
getExpPos (EConst c _) = getUIdPosition c
getExpPos (ESort pos _) = pos
getExpPos (EAbs b _) = getBindPos b
getExpPos (EProd b _) =  getBindPos b
getExpPos (EArrow _ e1 _) =  getExpPos e1
getExpPos (EApp h _) = getExpPos h
getExpPos (EDef [] e) = getExpPos e
getExpPos (EDef (l:_) _) = getLetDefPos l
getExpPos (ECon n _) = getIdPosition n
getExpPos (EConF n _ _) = getIdPosition n
getExpPos (EData []) = noPosition
getExpPos (EData ((n,_):_)) = getIdPosition n
getExpPos (EIndData  _ (((n, _ ), _ ) :_ )) = getIdPosition n
getExpPos (ECase e _) = getExpPos e
getExpPos (EProj e _) = getExpPos e
--getExpPos (EProjT e _) = getExpPos e
getExpPos (ESig pos _) = pos
getExpPos (EStruct pos _ _ _ _ ) = pos
--getExpPos (EStructV pos _ _ _ _) = pos
getExpPos (Epackage pos _ _ _ _ ) = pos
--getExpPos (EpackageV pos _ _ _ _) = pos
getExpPos (EBinOp e _ _) = getExpPos  e
getExpPos (EMeta _ pos _ _ _ _) = pos
getExpPos PreMeta = noPosition
getExpPos (EStop _ e) = getExpPos e
getExpPos (EClos _ e) = getExpPos e
getExpPos (EConstV c _) = getUIdPosition c
getExpPos (EOpen m _ _) = getExpPos m
--getExpPos (EUndef e) = getExpPos e
--getExpPos (EDefin e) = getExpPos e
getExpPos (ELiteral pos _) = pos
getExpPos _ = noPosition



getExpPosLast :: Exp -> Position
getExpPosLast (EAbs b e) = getExpPosLast e
getExpPosLast (EProd b e) =  getExpPosLast e
getExpPosLast (EApp h []) = getExpPosLast h
getExpPosLast (EApp h es) = getExpPosLast (snd $ last es)
getExpPosLast (EDef _ e) = getExpPosLast e
getExpPosLast (ECon n []) = getIdPosition n
getExpPosLast (ECon n es) = getExpPosLast (snd$ last es)
getExpPosLast (EConF n e []) = getExpPosLast e
getExpPosLast (EConF n _ es) = getExpPosLast (snd$ last es)
getExpPosLast (EProj e x) = getIdPosition x
getExpPosLast (EBinOp _ _ e) = getExpPosLast  e
getExpPosLast (EStop _ e) = getExpPosLast e
getExpPosLast (EClos _ e) = getExpPosLast e
getExpPosLast (EOpen _ _ e) = getExpPosLast e
getExpPosLast e = getExpPos e

getBindPos ((_,c):_,_) = getUIdPosition c
getBindPos (_,_) = error "getBindPos: "

getLetDefPos (DSimple d) = getDefPos d
getLetDefPos (DMutual (d:_)) = getDefPos d
getLetDefPos _ = error "getLetDefPos: "


getDefPos (Def _ _ _ c _ _ _ _) = getUIdPosition c
getDefPos (UnTypedDef _ _ _ c _ _) = getUIdPosition c
getDefPos (DOpen e _) = getExpPos e
