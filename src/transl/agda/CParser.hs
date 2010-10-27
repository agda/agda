-- | Parsers for CSyntax
import Data.List(nub)
import Parse
import BinParse
import FString(getFString, StrTable)
import PreStrings(fsStar, fsComma, fsRArrow, fsBRArrow,fsImpl)
import Position
import Error
import CSyntax
import Id
import Lex
import Literal
import AgdaTrace
import Monads(Error,raise)
import MetaVars(preMetaVar)
import PluginType (Plugin(..))
import MiscId(commaId)
--import AgdaPretty  -- just for debugging
--import PPrint      -- just for debugging

infix 6 >>>> , >>>>>
type CParser a = Parser [Token] a

pProgram :: CParser CProgram
pProgram = many pModule >>- CProgram


pLetDefs =
      --trace "LDs" $
      block (pLetDef pBindId)


pModule :: CParser CModule
pModule = l L_module ..+ pModId +.+ pPArgs +.+  pPackageBody >>>> CModule


-- pNativeLine = l L_native ..+ string' +.. sm

--pInterface :: CParser (CInterface, StrTable)
--pInterface = (l L_interface ..+ l L_use ..+ sepBy pModId cm +.+ l L_in ..+
--            pSign pModId +.. sm >>> CInterface) +.+ eof

pType = pExpr

pExpr :: CParser CExpr
pExpr =
        --trace "E" $
        exp0 +.+ many comment >>> foldr (Ccomment False)

{-
pExprStart :: CParser CExpr
pExprStart =
       --trace "S" $
       exp9  +.+ many comment >>> foldr (Ccomment False)
-}

exp0 :: CParser CExpr
exp0 =
       --trace "0" $
       binop getFixity mkBin pOper exp10

mkBin e1 op e2 =
    if isRArrow op  then CArrow False e1 e2
    else if isBRArrow op then CArrow True e1 e2
    else CBinOp e1 op e2


pB p = p `into` \ (xs,a)->
                 rarrow         .> CArg (map ((,) False) xs) a
             |!! brarrow        .> CArg (map ((,) True) xs) a



pB' p = p `into` \ xsas ->
                 rarrow         .> (False,xsas)
             |!! brarrow        .> (True,xsas)





exp10 :: CParser CExpr
exp10 =
      --trace "A" $
            l L_lam ..+ pB' pPBind +.+ pExpr >>>
                     (\(h,CBind xs a) e  -> cLam [(h,CBind [x] a) | x<- xs] e)
        |!! l L_let ..+ block (pLetDef pBindId) +.+ l L_in ..+ pExpr    >>> Clet
        |!! l L_case ..+ pExpr +.+ l L_of ..+ block pCaseArm        >>> Ccase
#ifdef NEWSYNTAX

#else
        |!! l L_open ..+ pExpr +.+ pOpenArgs +.+ l L_in ..+ pExpr >>>> Copen



        |!! l L_data ..+ pSummands                                      >>- CSum
        |!! l L_idata ..+  pIndSummands                  >>- (CIndSum [])
#endif
        |!! l L_sig +.+ block (pSign pBindId)                >>> CProduct
        |!! l L_external +.+ (many1 string') +.+ (many aexp)      >>>> (\p -> \(name:opts) -> \es -> (CExternal (Plugin p name (concat opts) es ())))
            -- Should only be one or two strings
        |!! l L_do +.+ pDoBlock                                         >>> CDo
        |!! l L_if ..+ exp0 +.+ l L_then ..+ exp0 +.+ l L_else ..+ exp0 >>>> Cif
        ||! pB pPArgsT +.+ pExpr                                                >>> CUniv
        ||! aexp +.+ many abexp                                         >>> cApply


pOpenArgs :: CParser COpenArgs
pOpenArgs =  l L_use ..+ pOArgs     >>-  COpenArgs


pOArgs :: CParser [COArg]
pOArgs = sepBy pOArg cm



pOArg :: CParser COArg
pOArg = ( many pProp +.+ pBindId ) `into`
        \ (ps,i) ->
           (eq ..+ pBindId                                        >>- (\i' -> COArgAs ps i' i)
           ||! (dc ..+ pExpr) `into` (\a ->  eq ..+ pBindId >>- (\i' -> COArgAsT ps i' a i)
                                            ||! succeed    (COArgT ps i a))
           ||! succeed                                                   (COArg ps i))


{-
        \ (ps,i) ->
           (eq ..+ pBindId                                        >>- (\i' -> COArgAs ps i' i)
           ||! (dc ..+ pExpr +.+ eq ..+ pBindId >>- (\(a,i') -> COArgAsT ps i' a i))

-}

-- Is this a problem? MT says that it conflicts with Ilya syntax???
abexp =  l L_bar ..+ aexp               >>- (\x->(True,x))
       |!! aexp                 >>- (\x->(False,x))



aexp :: CParser CExpr
aexp =
        --trace "a" $
        aexp' +.+ many (l L_dot ..+ pBindId)                            >>> foldl CSelect

aexp' :: CParser CExpr
aexp' =
        --trace "a'" $  -- "'"
        comment +.+ aexp'                       >>> (Ccomment True)
#ifdef NEWSYNTAX
        ||! pId                                 >>- CVar
#else
        ||! pId `into` (\ i ->
                        l L_at ..+ l L_uscore       .>  (CCConS i)
                        ||!  l L_at ..+ aexp        >>- CCCon i
                        ||! succeed (CVar i))
#endif
        ||! lp ..+  pCmId +.. rp                     >>- CVar
        ||! lp ..+ sepBy1 pExpr cm +.. rp            >>- cBinOp commaId
        ||! lb +.+ sepBy pExpr cm +.. rb            >>> CList
        ||! pTYPE +.+ oNum                          >>>> CStar
        ||! l L_Type                                >>- cType
        ||! l L_Set                                 >>- cSet
        ||! pMeta False
        ||! many pProp +.+ l L_struct +.+ block (pLetDef pBindId)               >>>> CRecord
        ||! integer
        ||! string
        ||! char

--pDoBlock :: CParser [CBind]
--pDoBlock = testp "<do-block>" okBlk (block pDoBind)
--  where okBlk [] = False
--        okBlk bs = case last bs of CBind_ _ -> True; _ -> False

--pDoBind :: CParser CBind
--pDoBind =   pPArg +.+ l L_larrow ..+ pExpr                            >>> CBind
--        ||! l L_let ..+ block (pLetDef pBindId)                               >>- CBLet
  --   ||! pExpr                                                        >>- CBind_

pDoBlock :: CParser [CDoBind]
pDoBlock = block pDoBind

pDoBind :: CParser CDoBind
pDoBind =   pBindId +.+ l L_larrow ..+ pExpr                        >>> CDoBind
        ||! l L_let ..+ block (pLetDef pBindId)                     >>- CDoLet
        ||! pExpr                                                   >>- CDoBind_


block :: CParser a -> CParser [a]
block p =
          --trace "bl" $
          startBlock ..+ hBlock p

hBlock :: CParser a -> CParser [a]
hBlock p =
           --trace "hB" $
           lc ..+ sepBy p dsm +.. osm +.. rc

block1 :: CParser a -> CParser [a]
block1 p =
           --trace "bl1" $
           startBlock ..+ hBlock p

hBlock1 :: CParser a -> CParser [a]
hBlock1 p =
            --trace "hB1" $
            lc ..+ sepBy1 p dsm +.. osm +.. rc


pTYPE = l L_star

pCaseArm :: CParser (CPat, CExpr)
pCaseArm =  pAPat +.+ rarrow ..+ pExpr

pSummands :: CParser [(Id, [CArg])]
pSummands = sepBy pSummand (l L_bar)

pSummand :: CParser (Id, [CArg])
pSummand = pBindId +.+ ( many (pPArgsBT False))                    >>> (,)

pSummand' :: CParser (Id, [CArg])
pSummand' = pBindId +.+ (pPArgsBT  False)                   >>> \i -> \a -> (i,[a])

pIndSummands :: CParser CIndSummands
pIndSummands = sepBy pIndSummand (l L_bar)

pExplInds :: CParser CIndSummands
pExplInds = sepBy pExplInd (l L_bar)

pIndSummand :: CParser CIndSummand
pIndSummand = pSummand `into` \ (c,cas1) ->
              pIndSummandTyp `into` \ es ->
              succeed (CIndImpl (c,cas1) (map ((,) False) es))


pExplInd :: CParser CIndSummand
pExplInd = pSummand `into` \ (c,cas1) ->
               pExplTyp `into` \ (n,es) ->
               succeed (CIndExpl (c,cas1) n es)

pIndSummandTyp :: CParser [CExpr]
pIndSummandTyp = (l L_over ..+  block aexp )
                  ||! dc ..+  (l L_uscore ..+ many aexp)
                 ||! succeed []

pExplTyp :: CParser (Id,[(Bool,CExpr)])
pExplTyp = dc ..+  pId +.+ many abexp


pPackageBody :: CParser CPackageBody
pPackageBody =
            --trace "PBd" $
            eq ..+ pExpr                      >>- CPackageInstance
            ||! many pProp +.+ l L_where +.+ block (pLetDef pBindId)     >>>> CPackageDef


--pOpenArgs :: CParser COpenArgs
--pOpenArgs


pSign :: CParser Id -> CParser CSign
--sepBy1 pBindId cm +.+ dc ..+ pType +.. rp             >>- (\ (is, t) -> [CArg i t | i <- is])



pSign pi =  pDefn pi                                                    >>- CSignDef
        ||! sepBy1 pi cm +.+ dc ..+ pType               >>>  CSign

--      ||! l L_type ..+ pi +.+ many pPArg                              >>> CSignType

pLetDef :: CParser Id -> CParser CLetDef
pLetDef p =
        --trace "LD" $
        l L_mutual ..+ block1 (pDef p)                              >>-  CMutual

        ||! comment                                                >>- CLetDefComment
        ||! pDef p                                                      >>- CSimple

pDef :: CParser Id -> CParser CDef
pDef pi =
         --trace "Def" $
             comment                                        >>- CDefComment
        |!! l L_class ..+ pPClassArg pi +.+ pClassRhs
                >>> (\as -> \ (export,sds) -> CDef [] (CClass as export sds))

        ||! many pProp +.+ osm ..+ pDefn pi                             >>> CDef


pProp :: CParser CProp
pProp =     l L_public                                                  .> Cpublic
        |!! l L_private                                                 .> Cprivate
        |!! l L_abstract                                                .> Cabstract
        |!! l L_concrete                                                .> Cconcrete


pDefn :: CParser Id -> CParser CDefn
pDefn pi =
        --trace "Defn" $
            l L_data ..+        pi +.+ pPArgs +.+ pPMaybeExpr +.+ eq ..+ pSummands >>>>> Cdata

        |!! l L_idata ..+     pi +.+ pPArgs' +.+ dc ..+ pExpr +.+ l L_where ..+ block (pExplInd) >>>>> Cidata
        |!! l L_newtype ..+ pi +.+ pPArgs +.+ dc ..+ pType +.+ eq ..+ pSummand' >>>>>  Cnewtype
        |!! l L_type ..+ pi +.+ pPArgs +.+ eq ..+ pExpr >>>>  Ctype
        |!! l L_native ..+ pi +.+  dc ..+ pType           >>> CNative
        |!! l L_axiom ..+ pi +.+ pPArgs +.+ dc ..+ pType           >>>> CAxiom
        |!! l L_package ..+ pi +.+ pPArgs +.+  pPackageBody >>>> CPackage
        |!! l L_open ..+ pExpr +.+  pOpenArgs   >>> COpen
        |!! l L_instance ..+ pi +.+ pPArgs +.+ dc ..+ pPInstanceArg +.+ l L_where ..+  block (pLetDef pBindId) >>>>> CInstance
       ||! pi +.+ pPArgs' +.+ dc ..+ pType
             `into` (\ (i,(as,e)) ->
                       eq ..+ pExpr      >>-  CValueT i as e
                     ||! dsm ..+ pClause1 i pi   >>-  CValueS i as e )
                       {- allows for a def like
                           foo(n::N)::N -> N;
                           foo x = n
                        -}
#ifdef NEWSYNTAX

#else
       ||!  pi +.+ eq ..+ pExpr                        >>>   CValue
#endif


--pClauses :: Id -> CParser Id -> CParser [CClause]
--pClauses i pi = many (dsm ..+ pClause i pi)

--pClauses1 :: Id -> CParser Id -> CParser [CClause]
--pClauses1 i pi = sepBy1 (pClause i pi) dsm

pClause1 :: Id -> CParser Id -> CParser CClause
pClause1 i pi = pClause i pi
--
--pClauses :: Id -> CParser Id -> CParser [CClause]
--pClauses i pi = pClause i pi

pClause :: Id -> CParser Id -> CParser CClause
pClause i pi =
        piEq i pi ..+ many pBAPat +.+ eq ..+ pExpr            >>> CClause
    ||! pAPat +.+ piEq i pOper ..+ pAPat +.+ eq ..+ pExpr     >>>>
                (\a1 -> \a2  -> \e -> CClause [(False,a1),(False,a2)] e)

piEq :: Id -> CParser Id -> CParser Id
piEq i pi = testp (getIdString i) (\i'->i==i') pi


pPatArg :: CParser CPatArg
pPatArg = lp ..+ pBindId +.+ dc ..+ pExpr +.. rp >>>  CPatT
      ||! pBindId >>- CPatId


pPatApply :: CParser CPat
pPatApply = pBindId +.+ many pPatArg                            >>> (\i -> \l -> (CPCon i (map CPVar l)))


pPatOp :: CParser CPat
pPatOp = binop getFixity mkBinP (pOper |!! pCmId) pAPat
  where mkBinP p1 op p2 = CPCon op [p1, p2]

pBAPat :: CParser (Bool, CPat)
pBAPat = l L_bar ..+ pAPat                                            >>- (\x->(True,x))
         |!!   pAPat                                                        >>- (\x->(False,x))

pAPat :: CParser CPat
pAPat =   -- pBindId `into` (\ i ->
--                                -- l L_at ..+ pAPat                   >>- CPAs (CArg i)
--                            succeed                                 (CPVar (CArg i)))
            pPatArg    >>- CPVar
        ||! lp ..+ pPatApply +.. rp
        ||! lp ..+ pPatOp +.. rp
--        ||! char                                                      >>- (\ (CLit p l) -> CPLit p l)


pPArgsT :: CParser ([Id],CExpr)
pPArgsT = lp ..+ sepBy1 pBindId cm +.+ dc ..+ pType +.. rp

pPBind :: CParser CBind
pPBind =
          many1 pBindId   >>- (\xs -> CBind  xs Nothing )
      ||! pPArgsT      >>- (\(xs,t) -> CBind xs (Just t))




pPArgsBT :: Bool -> CParser CArg
pPArgsBT def = lp ..+ sepBy1 (pBBindId def) cm +.+ dc ..+ pType +.. rp    >>> CArg

pPArgs :: CParser CArgs
pPArgs = many (pPArgsBT False)

#ifdef NEWSYNTAX
pPArgs' :: CParser CArgs
pPArgs' = many (pPArgsBT True)
#else
pPArgs' :: CParser CArgs
pPArgs' = many (pPArgsBT False)
#endif


pPClassArg :: CParser Id -> CParser CClassArg
pPClassArg pi = pi +.+ pPArgs +.+ dc ..+ pExpr
       `into` (\(c,(as,t)) -> l L_extends ..+  pPArgs >>- CClassArg c as t
                            |!! succeed (CClassArg  c as t []))
pClassRhs :: CParser (Bool, [CSign])
pClassRhs = l L_where ..+   block (pSign pBindId) >>- (\sds -> (False,sds))
        |!! l L_exports ..+   block (pSign pBindId) >>- (\sds -> (True,sds))

pPMaybeExpr ::  CParser (Maybe CExpr)
pPMaybeExpr  = dc ..+ pExpr >>- Just
            ||! succeed Nothing

pPInstanceArg :: CParser CInstanceArg
pPInstanceArg = pType >>- CInstanceArg



--pMeta :: Bool -> CParser CExpr
--pMeta b = l L_bar ..+ (pMeta' b True)
-- ||! pMeta' b False

pMeta :: Bool -> CParser CExpr
pMeta b  = l L_uscore >>- (\p -> CMeta p b (Just True) preMetaVar)
       ||! l L_meta   >>- (\p -> CMeta p b (Just False) preMetaVar)

pOper :: CParser Id
pOper = pOpId ||! l L_bquote ..+ pVarId +.. l L_bquote



pModId, pVarId,pConId, pBindId, pOpId, pCmId :: CParser Id
pModId = lcp "<modid>" (\p x->case x of L_modid fs -> Just (mkId p fs); _ -> Nothing)

pBindId = pVarId
      ||! lp ..+ pOpId +.. rp



pBindIds = many pBindId

pBBindId def = l L_bar ..+ pBindId >>- (,) True
       |!! l L_excl ..+ pBindId >>- (,) False
       |!! pBindId          >>- (,) def



pVarId = lcp "<id>" (\p x->case x of L_varid fs -> Just (mkId p fs); _ -> Nothing)

pOpId = lcp "<op>" (\p x->case x of L_varsym fs -> Just (mkId p fs); _ -> Nothing)
pCmId = lcp "<op>" (\p x->case x of L_comma  -> Just (mkId p fsComma); _ -> Nothing)

pConId = lcp "<id>"  (\p x->case x of L_conid fs -> Just (mkId p fs); _ -> Nothing)


pId :: CParser Id
pId = pBindId ||!  pModId

-- Utilities

p >>>> f = p >>- \ (x,(y,z)) -> f x y z
p >>>>> f = p >>- \ (x,(y,(z,w))) -> f x y z w


eq = l L_eq
lp = l L_lpar
rp = l L_rpar
lb = l L_lsquare
rb = l L_rsquare
cm = l L_comma
lc = l L_lcurl
rc = l L_rcurl
sm = l L_semi
dc = l L_dcolon
osm = sm ||! succeed noPosition
dsm = sm +.. osm
eof = lcp "<EOF>" (\p x->case x of L_eof x -> Just x; _ -> Nothing)

l :: LexItem -> CParser Position
l li =  token ( \ls->
        case ls of
        Token p li' : ls' -> if li==li' then Right (p, ls') else Left (prLexItem li) )

getPos :: CParser Position
getPos = token ( \ls->
        case ls of
        Token p _ : _ -> Right (p, ls))

lcp :: String -> (Position -> LexItem -> Maybe a) -> CParser a
lcp s f =
        token $ \ls->
        case ls of
        Token p li : ls' ->
            case f p li of
            Just x  -> Right (x, ls')
            Nothing -> Left s

startBlock :: CParser ()
startBlock =
        --trace "sB" $
        token $ \ ts ->
        case ts of
        t@(Token p@(Position _ _ c) li) : ts' | li /= L_lcurl ->
            Right ((), Token p L_lcurl : t : col c ts')
        _ -> Right ((), ts)
  where col c (t@(Token p@(Position _ _ c') _) : ts) | c' == c = Token p L_semi : t : col c ts
        col c (t@(Token p@(Position _ _ c') _) : ts) | c' >  c = t : col c ts
--      col c (t@(Token p@(Position _ _ c') (L_comment _)) : ts) | c' < c = t : col c ts
        col c (t@(Token p@(Position _ _ c') _) : ts) | c' <  c = Token p L_rcurl : t : ts
        col c [] = [Token noPosition L_rcurl] -- XXX bad position

errSyntax :: [String] -> [Token] -> EMsg
errSyntax ss ts =
        case ts of
        Token p (L_error em) : _ -> (p, em)
        Token p li           : _ -> (p, ESyntax (showt (prLexItem li)) (map showt (nub ss)))
                where showt t = case show t of
                                    "\"\\\\\"" -> "\"\\\""
                                    s -> s

oNum :: CParser (Int, Int)
oNum =     integer' `into` (\ n ->
                            l L_dot ..+ integer' >>- (\m -> (n,m))
                            ||! succeed (n,n))
       ||! succeed (0,0)

comment :: CParser Comment
comment = lcp "<comment>" (\p x->case x of L_comment s -> Just s; _ -> Nothing)

integer' :: CParser Int
integer' = lcp "<integer>" (\p x->case x of L_integer i-> Just (fromInteger i); _ -> Nothing)

string' :: CParser String
string' = lcp "<string>" (\p x->case x of L_string s-> Just s; _ -> Nothing)

integer = lcp "<integer>" (\p x->case x of L_integer i-> Just (CLit p (LInteger    i)); _ -> Nothing)
string  = lcp "<string>"  (\p x->case x of L_string  s-> Just (CLit p (LString s)); _ -> Nothing)
char    = lcp "<char>"    (\p x->case x of L_char    c-> Just (CLit p (LChar   c)); _ -> Nothing)
rational   = lcp "<rational>"    (\p x->case x of L_rational   c-> Just (CLit p (LRational   c)); _ -> Nothing)

--string' = string >>- \ (CLit _ (LString s)) -> s

star    = lcp "*"   (\p x->case x of L_varsym fs | fs == fsStar    -> Just p; _ -> Nothing)
--cm      = lcp ","   (\p x->case x of L_varsym fs | fs == fsComma   -> Just p; _ -> Nothing)
rarrow  = lcp "->"  (\p x->case x of L_varsym fs | fs == fsRArrow  -> Just p; _ -> Nothing)
brarrow = lcp "|->" (\p x->case x of L_varsym fs | fs == fsBRArrow -> Just p; _ -> Nothing)
rimpl = lcp "=>" (\p x->case x of L_varsym fs | fs == fsImpl -> Just p; _ -> Nothing)



idP :: String -> CParser ()
idP str = token f where f ((Token _ (L_varid x) :ts))|getFString x==str = Right ((),ts)
                        f _ = Left str


finalP :: CParser a -> [Token] -> Error (a,StrTable)
finalP p ts = chkParse (p +.+ eof ) ts
{-
  do
     --traceM$"finalP:enter"
     tmp@(e,_) <- chkParse (p +.+ eof) ts
     --traceM$"finalP:exit"
     return tmp
-}

chkParse :: (CParser (a, StrTable))  -> [Token] -> Error (a, StrTable)
chkParse p ts =
    case parse p ts of
        Right ((m,_):_) -> return m
        Left  (ss,ts)   -> let (Token _ (L_eof tbl)) = last ts
                           in  raise (errSyntax (filter (not . null ) ss) ts)
