{-# LANGUAGE CPP #-}
#include "../../undefined.h"

module Compiler.Alonzo.Main where
import Debug.Trace(trace)
import Language.Haskell.Syntax
import Language.Haskell.Pretty

import Compiler.Alonzo.Haskell
-- import Compiler.Alonzo.Debug
import Compiler.Alonzo.Names
import Compiler.Alonzo.PatternMonad
-- import qualified Compiler.Alonzo.PatternMonadLift as PML

import qualified Syntax.Concrete.Name as C

import Syntax.Internal
import Syntax.Literal
-- import Syntax.Scope
import Text.PrettyPrint
import Syntax.Common
-- import Syntax.Abstract(Pattern'(..),Pattern)

import Control.Monad.State

import Data.Set as Set
import Data.List as List
import Data.Map as Map
import Data.Generics.Text

-- import Syntax.Abstract.Test
import Syntax.Abstract.Name
import qualified Syntax.Concrete.Name as CN

import Interaction.Options
import Interaction.Monad

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Reduce

import Utils.Monad

import System.IO
-- import Data.List(nub)

-- import Version

-- | The main function
compilerMain :: IM () -> IM ()
compilerMain typeCheck = do
	typeCheck
	sig <- gets stSignature
        -- debugSigInfo sig
        let (moduleName:_) =  keys $ sigSections sig
        builtinMap <- getBuiltinThings
	-- let sigs = toList sig
	-- let definitions = mdefDefs (snd (head sigs)) -- :: Map Name Definition       
	let definitions = sigDefinitions sig -- :: Map QName Definition
	let defs = Map.toList definitions
        let names = List.map fst defs
        hsdefs <- mapM processDefWithDebug defs
        impNames <- getImports
        let imps = List.map show (Set.toList impNames)
        let mainNum = (numOfMainS names)
        let fileBase =  show moduleName
        let moduleString = fileBase
        let hsmod = hsModuleImporting moduleString imps (concat hsdefs)
        liftIO $ outputHsModule fileBase hsmod mainNum
        -- let almod = List.map AlDecl hsdefs
        -- liftIO $ printAlModule moduleString almod
       

numOfMainS :: [QName] -> Maybe Int
numOfMainS [] = Nothing
numOfMainS (n:ns) | isMain (qnameName n) = Just $ numOfQName n
                  | otherwise = numOfMainS ns

-- isMain (Name _ (C.Name _ [C.Id _ "mainS"]) _ _ ) = True
isMain n = (show n == "mainS")

getConArity :: QName -> IM Nat
getConArity qn = do
        (Defn _ ty (Constructor np origqn _ isa)) <- getConstInfo qn        
	ty' <- normalise ty
        return $ typeArity ty' - np
        -- return $ arity ty'

processDefWithDebug :: (QName,Definition) -> IM [HsDecl]
processDefWithDebug (qname,def) = do
     def <- instantiateFull def
     hsdecls <- processDef (qname,def)
     return (nameInfo:hsdecls) where
         nameInfo = infoDecl infoName (show name)
         infoName = "name" ++ (show $ numOfName name)
	 name = qnameName qname
        
infoDecl :: String -> String -> HsDecl
infoDecl name val = HsFunBind [ HsMatch dummyLoc hsname [] rhs []] where
    rhs = HsUnGuardedRhs $ HsLit $ HsString val 
    hsname = HsIdent name


processDef :: (QName,Definition) -> IM [HsDecl]
processDef (qname,Defn typ fvs (Function clauses isa)) =  do
      hsDecls <- foldClauses name 1 clauses
      return [HsFunBind [HsMatch dummyLoc (dfName name) [] rhs hsDecls]] where
                rhs = HsUnGuardedRhs $ HsVar $ UnQual $ dfNameSub name 1
                name = qnameName qname
 
processDef (qname,Defn typ fvs (Datatype n nind Nothing [] sort isa)) = do
  return [ddecl,vdecl]  where
      name = qnameName qname
      ddecl = HsDataDecl  dummyLoc [] (dataName name) tvars cons []
      tvars = []
      cons = [HsConDecl dummyLoc (conName name) [] ]
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs n) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs :: Nat -> [HsPat]
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)

processDef (qname,Defn typ fvs (Datatype n nind Nothing cs sort isa)) = do
  cons <- consForName name cs
  arities <- getConArities cs
  return [ddecl cons arities,vdecl]  where
      name = qnameName qname
      dataname = dataName name
      ddecl cs arities = HsDataDecl  dummyLoc [] dataname (tvars arities) cs []
      tvars arities = take (List.maximum arities) $ List.map HsIdent letters
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs (n+nind)) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)

-- Records are translated to a data with one cons
processDef (qname, Defn typ fvs (Record n clauses fields tel sort isa)) =  do
   return [ddecl arity tel,vdecl tel]  where
      name = qnameName qname
      arity = length fields
      ddecl n tel = HsDataDecl  dummyLoc [] dataname (tvars n) [con n] []
      dataname = (dataName name)
      tvars n = take n idents
      con n = HsConDecl dummyLoc (conName  name) args
      idents = List.map HsIdent letters
      args =  List.map (HsUnBangedTy . HsTyVar) $ take arity idents
      vdecl tel = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs 0) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)
	
processDef def@(qname,Defn typ fvs con@(Constructor n origqn qn isa)) =
    return []

-- FIXME
processDef def@(qname,Defn typ fvs Axiom) = return []

processDef (qname,Defn typ fvs (Primitive info prim expr)) = return $
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
             -- rhs = HsUnGuardedRhs $ error $ "primitive: " ++ (show prim)
             rhs = HsUnGuardedRhs $ HsVar $ rtpQName prim
             decls = []
             hsid = dfName name
             name = qnameName qname

processDef (qname, (Defn typ fvs (Datatype _ _ (Just clause) _ _ _))) = do
           -- liftIO $ putStrLn $ gshow $ clauseBody clause 
    mkSynonym (clauseBody clause) where
    name = qnameName qname
    mkSynonym (Lam _ (Abs _ t)) = mkSynonym t
    mkSynonym (Def rhsqname args) = return [ddecl, vdecl] where
      ddecl = HsTypeDecl loc dname [] typ
      moduleName = qnameModule rhsqname
      hsModuleName = Module $ moduleStr moduleName
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs 0) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      loc = dummyLoc
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)
      dname = dataName name
      typ = HsTyCon $ Qual hsModuleName $ dataName $ qnameName rhsqname
    mkSynonym t = __IMPOSSIBLE__
{-          do
              liftIO $ putStrLn $ gshow t 
              return []
-}

{-
  t <- normalise $ Def qname []
  mkSynonym t where
    name = qnameName qname
    mkSynonym (Lam _ (Abs _ t)) = mkSynonym t
    mkSynonym (Def newqn args) = return [ddecl, vdecl] where
      ddecl = HsTypeDecl loc dname [] typ
   
      loc = dummyLoc
      dname = dataName name
      typ = HsTyCon $ UnQual $ dataName $ qnameName newqn
    mkSynonym t = do
              liftIO $ putStrLn $ gshow t 
              return []
-}


-- error "Unimplemented: Datatype from module"

{-
processDef (name,Defn typ fvs _) = return $
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
                    rhs = HsUnGuardedRhs hsUndefined
                    decls = []
                    hsid = dfName name
-}


consForName dname qns = mapM (processCon dname)  qns

times :: Nat -> a -> [a]
times 0 x = []
times n x = x:(times (n-1) x)

processCon dname qn = do
  -- let id = nameId $ qnameName qn
  -- let NameId cn = id
  arity <- getConArity qn
  -- let arg = HsUnBangedTy $ HsTyCon unit_tycon_name
  let arg = HsUnBangedTy $ HsTyVar $ HsIdent "a"
  let idents =  List.map HsIdent letters
  let args =  List.map (HsUnBangedTy . HsTyVar) $ take arity idents
  return $ HsConDecl dummyLoc (conName $ qnameName qn) args

{-
dummyCon :: Int -> Int -> HsConDecl
dummyCon i j = HsConDecl dummyLoc (mangleConName i j) []

mangleConName :: Int -> Int -> HsName
-- mangleConName i j = (HsIdent $ "C"++(show i)++"_"++(show j))
mangleConName i j = (HsIdent $ "C"++(show j))
-}

-- consForData :: QName -> IM [Definition]
-- consForData qn = undefined

consDefs :: [QName] -> IM [Definition]
consDefs qns = do
  definitions <- getDefinitions
  return [definitions ! qn | qn <- qns]


processClause :: Name -> Int -> Clause -> IM HsDecl
processClause name number clause@(Clause args (body)) = do
  ldefs <- getDefinitions
  let bodyPM = processBody body
  let (exp, pst) =  runState bodyPM (initPState clause ldefs)
  let rhs = HsUnGuardedRhs exp
  let (pats, pst2) = runState (processArgPats args) pst
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] 
    where
                    decls = []
                    hsid = dfNameSub name number
                    -- pats =  processArgPats  args               
                    
contClause :: Name -> Int -> Clause -> IM HsDecl
contClause name number (Clause args (body)) = do
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] where
                decls = []
                hsid = dfNameSub name number
                rightLetters =  take (length args) letters
                pats = List.map (HsPVar . HsIdent) rightLetters
                rhs = HsUnGuardedRhs exp
		exp = vecApp expfun expargs
                expfun = hsCast$ HsVar $ UnQual $ dfNameSub name (number+1)
                expargs = List.map (HsVar . UnQual . HsIdent) rightLetters

foldClauses :: Name -> Nat -> [Clause] -> IM [HsDecl]
foldClauses name n [] = return []
foldClauses name n [c] = do
        decl <- processClause name n c
        return [decl]
foldClauses name n (c:cs) = do
	head <- processClause name n c
        cont <- contClause name n c
	tail <- foldClauses name (n+1) cs
	return (head:cont:tail)

processArgPats :: [Arg Pattern] -> PM [HsPat]
processArgPats args = mapM processArgPat args

processArgPat :: (Arg Pattern) -> PM HsPat
processArgPat (Arg hid pat) = processPat pat

processPat :: Pattern -> PM HsPat
processPat (VarP _) = do
  pats  <- getPlst
  case pats of
        [] -> do 
	   c <- getPclause
	   error $ "Oops! empty pattern list in\n" ++ (gshow c)
	(p:ps) -> do
	  putPlst ps
	  return p

processPat (ConP qname args) = do 
  let name = qnameName qname   
  hspats <- mapM processArgPat args
  return $ HsPParen $ HsPApp (conQName qname) hspats

processPat (LitP (LitInt _ i)) = return $ HsPLit (HsInt i)
processPat (LitP (LitChar _ c)) = 
  return $  HsPParen $ HsPApp (rtpCon "CharT") [HsPLit (HsChar c)]
processPat (LitP _) = error "Unimplemented literal patttern" 
-- processPat (AbsurdP _) = return HsPWildCard

           
processBody :: ClauseBody -> PM HsExp
processBody (NoBind cb) = do 
        addWildcard
	processBody cb 
processBody (Bind (Abs name cb)) = do
	cnt <- getPcnt
	addVar (cnt)
	incPcnt
	processBody cb

processBody (Body t) = processTerm t >>= (return . hsCast)
processBody NoBody = do
	putPlst (repeat HsPWildCard)
	return hsUndefined

processTerm :: Term -> PM HsExp
processTerm (Var n ts) = do
  cnt <- getPcnt
  processVap (hsVar $ "v" ++ (show (cnt - n - 1))) ts

processTerm (Def qn ts) = processVap (HsVar $ dfQName qn) ts

-- Check if the con was redefined from other module
-- if so, use the original name
-- !!!
processTerm (Con qn ts) = do
            ldefs <- getPDefs
            if (Map.member qn ldefs) 
              then do 
                (Defn _ _ definiens) <- Map.lookup qn ldefs
                case definiens of
                 (Constructor n origqn qn isa) -> 
                       --trace ( "Good: " ++ (show qn)  ++ (gshow definiens)) $
                     processVap (HsCon $ conQName origqn) ts
                 _ ->       -- trace ( "Careful: " ++ (show qn)  ++ (gshow definiens)) $
                         processVap (HsCon $ conQName qn) ts
              else processVap (HsCon $ conQName qn) ts

processTerm (Lam h (Abs n t)) = do
  cnt <- getPcnt
  incPcnt
  exp <- processTerm t
  return $ hsLam ("v" ++ show cnt)  exp
processTerm (Lit l) = return $  (processLit l)
processTerm (Pi arg abs) = return $ HsVar  unit_con_name
processTerm (Fun arg typ) = return $ HsVar  unit_con_name
processTerm (Sort s) =  return $ HsVar  unit_con_name
processTerm (BlockedV b) =  error "Unimplemented term: Blocked"
processTerm (MetaV _ _) =  error "Can't have metavariables"

-- processTerm t =  return hsUndefined

processLit :: Literal -> HsExp
processLit (LitInt _ i) =  HsApp toNat $ intLit i where
	intLit i = HsParen $ hsPreludeTypedExp "Int" $ HsLit $ HsInt i
	toNat = HsVar $ Qual (Module "RTP") $ HsIdent "_primIntToNat"
processLit (LitFloat _ f) =  hsPreludeTypedExp "Double" $ 
						HsLit $ HsFrac $ toRational f
-- processLit (LitFloat _ f) =  HsApp (HsVar $ rtpCon "FloatT")
--                                   (HsLit $ HsFrac $ toRational f)
processLit (LitString _ s) =  HsLit $ HsString s
processLit (LitChar _ c) =  HsApp (HsVar $ rtpCon "CharT")
                                  (HsLit $ HsChar c)

processVap :: HsExp -> [Arg Term] -> PM HsExp
processVap e ts = do
  p <- get
  return $ unfoldVap p  e ts

unfoldVap :: PState -> HsExp -> [Arg Term] -> HsExp
unfoldVap _ e [] = e
unfoldVap p e ((Arg NotHidden t):ts) = unfoldVap p (hsAp e e1) ts where
 e1 = evalState (processTerm t) p
-- unfoldVap p e ((Arg Hidden t):ts) = unfoldVap p e ts 
unfoldVap p e ((Arg Hidden t):ts) = unfoldVap p (hsAp e e1) ts where
 e1 = evalState (processTerm t) p


processDefWithDebug :: (QName,Definition) -> IM [HsDecl]
processDefWithDebug (qname,def) = do
     -- let name = qnameName qname
     hsdecls <- processDef (name,def)
     return (nameInfo:hsdecls) where
         nameInfo = infoDecl infoName (show name)
         infoName = "name" ++ (show $ numOfName name)
	 name = qnameName qname
infoDecl :: String -> String -> HsDecl
infoDecl name val = HsFunBind [ HsMatch dummyLoc hsname [] rhs []] where
    rhs = HsUnGuardedRhs $ HsLit $ HsString val 
    hsname = HsIdent name

processClause :: Name -> Int -> Clause -> IM HsDecl
processClause name number clause@(Clause args (body)) = do
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] where
                    decls = []
                    hsid = dfNameSub name number
                    -- pats =  processArgPats  args               
                    bodyPM = processBody body
                    (exp, pst) =  runState bodyPM (initPState clause)
                    rhs = HsUnGuardedRhs exp
                    (pats, pst2) = runState (processArgPats args) pst

contClause :: Name -> Int -> Clause -> IM HsDecl
contClause name number (Clause args (body)) = do
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] where
                decls = []
                hsid = dfNameSub name number
                rightLetters =  take (length args) letters
                pats = List.map (HsPVar . HsIdent) rightLetters
                rhs = HsUnGuardedRhs exp
		exp = vecApp expfun expargs
                expfun = hsCast$ HsVar $ UnQual $ dfNameSub name (number+1)
                expargs = List.map (HsVar . UnQual . HsIdent) rightLetters

foldClauses :: Name -> Nat -> [Clause] -> IM [HsDecl]
foldClauses name n [] = return []
foldClauses name n [c] = do
        decl <- processClause name n c
        return [decl]
foldClauses name n (c:cs) = do
	head <- processClause name n c
        cont <- contClause name n c
	tail <- foldClauses name (n+1) cs
	return (head:cont:tail)

processDef :: (Name,Definition) -> IM [HsDecl]
processDef (name,Defn typ fvs (Function clauses isa)) = 
    -- mapM (processClause name) clauses
    do
        hsDecls <- foldClauses name 1 clauses
        return [HsFunBind [HsMatch dummyLoc (dfName name) [] rhs hsDecls]] where
                rhs = HsUnGuardedRhs $ HsVar $ UnQual $ dfNameSub name 1

 
processDef (name,Defn typ fvs (Datatype n nind Nothing [] sort isa)) = do
  return [ddecl,vdecl]  where
      ddecl = HsDataDecl  dummyLoc [] (dataName name) tvars cons []
      tvars = []
      cons = [HsConDecl dummyLoc (conName name) [] ]
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs n) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs :: Nat -> [HsPat]
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)

processDef (name,Defn typ fvs (Datatype n nind Nothing cs sort isa)) = do
  cons <- consForName name cs
  arities <- getConArities cs
  return [ddecl cons arities,vdecl]  where
      ddecl cs arities= HsDataDecl  dummyLoc [] (dataName name) (tvars arities) cs []
      tvars arities = take (List.maximum arities) $ List.map HsIdent letters
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs (n+nind)) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)

-- Records are translated to a data with one cons
processDef (name, Defn typ fvs (Record n clauses fields tel sort isa)) =  do
   -- liftIO $ print arity
   -- liftIO $ print fields
   return [ddecl arity tel,vdecl tel]  where
	arity = length fields
	ddecl n tel = HsDataDecl  dummyLoc [] (dataName name) 
                                    (tvars n) [con n] []
	tvars n = take n letters
       	con n = HsConDecl dummyLoc (conName  name) args
  	letters =  List.map HsIdent ["a", "b", "c", "d", "e"]
  	args =  List.map (HsUnBangedTy . HsTyVar) $ take arity letters
      	vdecl tel = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs 0) rhs []]
	rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      	hsname = dfName name
      	nDummyArgs 0 = []
      	nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)
	
processDef def@(name,Defn typ fvs con@(Constructor n origqn qn isa)) = do
    return []

processDef def@(name,Defn typ fvs Axiom) = return []

processDef (name,Defn typ fvs (Primitive info prim expr)) = return $
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
             -- rhs = HsUnGuardedRhs $ error $ "primitive: " ++ (show prim)
             rhs = HsUnGuardedRhs $ HsVar $ rtpQName prim
             decls = []
             hsid = dfName name


processDef (_, Defn _ _ (Datatype _ _ (Just _) _ _ _)) = error "Unimplemented: Datatype from module"

{-
processDef (name,Defn typ fvs _) = return $
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
                    rhs = HsUnGuardedRhs hsUndefined
                    decls = []
                    hsid = dfName name
-}


consForName dname qns = mapM (processCon dname)  qns

times :: Nat -> a -> [a]
times 0 x = []
times n x = x:(times (n-1) x)

processCon dname qn = do
  -- let id = nameId $ qnameName qn
  -- let NameId cn = id
  arity <- getConArity qn
  -- let arg = HsUnBangedTy $ HsTyCon unit_tycon_name
  let arg = HsUnBangedTy $ HsTyVar $ HsIdent "a"
  let letters =  List.map HsIdent ["a", "b", "c", "d", "e"]
  let args =  List.map (HsUnBangedTy . HsTyVar) $ take arity letters
  return $ HsConDecl dummyLoc (conName $ qnameName qn) args

{-
dummyCon :: Int -> Int -> HsConDecl
dummyCon i j = HsConDecl dummyLoc (mangleConName i j) []

mangleConName :: Int -> Int -> HsName
-- mangleConName i j = (HsIdent $ "C"++(show i)++"_"++(show j))
mangleConName i j = (HsIdent $ "C"++(show j))
-}

-- consForData :: QName -> IM [Definition]
-- consForData qn = undefined

consDefs :: [QName] -> IM [Definition]
consDefs qns = do
  definitions <- getDefinitions
  return [definitions ! qn | qn <- qns]


getDefinitions :: IM Definitions
getDefinitions = do
  sig <- gets stSignature
  -- let sigs = toList sig
  -- let definitions = mdefDefs (snd (head sigs)) -- :: Map Name Definition
  let definitions = sigDefinitions sig -- :: Map QName Definition
  return definitions


getConArities cs = mapM getConArity cs

getConArity :: QName -> IM Nat
getConArity qn = do
        (Defn _ ty (Constructor np origqn _ isa)) <- getConstInfo qn        
	ty' <- normalise ty
        return $ typeArity ty' - np
        -- return $ arity ty'

typeArity :: Type -> Nat
typeArity (El s t) = ar t where
    ar (Pi _ (Abs _ t2)) = typeArity t2 + 1
    ar (Fun a t2) = typeArity t2 + 1
    ar _ = 0


letters = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "k", "m", "n", "p","q"]

vecApp :: HsExp -> [HsExp] -> HsExp
vecApp e [] = e
vecApp e (a:as) = vecApp (HsApp e a) as