module Agda.Compiler.Alonzo.Main where

import Language.Haskell.Syntax
import Language.Haskell.Pretty

import Agda.Compiler.Alonzo.Haskell
import Agda.Compiler.Alonzo.Debug
import Agda.Compiler.Alonzo.Names

import qualified Agda.Syntax.Concrete.Name as C

import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Scope
import Text.PrettyPrint
import Agda.Syntax.Common

import Control.Monad.State
import Control.Monad.Error

import Data.List as List
import Data.Map as Map

import Agda.Syntax.Abstract.Test
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as CN

import Agda.Interaction.Options
import Agda.Interaction.Monad

import Agda.TypeChecker
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Monad

import System.IO
import Data.List(nub)

-- import Agda.Version

-- | The main function
compilerMain :: IM () -> IM ()
compilerMain typeCheck = do
	typeCheck
	sig <- gets stSignature
        debugSigInfo sig
        let [moduleName] =  keys sig
        builtinMap <- getBuiltinThings
	let sigs = toList sig
	let definitions = mdefDefs (snd (head sigs)) -- :: Map Name Definition
	let defs = toList definitions
        let names = List.map fst defs
        hsdefs <- mapM processDefWithDebug defs
        impNames <- getImports
        let imps = List.map show (List.nub impNames)
        let mainNum = (numOfMainS names)
        let fileBase =  show moduleName
        let moduleString = fileBase
        let hsmod = hsModuleImporting moduleString imps (concat hsdefs)
        liftIO $ outputHsModule fileBase hsmod mainNum
        -- let almod = List.map AlDecl hsdefs
        -- liftIO $ printAlModule moduleString almod
       

numOfMainS :: [Name] -> Maybe Int
numOfMainS [] = Nothing
numOfMainS (n:ns) | isMain n = Just $ numOfName n
                  | otherwise = numOfMainS ns

-- isMain (Name _ (C.Name _ [C.Id "mainS"])) = True
isMain n = (show n == "mainS")

getConArity :: QName -> IM Nat
getConArity qn = do
        definitions <- getDefinitions
        let (Defn ty fv (Constructor np _ isa)) = definitions ! (qnameName qn)
        -- return $ typeArity ty
        return $ arity ty

typeArity :: Type -> Nat
typeArity (El s t) = ar t where
    ar (Pi _ (Abs _ t2)) = typeArity t2 + 1
    ar (Fun a t2) = typeArity t2 + 1
    ar _ = 0


-- returnOne :: Monad m => a -> m [a]
-- returnOne  = return . return

type PState = Nat
initPState = 0
type PM a = State PState a

processArgPats :: [Arg Pattern] -> [HsPat]
processArgPats args = pats where
    pm = mapM processArgPat args
    (pats, pst) =  runState pm initPState
    initPState = 0

processArgPat :: (Arg Pattern) -> PM HsPat
processArgPat (Arg hid pat) = processPat pat

processPat :: Pattern -> PM HsPat
processPat (VarP _) = do
  n <- get 
  put (n+1)
  return $ HsPVar $ HsIdent ("v" ++ (show n))

processPat (ConP qname args) = do 
  let name = qnameName qname   
  hspats <- mapM processArgPat args
  return $ HsPParen $ HsPApp (conQName qname) hspats

processPat (LitP (LitInt _ i)) = return $ HsPLit (HsInt i)
processPat (LitP (LitChar _ c)) = 
  return $  HsPParen $ HsPApp (rtpCon "CharT") [HsPLit (HsChar c)]
processPat (LitP _) = error "Unimplemented literal patttern" -- return HsPWildCard
processPat AbsurdP = return HsPWildCard

           
processBody :: ClauseBody -> PM HsExp
processBody (NoBind cb) = processBody cb 
processBody (Bind (Abs n cb)) = processBody cb

processBody (Body t) = processTerm t >>= (return . hsCast)
processBody NoBody = return hsUndefined

processTerm :: Term -> PM HsExp
processTerm (Var n ts) = do
  cnt <- get
  processVap (hsVar $ "v" ++ (show (cnt - n -1))) ts

processTerm (Def qn ts) = processVap (HsVar $ dfQName qn) ts
processTerm (Con qn ts) = processVap (HsCon $ conQName qn) ts

processTerm (Lam h (Abs n t)) = do
  exp <- processTerm t
  return $ hsLam n exp
processTerm (Lit l) = return $  (processLit l)
processTerm (Pi arg abs) =  error "Unimplemented term: Pi"
processTerm (Fun arg typ) =  error "Unimplemented term: Fun"
processTerm (Sort s) =  error "Unimplemented term: Sort"
processTerm (BlockedV b) =  error "Unimplemented term: Blocked"
processTerm (MetaV _ _) =  error "Can't have metavariables"

-- processTerm t =  return hsUndefined

processLit :: Literal -> HsExp
processLit (LitInt _ i) =  hsPreludeTypedExp "Integer" $ HsLit $ HsInt i
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
unfoldVap p e ((Arg Hidden t):ts) = unfoldVap p e ts 


processDefWithDebug :: (Name,Definition) -> IM [HsDecl]
processDefWithDebug (name,def) = do
     hsdecls <- processDef (name,def)
     return (nameInfo:hsdecls) where
         nameInfo = infoDecl infoName (show name)
         infoName = "name" ++ (show $ numOfName name)

infoDecl :: String -> String -> HsDecl
infoDecl name val = HsFunBind [ HsMatch dummyLoc hsname [] rhs []] where
    rhs = HsUnGuardedRhs $ HsLit $ HsString val 
    hsname = HsIdent name

processClause :: Name -> Int -> Clause -> IM HsDecl
processClause name number (Clause args (body)) = do
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] where
                    decls = []
                    hsid = dfNameSub name number
                    -- pats =  processArgPats  args               
                    pm = mapM processArgPat args
                    (pats, pst) =  runState pm initPState
                    rhs = HsUnGuardedRhs exp
                    (exp, pst2) = runState (processBody body) pst

contClause :: Name -> Int -> Clause -> IM HsDecl
contClause name number (Clause args (body)) = do
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] where
                decls = []
                hsid = dfNameSub name number
                pats = replicate (length args) HsPWildCard
                rhs = HsUnGuardedRhs exp
                exp = HsVar $ UnQual $ dfNameSub name (number+1)
                

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

 
processDef (name,Defn typ fvs (Datatype n [] sort isa)) = do
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

processDef (name,Defn typ fvs (Datatype n cs sort isa)) = do
  cons <- consForName name cs
  arities <- getConArities cs
  return [ddecl cons arities,vdecl]  where
      ddecl cs arities= HsDataDecl  dummyLoc [] (dataName name) (tvars arities) cs []
      tvars arities = take (List.maximum arities) $ List.map HsIdent ["a", "b", "c", "d", "e"]
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs n) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)


processDef def@(name,Defn typ fvs con@(Constructor n qn isa)) = do
    return []

processDef def@(name,Defn typ fvs Axiom) = return []

processDef (name,Defn typ fvs (Primitive info prim expr)) = return $
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
             -- rhs = HsUnGuardedRhs $ error $ "primitive: " ++ (show prim)
             rhs = HsUnGuardedRhs $ HsVar $ rtpQName prim
             decls = []
             hsid = dfName name


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
  let id = nameId $ qnameName qn
  let NameId cn = id
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
  let ns = List.map qnameName qns
  return [definitions ! name | name <- ns]


getDefinitions :: IM Definitions
getDefinitions = do
  sig <- gets stSignature
  let sigs = toList sig
  let definitions = mdefDefs (snd (head sigs)) -- :: Map Name Definition
  return definitions


getConArities cs = mapM getConArity cs