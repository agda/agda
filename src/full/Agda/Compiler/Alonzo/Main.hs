{-# LANGUAGE CPP #-}

module Agda.Compiler.Alonzo.Main where

#include "../../undefined.h"
import Agda.Utils.Impossible

import Debug.Trace(trace)
import Language.Haskell.Syntax
import Language.Haskell.Pretty
import System.FilePath (pathSeparator)

import Agda.Compiler.Alonzo.Haskell
-- import Agda.Compiler.Alonzo.Debug
import Agda.Compiler.Alonzo.Names
import Agda.Compiler.Alonzo.PatternMonad
-- import qualified Agda.Compiler.Alonzo.PatternMonadLift as PML

import qualified Agda.Syntax.Concrete.Name as C

import Agda.Syntax.Internal
import Agda.Syntax.Literal
-- import Agda.Syntax.Scope
import Text.PrettyPrint
import Agda.Syntax.Common
-- import Agda.Syntax.Abstract(Pattern'(..),Pattern)

import Control.Applicative
import Control.Monad.State

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List as List
import Data.Set (Set)
import Data.Map (Map, (!))
import Data.Generics.Text

-- import Agda.Syntax.Abstract.Test
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as CN

import Agda.Interaction.Options
import Agda.Interaction.Monad

import Agda.TypeChecker
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce

import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Pretty

import System.IO
-- import Data.List(nub)

-- import Agda.Version

-- | The main function
compilerMain :: TCM () -> TCM ()
compilerMain typeCheck = ignoreAbstractMode $ do
      typeCheck
      sig <- gets stSignature
      let (moduleName:_) =  Map.keys $ sigSections sig
      withCurrentModule moduleName $ do -- TODO: Hack!
        builtinMap <- getBuiltinThings
	-- let sigs = toList sig
	-- let definitions = mdefDefs (snd (head sigs)) -- :: Map Name Definition
	let definitions = sigDefinitions sig -- :: Map QName Definition
	let defs = Map.toList definitions
        let names = List.map fst defs
        hsdefs <- mapM processDefWithDebug defs
        -- We get more than we need here
        allImps <- map (render . pretty) . Map.keys <$> getVisitedModules
        verboseS "comp.alonzo.import" 20 $ liftIO $ mapM_ (\m -> putStrLn $ "import " ++ m) allImps
        hImps <- getHaskellImports
        let mainNum = (numOfMainS names)
        let fileBase = map pathSep (show moduleName)
              where
                pathSep '.' = pathSeparator
                pathSep c   = c
        let moduleString = show moduleName
        let hsmod = hsModuleImporting moduleString hImps allImps (concat hsdefs)
        liftIO $ outputHsModule fileBase hsmod mainNum
        -- let almod = List.map AlDecl hsdefs
        -- liftIO $ printAlModule moduleString almod

-- TODO: move somewhere else
fromCurrentModule :: QName -> TCM Bool
fromCurrentModule q = do
  m <- qnameFromList . mnameToList <$> currentModule
  return $ moduleId q == moduleId m
  where
    moduleId q = mi
      where NameId _ mi = nameId $ qnameName q

flattenSubmodules :: QName -> TCM QName
flattenSubmodules q = do
  ifM (fromCurrentModule q)
      (return q)
  $ do
    topModules <- map (iModuleName . miInterface) . Map.elems <$>
                    getVisitedModules
    case filter (isInModule q) topModules of
      [top]     -> return $ q { qnameModule = top }
      []        -> error $ "flattenSubmodules: " ++ show q ++ " </- " ++ show topModules
      _ : _ : _ -> __IMPOSSIBLE__

maybeQualName :: (QName -> HsQName) -> (Name -> HsName) -> QName -> PM HsQName
maybeQualName qual unqual q = lift $ do
  ifM (fromCurrentModule q)
      (return $ UnQual (unqual $ qnameName q))
      (qual <$> flattenSubmodules q)

maybeQualConName = maybeQualName conQName conName
maybeQualDefName = maybeQualName dfQName dfName

numOfMainS :: [QName] -> Maybe Nat
numOfMainS [] = Nothing
numOfMainS (n:ns) | isMain (qnameName n) = Just $ numOfQName n
                  | otherwise = numOfMainS ns

-- isMain (Name _ (C.Name _ [C.Id _ "mainS"]) _ _ ) = True
isMain n = (show n == "main")



processDefWithDebug :: (QName,Definition) -> TCM [HsDecl]
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


processDef :: (QName,Definition) -> TCM [HsDecl]
processDef (qname,Defn { theDef = Function { funClauses = clauses } }) =  do
      hsDecls <- foldClauses name 1 clauses
      return [HsFunBind [HsMatch dummyLoc (dfName name) [] rhs hsDecls]] where
                rhs = HsUnGuardedRhs $ HsVar $ UnQual $ dfNameSub name 1
                name = qnameName qname

processDef (qname,Defn { theDef = Datatype{ dataPars = n, dataClause = Nothing, dataCons = [] } }) = do
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

processDef (qname,Defn { theDef = Datatype{ dataPars = n, dataIxs = nind, dataClause = Nothing, dataCons = cs }}) = do
  cons <- consForName name cs
  arities <- getConArities cs
  return [ddecl cons arities,vdecl]  where
      name = qnameName qname
      dataname = dataName name
      ddecl cs arities = HsDataDecl  dummyLoc [] dataname (tvars arities) cs []
      tvars arities = genericTake (List.maximum arities) $ List.map HsIdent letters
      vdecl = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs (n+nind)) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)

-- Records are translated to a data with one cons
processDef (qname, Defn { theDef =
            Record { recPars = n, recFields = fields, recTel = tel } }) =  do
   return [ddecl arity tel,vdecl tel]  where
      name = qnameName qname
      arity = genericLength fields
      ddecl n tel = HsDataDecl  dummyLoc [] dataname (tvars n) [con n] []
      dataname = (dataName name)
      tvars n = genericTake n idents
      con n = HsConDecl dummyLoc (conName  name) args
      idents = List.map HsIdent letters
      args =  List.map (HsUnBangedTy . HsTyVar) $ genericTake arity idents
      vdecl tel = HsFunBind [ HsMatch dummyLoc hsname (nDummyArgs 0) rhs []]
      rhs = HsUnGuardedRhs $ HsVar $ unit_con_name
      hsname = dfName name
      nDummyArgs 0 = []
      nDummyArgs k = (HsPVar $ HsIdent ("v" ++ (show k))) : nDummyArgs (k-1)

processDef def@(qname,Defn { theDef = Constructor{} }) =
    return []

processDef def@(qname,Defn { theDef = Axiom{axHsDef = mhs} }) = return
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
             rhs = HsUnGuardedRhs $ case mhs of
                    Just (HsDefn _ hs) -> hsVar hs
                    _                  -> hsError $ "axiom: " ++ show qname
             decls = []
             hsid = dfName name
             name = qnameName qname

processDef (qname,Defn { theDef = Primitive info prim expr }) = return $
  [HsFunBind [HsMatch dummyLoc hsid  [] rhs decls]] where
             -- rhs = HsUnGuardedRhs $ error $ "primitive: " ++ (show prim)
             rhs = HsUnGuardedRhs $ HsVar $ rtpQName prim
             decls = []
             hsid = dfName name
             name = qnameName qname

processDef (qname, (Defn { theDef = Datatype{dataClause = Just clause} })) = do
           -- liftIO $ putStrLn $ gshow $ clauseBod clause
    mkSynonym (clauseBod clause) where
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
  let args =  List.map (HsUnBangedTy . HsTyVar) $ genericTake arity idents
  return $ HsConDecl dummyLoc (conName $ qnameName qn) args

{-
dummyCon :: Nat -> Nat -> HsConDecl
dummyCon i j = HsConDecl dummyLoc (mangleConName i j) []

mangleConName :: Nat -> Nat -> HsCode
-- mangleConName i j = (HsIdent $ "C"++(show i)++"_"++(show j))
mangleConName i j = (HsIdent $ "C"++(show j))
-}

-- consForData :: QName -> TCM [Definition]
-- consForData qn = undefined

consDefs :: [QName] -> TCM [Definition]
consDefs qns = do
  definitions <- getDefinitions
  return [definitions ! qn | qn <- qns]


processClause :: Name -> Nat -> Clause -> TCM HsDecl
processClause name number clause@(Clause{ clausePerm = perm
                                        , clausePats = args
                                        , clauseBody = body
                                        }) = do
  reportSLn "comp.alonzo.clause" 20 $
    "processClause " ++ show name ++ "\n" ++
    "  perm = " ++ show perm ++ "\n" ++
    "  args = " ++ show args ++ "\n"
  ldefs <- getDefinitions
  let bodyPM = processBody body
      pst0   = initPState clause ldefs
  (exp, pst) <- runStateT bodyPM pst0
  let rhs = HsUnGuardedRhs exp
  (pats, pst2) <- runStateT (processArgPats args) pst
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls]
    where
                    decls = []
                    hsid = dfNameSub name $ fromIntegral number
                    -- pats =  processArgPats  args

contClause :: Name -> Nat -> Clause -> TCM HsDecl
contClause name number (Clause{ clausePats = args, clauseBody = body }) = do
  return $ HsFunBind $ [HsMatch dummyLoc hsid pats rhs decls] where
                decls = []
                hsid = dfNameSub name (fromIntegral number)
                rightLetters =  genericTake (length args) letters
                pats = List.map (HsPVar . HsIdent) rightLetters
                rhs = HsUnGuardedRhs exp
		exp = vecApp expfun expargs
                expfun = hsCast$ HsVar $ UnQual $ dfNameSub name (fromIntegral $ number+1)
                expargs = List.map (HsVar . UnQual . HsIdent) rightLetters

foldClauses :: Name -> Nat -> [Clause] -> TCM [HsDecl]
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

processPat (DotP _) = return HsPWildCard

processPat (ConP qname args) = do
  hsCode <- do
    def <- lift $ theDef <$> getConstInfo qname
    case def of
      Constructor{conHsCode = c} -> return c
      Record{}                   -> return Nothing  -- no COMPILED_DATA for records yet
      _                          -> __IMPOSSIBLE__
  cname <- case hsCode of
        Just (_, h)  -> return $ UnQual $ HsIdent h
        Nothing -> maybeQualConName qname
  hspats <- mapM processArgPat args
  return $ HsPParen $ HsPApp cname hspats

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
	-- cnt <- getPcnt
	addVar
	incPcnt
	processBody cb

processBody (Body t) = processTerm t >>= (return . hsCast)
processBody NoBody = do
	putPlst (repeat HsPWildCard)
	return hsUndefined

processTerm :: Term -> PM HsExp
processTerm (Var n ts) = do
  cnt <- getPcnt
  processVap (hsVar $ "v" ++ (show (cnt - fromIntegral n - 1))) ts

processTerm (Def qn ts) = do
  x <- maybeQualDefName qn
  processVap (HsVar x) ts

-- Check if the con was redefined from other module
-- if so, use the original name
-- !!!
processTerm (Con qn ts) = do
  def <- lift $ theDef <$> getConstInfo qn
  case def of
    Constructor{conHsCode = Just (_, hs)} ->
        processVap (HsCon $ UnQual $ HsIdent hs) ts
    -- Can be a record constructor in which case the def will be for the record.
    _ -> do
      ldefs <- getPDefs
      if (Map.member qn ldefs)
        then do
          definiens <- case theDef <$> Map.lookup qn ldefs of
                          Just df -> return df
                          Nothing -> fail $ "Alonzo: No such definition: " ++ show qn
          case definiens of
            Constructor{conSrcCon = origqn} -> do
              x <- maybeQualConName origqn
              processVap (HsCon x) ts
            _ -> do
              x <- maybeQualConName qn
              processVap (HsCon x) ts
        else do
          x <- maybeQualConName qn
          processVap (HsCon x) ts

processTerm (Lam h (Abs n t)) = do
  cnt <- getPcnt
  incPcnt
  exp <- processTerm t
  return $ hsLam ("v" ++ show cnt)  exp
processTerm (Lit l) = return $  (processLit l)
processTerm (Pi arg abs) = return $ HsVar  unit_con_name
processTerm (Fun arg typ) = return $ HsVar  unit_con_name
processTerm (Sort s) =  return $ HsVar  unit_con_name
processTerm (MetaV _ _) =  error "Can't have metavariables"

-- processTerm t =  return hsUndefined

processLit :: Literal -> HsExp
processLit (LitInt _ i) =  HsApp toNat $ intLit i where
	intLit i = HsParen $ hsPreludeTypedExp "Integer" $ HsLit $ HsInt i
	toNat = HsVar $ Qual (Module "RTP") $ HsIdent "_primIntegerToNat"
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
  lift $ unfoldVap p e ts

unfoldVap :: PState -> HsExp -> [Arg Term] -> TCM HsExp
unfoldVap _ e [] = return e
unfoldVap p e ((Arg NotHidden t):ts) = do
  e1 <- evalStateT (processTerm t) p
  unfoldVap p (hsAp e e1) ts
-- unfoldVap p e ((Arg Hidden t):ts) = unfoldVap p e ts
unfoldVap p e ((Arg Hidden t):ts) = do
  e1 <- evalStateT (processTerm t) p
  unfoldVap p (hsAp e e1) ts



getDefinitions :: TCM Definitions
getDefinitions = do
  sig <- gets stSignature
  let definitions = sigDefinitions sig -- :: Map QName Definition
  idefs <- sigDefinitions <$> getImportedSignature
  return (definitions `Map.union` idefs)



getConArities cs = mapM getConArity cs

getConArity :: QName -> TCM Nat
getConArity qn = do
        Defn _ ty _ _ Constructor{conPars = np} <- getConstInfo qn
	ty' <- normalise ty
        return $ typeArity ty' - np
        -- return $ arity ty'

typeArity :: Type -> Nat
typeArity (El s t) = ar t where
    ar (Pi _ (Abs _ t2)) = typeArity t2 + 1
    ar (Fun a t2) = typeArity t2 + 1
    ar _ = 0

clauseBod :: Clause -> Term
clauseBod c = stripBinds (clauseBody c) where
  stripBinds (Bind (Abs _ r)) = stripBinds r
  stripBinds (NoBind r) = stripBinds r
  stripBinds (Body r) = r
  stripBinds (NoBody) = __IMPOSSIBLE__

letters = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "k", "m", "n", "p","q"]

vecApp :: HsExp -> [HsExp] -> HsExp
vecApp e [] = e
vecApp e (a:as) = vecApp (HsApp e a) as

