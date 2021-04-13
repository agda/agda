-- | Main module for Go backend.

module Agda.Compiler.GoLang.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Trans
import Control.Monad (zipWithM)

import Data.Char     ( isSpace, chr, ord, isLetter, isDigit, isAsciiUpper)
import Data.Foldable ( forM_ )
import Data.List     ( intercalate, partition )
import Data.Set      ( Set )
import Data.Maybe (fromMaybe)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Text as T

import System.Directory   ( createDirectoryIfMissing, setCurrentDirectory  )
import System.Environment ( setEnv )
import System.FilePath    ( splitFileName, (</>) )
import System.Process     ( callCommand )

import Paths_Agda

import Agda.Interaction.Options
import Agda.Interaction.Imports ( isNewerThan )

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name ( isNoName )
import Agda.Syntax.Abstract.Name
  ( ModuleName, QName,
    mnameToList, qnameName, qnameModule, nameId, qnameToList0, uglyShowName )
import Agda.Syntax.Internal
import Agda.Syntax.Literal ( Literal(..) )
import Agda.Syntax.Internal.Names (namesIn)
import qualified Agda.Syntax.Treeless as T
import Agda.Compiler.Treeless.NormalizeNames

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Reduce ( instantiateFull, reduce )
import Agda.TypeChecking.Substitute as TC ( TelV(..), raise, subst )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rewriting
import Agda.TypeChecking.Primitive (getBuiltinName)

import Agda.Utils.Function ( iterate' )
import Agda.Utils.List ( headWithDefault )
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( boolToMaybe, catMaybes, caseMaybeM, whenNothing )
import Agda.Utils.Monad ( ifM, when )
import Agda.Utils.Null  ( null )
import Agda.Utils.Pretty (prettyShow, render)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.IO.Directory
import Agda.Utils.IO.UTF8 ( writeFile )
import Agda.Utils.Singleton ( singleton )

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateDefaults
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Compiler.Treeless.Erase ( computeErasedConstructorArgs, typeWithoutParams )
import Agda.Compiler.Treeless.Subst ()
import Agda.Compiler.Backend (Backend(..), Backend'(..), Recompile(..))

import Agda.Compiler.GoLang.Syntax
  (GoQName, Exp(Self,Global,Undefined,Null,String,Char,Integer,GoInterface,GoStruct,GoStructElement,Local,Lambda,GoFunction, GoSwitch, GoIf, GoCase, GoCreateStruct, Const, GoMethodCall, GoVar, GoLet, BinOp, ReturnExpression, GoMethodCallParam),
    LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId,MemberIndex), GoImports(GoImportUsage, GoImportField, GoImportDeclarations), Module(Module, modName), Comment(Comment), TypeId(TypeId, ConstructorType, GenericFunctionType, EmptyType, EmptyFunctionParameter, FunctionType, FunctionReturnElement, PiType), GoFunctionSignature(OuterSignature, InnerSignature),
    modName
  )
import Agda.Compiler.GoLang.Substitution

import qualified Agda.Compiler.GoLang.Pretty as GoPretty

import Agda.Utils.Impossible (__IMPOSSIBLE__)

--------------------------------------------------
-- Entry point into the compiler
--------------------------------------------------

goBackend :: Backend
goBackend = Backend goBackend'

goBackend' :: Backend' GoOptions GoOptions GoModuleEnv Module (Maybe Exp)
goBackend' = Backend'
  { backendName           = goBackendName
  , backendVersion        = Nothing
  , options               = defaultGoOptions
  , commandLineFlags      = goCommandLineFlags
  , isEnabled             = optGoCompile
  , preCompile            = goPreCompile
  , postCompile           = goPostCompile
  , preModule             = goPreModule
  , postModule            = goPostModule
  , compileDef            = goCompileDef
  , scopeCheckingSuffices = False
  , mayEraseType          = const $ return False
      -- Andreas, 2019-05-09, see issue #3732.
      -- If you want to use Go data structures generated from Agda
      -- @data@/@record@, you might want to tell the treeless compiler
      -- not to erase these types even if they have no content,
      -- to get a stable interface.
  }

--- Options ---

data GoOptions = GoOptions
  { optGoCompile  :: Bool
  , optGoOptimize :: Bool
  , optGoMinify   :: Bool
      -- ^ Remove spaces etc. See https://en.wikipedia.org/wiki/Minification_(programming).
  , optGoVerify   :: Bool
      -- ^ Run generated code through interpreter.
  , optGoTransform   :: Bool    
  }

defaultGoOptions :: GoOptions
defaultGoOptions = GoOptions
  { optGoCompile  = False
  , optGoOptimize = False
  , optGoMinify   = False
  , optGoVerify   = False
  , optGoTransform = False
  }

goCommandLineFlags :: [OptDescr (Flag GoOptions)]
goCommandLineFlags =
    [ Option [] ["go"] (NoArg enable) "compile program using the go backend"
    , Option [] ["go-optimize"] (NoArg enableOpt) "turn on optimizations during Go code generation"
    -- Minification is described at https://en.wikipedia.org/wiki/Minification_(programming)
    , Option [] ["go-minify"] (NoArg enableMin) "minify generated Go code"
    , Option [] ["go-verify"] (NoArg enableVerify) "except for main module, run generated Go modules through `node` (needs to be in PATH)"
    , Option [] ["go-transform"] (NoArg enableGoTransform) "transform go to go2"
    ]
  where
    enable       o = pure o{ optGoCompile  = True }
    enableOpt    o = pure o{ optGoOptimize = True }
    enableMin    o = pure o{ optGoMinify   = True }
    enableVerify o = pure o{ optGoVerify   = True }
    enableGoTransform o = pure o{ optGoTransform   = True }

--- Top-level compilation ---

goPreCompile :: GoOptions -> TCM GoOptions
goPreCompile opts = return opts

-- | After all modules have been compiled, copy RTE modules and verify compiled modules.

goPostCompile :: GoOptions -> IsMain -> Map.Map ModuleName Module -> TCM ()
goPostCompile opts _ ms = do
  reportSDoc "function.go" 6 $ " ms:" <+> (text . show) ms
  forM_ ms $ \ Module{ modName } -> do
    mdir <- compileDir
    liftIO $ setCurrentDirectory mdir
    reportSDoc "function.go" 5 $ " mdir:" <+> (text . show) mdir
    reportSDoc "function.go" 5 $ " goFile:" <+> (text . show) (go2goFilePath modName)
    let comm = unwords [ "go", "tool", "go2go", "translate", (go2goFilePath modName) ]
    liftIO $ callCommand comm
--- Module compilation ---

type GoModuleEnv = Maybe CoinductionKit

goPreModule :: GoOptions -> IsMain -> ModuleName -> FilePath -> TCM (Recompile GoModuleEnv Module)
goPreModule _opts _ m ifile = ifM uptodate noComp yesComp
  where
    uptodate = liftIO =<< isNewerThan <$> outFile_ <*> pure ifile

    noComp = do
      m   <- prettyShow <$> curMName
      out <- outFile_
      reportSLn "compile.go" 1 $ repl [m, ifile, out] "Compiling g <<0>> in <<1>> to <<2>>"
      Recompile <$> coinductionKit

    yesComp = do
      m   <- prettyShow <$> curMName
      out <- outFile_
      reportSLn "compile.go" 1 $ repl [m, ifile, out] "Compiling go <<0>> in <<1>> to <<2>>"
      Recompile <$> coinductionKit

goPostModule :: GoOptions -> GoModuleEnv -> IsMain -> ModuleName -> [Maybe Exp] -> TCM Module
goPostModule opts _ isMain _ defs = do
  m             <- goMod <$> curMName
  is            <- map (goMod . fst) . iImportedModules <$> curIF
  reportSDoc "function.go" 10 $ "\n m:" <+> (text . show) m
  reportSDoc "function.go" 10 $ "\n is:" <+> (text . show) is
  let importDeclarations = GoImportDeclarations $ (map goImportDecl is) ++ ["math/big", "helper"]
  let importUsages = (map goImportUsg is) ++ [(GoImportUsage "big"), (GoImportUsage "helper")] 
  let mod = Module m (importDeclarations : ([GoImportField] ++ importUsages)) es
  writeModule mod
  mdir <- compileDir
  when (optGoTransform opts) $ do
    liftIO $ setCurrentDirectory mdir
    reportSDoc "function.go" 5 $ " mdir:" <+> (text . show) mdir
    let comm = unwords [ "go", "tool", "go2go", "translate", (go2goFilePath m) ]
    reportSDoc "function.go" 6 $ "\n cmd:" <+> (text . show) comm
    liftIO $ callCommand comm
  return mod
  where
  es       = catMaybes defs
  main     = MemberId "main"
  -- Andreas, 2020-10-27, only add invocation of "main" if such function is defined.
  -- This allows loading of generated .go files into an interpreter
  -- even if they do not define "main".


goCompileDef :: GoOptions -> GoModuleEnv -> IsMain -> Definition -> TCM (Maybe Exp)
goCompileDef opts kit _isMain def = definition (opts, kit) (defName def, def)

--------------------------------------------------
-- Naming
--------------------------------------------------

prefix :: [Char]
prefix = "golang2/src"

goMod :: ModuleName -> GlobalId
goMod m = GlobalId (prefix : map prettyShow (mnameToList m))

goFileName :: GlobalId -> String
goFileName (GlobalId ms) =  "src/" ++ (intercalate "/" (tail (init ms))) ++ (goFileName' (tail (init ms))) ++ (intercalate "_" (tail ms)) ++ "/" ++ (intercalate "_" (tail ms) ++ ".go2")

goFileName' :: [String] -> String
goFileName' = \case
  [] -> ""
  _ -> "/"

go2goFilePath :: GlobalId -> String
go2goFilePath (GlobalId ms) = "src/" ++ (intercalate "/" (tail (init ms))) ++ (goFileName' (tail (init ms))) ++ (intercalate "_" (tail ms)) ++ "/" ++ (intercalate "_" (tail ms) ++ ".go2")

goImportDecl :: GlobalId -> String
goImportDecl (GlobalId ms) = (intercalate "/" (init ms)) ++ "/" ++ (intercalate "_" (tail ms))

goImportUsg :: GlobalId -> GoImports
goImportUsg (GlobalId ms) = GoImportUsage $ intercalate "_" (tail ms)

goMember :: Name -> MemberId
goMember n
  -- Anonymous fields are used for where clauses,
  -- and they're all given the concrete name "_",
  -- so we disambiguate them using their name id.
  | isNoName n = MemberId ("_" ++ show (nameId n))
  | otherwise  = MemberId $ prettyShow n

global' :: QName -> TCM (Exp, GoQName)
global' q = do
  i <- iModuleName <$> curIF
  modNm <- topLevelModuleName (qnameModule q)
  let
    -- Global module prefix
    qms = mnameToList $ qnameModule q
    -- File-local module prefix
    localms = drop (length $ mnameToList modNm) qms
    nm = fmap goMember $ List1.snoc localms $ qnameName q
  if modNm == i
    then return (Self, nm)
    else return (Global (goMod modNm), nm)

global :: QName -> TCM (Exp, GoQName)
global q = do
  d <- getConstInfo q
  case d of
    Defn { theDef = Constructor { conData = p } } -> do
      getConstInfo p >>= \case
        -- Andreas, 2020-10-27, comment quotes outdated fact.
        -- anon. constructors are now M.R.constructor.
        -- We could simplify/remove the workaround by switching "record"
        -- to "constructor", but this changes the output of the Go compiler
        -- maybe in ways that break user's developments
        -- (if they link to Agda-generated Go).
        -- -- Rather annoyingly, the anonymous constructor of a record R in module M
        -- -- is given the name M.recCon, but a named constructor C
        -- -- is given the name M.R.C, sigh. This causes a lot of hoop-jumping
        -- -- in the map from Agda names to Go names, which we patch by renaming
        -- -- anonymous constructors to M.R.record.
        Defn { theDef = Record { recNamedCon = False } } -> do
          (m,ls) <- global' p
          return (m, ls <> singleton (MemberId "record"))
        _ -> global' (defName d)
    _ -> global' (defName d)

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

type EnvWithOpts = (GoOptions, GoModuleEnv)

definition :: EnvWithOpts -> (QName,Definition) -> TCM (Maybe Exp)
definition kit (q,d) = do
  reportSDoc "compile.go" 10 $ "compiling def:" <+> prettyTCM q
  (_,ls) <- global q
  d <- instantiateFull d

  definition' kit q d (defType d) ls

defGoDef :: Definition -> Maybe String
defGoDef def =
  case defCompilerPragmas goBackendName def of
    [CompilerPragma _ s] -> Just (dropEquals s)
    []                   -> Nothing
    _:_:_                -> __IMPOSSIBLE__
  where
    dropEquals = dropWhile $ \ c -> isSpace c || c == '='

ftype :: TypeId -> TypeId
ftype (ConstructorType v t) = FunctionType v t
ftype (FunctionType v t) = FunctionType v t
ftype (GenericFunctionType v t) = GenericFunctionType v t
ftype (PiType a b) = PiType a b
ftype _ = EmptyType

fReturnTypes :: [TypeId] -> [TypeId]
fReturnTypes ((ConstructorType v t) : tail) = (FunctionReturnElement t) : (fReturnTypes tail)
fReturnTypes (head : tail) = EmptyType : (fReturnTypes tail)
fReturnTypes [] = []

createSignature :: MemberId -> [TypeId] -> String -> [String] -> TCM (Exp -> Exp) 
createSignature fname [] resName genTypes = do
  return $ GoFunction [(OuterSignature fname genTypes EmptyFunctionParameter [] (TypeId resName))]
createSignature fname (firstArg : tail) resName genTypes = do
  return $ GoFunction ((OuterSignature fname genTypes (ftype firstArg) (fReturnTypes tail) (TypeId resName)) : (createSignatureInner tail resName))

createSignatureInner :: [TypeId] -> String -> [GoFunctionSignature]
createSignatureInner (head : tail) retName = (InnerSignature (ftype head) (fReturnTypes tail) (TypeId retName)) : (createSignatureInner tail retName)
createSignatureInner [] retName = []

countFalses :: [Bool] -> Nat
countFalses [] = 0
countFalses (False : xs) = 1 + countFalses xs
countFalses (_ : xs) = countFalses xs

extractReturnType :: Exp -> TCM TypeId
extractReturnType (GoFunction signatures _) = extractReturnType' $ head signatures
extractReturnType _ = __IMPOSSIBLE__  

extractReturnType' :: GoFunctionSignature -> TCM TypeId
extractReturnType' (OuterSignature _ _ _ _ retType) = return retType
extractReturnType' _ = __IMPOSSIBLE__  

retrieveGenericArguments :: [TypeId] -> [String]
retrieveGenericArguments [] = []
retrieveGenericArguments ((GenericFunctionType n t) : tail) = t : (retrieveGenericArguments tail)
retrieveGenericArguments ((PiType a b) : tail) = ((retrieveGenericArguments [a]) ++ (retrieveGenericArguments [b])) ++ (retrieveGenericArguments tail)
retrieveGenericArguments (_ : tail) = retrieveGenericArguments tail

definition' :: EnvWithOpts -> QName -> Definition -> Type -> GoQName -> TCM (Maybe Exp)
definition' kit q d t ls = do
  case theDef d of
    -- coinduction
    Constructor{} | Just q == (nameOfSharp <$> snd kit) -> do
      reportSDoc "compile.go" 30 $ " con1:" <+> (text . show) d
      return Nothing
    Function{} | Just q == (nameOfFlat <$> snd kit) -> do
      reportSDoc "compile.go" 30 $ " f1:" <+> (text . show) d
      return Nothing
    DataOrRecSig{} -> __IMPOSSIBLE__
    Axiom -> return Nothing

    GeneralizableVar{} -> return Nothing
    PrimitiveSort{} -> return Nothing

    Function{} | otherwise -> do
      reportSDoc "function.go" 5 $ "compiling fun:" <+> prettyTCM q
      fname <- liftTCM $ fullName q
      caseMaybeM (toTreeless T.EagerEvaluation q) (pure Nothing) $ \ treeless -> do
        used <- getCompiledArgUse q
        funBody <- eliminateCaseDefaults =<<
          eliminateLiteralPatterns
          (convertGuards treeless)
        (goArg, (ConstructorType _ name)) <- goTelApproximationFunction t used
        let count = countFalses used 
        let genericTypesUsed = retrieveGenericArguments goArg
        reportSDoc "function.go" 30 $ " genericTypesUsed:" <+> (text . show) genericTypesUsed
        reportSDoc "function.go" 30 $ " compiled treeless fun:" <+> pretty funBody 
        (TelV tel res) <- telView t
        let args = map (snd . unDom) (telToList tel)
        reportSDoc "function.go" 30 $ " goArg:" <+> (text . show) goArg
        reportSDoc "function.go" 30 $ " args:" <+> (text . show) args
        let (body, given) = lamView funBody
              where
                lamView :: T.TTerm -> (T.TTerm, Int)
                lamView (T.TLam t) = (+1) <$> lamView t
                lamView t = (t, 0)
            etaN = length $ dropWhile id $ reverse $ drop given used
        funBody' <- compileTerm kit ((length goArg) - 1) goArg
            $ T.mkTApp (raise etaN body) (T.TVar <$> [etaN-1, etaN-2 .. 0])
        functionSignature <- createSignature fname goArg name genericTypesUsed
        let emptyFunction = functionSignature Null
        returnType <- extractReturnType emptyFunction
        reportSDoc "function.go" 25 $ "\n functionSignature:" <+> (text . show) functionSignature 
        reportSDoc "function.go" 25 $ "\n funBody':" <+> (text . show) funBody'   
        reportSDoc "function.go" 30 $ "\n given:" <+> (text . show) given
        reportSDoc "function.go" 30 $ "\n etaN:" <+> (text . show) etaN
        return $ Just $ applyReturnType returnType (functionSignature funBody') 
    Primitive{primName = p} -> return Nothing
    Datatype{ dataPathCons = _ : _ } -> do
      reportSDoc "compile.go" 30 $ " data tupe:" <+> (text . show) q
      s <- render <$> prettyTCM q
      typeError $ NotImplemented $
        "Higher inductive types (" ++ s ++ ")"
    Datatype{} -> do
      reportSDoc "compile.go" 40 $ " data tupe2:" <+> (text . show) d
      let nameee = uglyShowName (qnameName q)
      reportSDoc "compile.go" 30 $ "\n nameee:" <+> (text . show) nameee
      computeErasedConstructorArgs q
      name <- liftTCM $ fullName q
      return (Just $ GoInterface $ name)
    Record{} -> do
        computeErasedConstructorArgs q
        return Nothing

    c@Constructor{conData = p, conPars = nc, conSrcCon = ch, conArity = cona} -> do
      (ff, gg) <- global q
      (ff2, gg2) <- global' q
      reportSDoc "compile.go" 5 $ "compiling gg2:" <+> (text . show) gg2
      reportSDoc "compile.go" 5 $ "compiling gg:" <+> (text . show) gg
      let np = arity t - nc
      erased <- getErasedConArgs q
      let inverseErased = map not erased
      reportSDoc "compile.go" 20 $ " erased:" <+> (text . show) inverseErased
      constName <- fullName q
      (goArg, goRes) <- goTelApproximation t inverseErased
      reportSDoc "compile.go" 20 $ " goTypes:" <+> (text . show) goArg
      case theDef d of
        dt -> return (Just $ GoStruct constName goArg)
    AbstractDefn{} -> __IMPOSSIBLE__
--------------------------------------------------
-- Writing out a Golang module
--------------------------------------------------

fullName :: QName -> TCM MemberId
fullName q = do
  (m,ls) <- global q
  case m of 
    Self -> return $ MemberId $ encode $ constructorName' ls
    Global (GlobalId id) -> do
      return $ MemberId $ (intercalate "_" (tail id)) ++ "." ++ (encode $ constructorName' ls)
    _ -> __IMPOSSIBLE__  

encode :: [Char] -> String
encode [] = []
encode name@(c : tail) = do
  case isAsciiUpper c of
    True -> encodeChars (name)
    False -> encodeChars $ 'F' : name

encodeChars :: [Char] -> String
encodeChars (c : tail) = (encodeChar c) ++ (encodeChars tail)
encodeChars [] = []

encodeChar :: Char -> String
encodeChar c = do
  case isValidChar c of
    True -> [c]
    False -> "u" ++ (show (ord c))

isValidChar :: Char -> Bool
isValidChar c = (isLetter c) || ('_' == c) || (isDigit c) 

constructorName' :: GoQName -> String
constructorName' s = do
  let ((MemberId name), remaining) = List1.uncons s
  case remaining of
    Nothing -> name
    Just rem -> name ++ "_" ++ (constructorName' rem)

map2 :: [Bool] -> [a] -> [a]
map2 bs as = map snd $ filter fst $ zip bs as

getVarName :: Nat -> String
getVarName n = [chr ((ord 'A') + n)]

compileAlt :: EnvWithOpts -> Nat -> [TypeId] -> Nat -> T.TAlt -> TCM Exp
compileAlt kit argCount args switchVar = \case
  T.TACon con ar body -> do
    erased <- getErasedConArgs con
    let nargs = ar - length (filter id erased)
    compiled <- compileTerm kit (nargs + argCount) args (eraseLocalVars erased body)
    memId <- fullName con
    let cas = GoCase memId switchVar argCount nargs [compiled]
    return cas
  _ -> __IMPOSSIBLE__

filterErased :: T.TTerm -> Bool
filterErased = \case
  T.TErased -> False
  _ -> True

getPiTypedMethodParams :: TypeId -> [Exp] -> Exp
getPiTypedMethodParams (PiType (ConstructorType name typeId) _ ) (exp : _) = GoMethodCallParam exp (TypeId typeId)
getPiTypedMethodParams (PiType (GenericFunctionType name typeId) _ ) (exp : _) = GoMethodCallParam exp (TypeId typeId)
getPiTypedMethodParams _ _ = __IMPOSSIBLE__

getTypelessMethodCallParams :: [Exp] -> [Exp]
getTypelessMethodCallParams [] = []
getTypelessMethodCallParams (head : tail) = (GoMethodCallParam head EmptyType) : (getTypelessMethodCallParams tail)

compileTerm :: EnvWithOpts -> Nat -> [TypeId] -> T.TTerm -> TCM Exp
compileTerm kit paramCount args t = do
  reportSDoc "function.go" 30 $ " compile term:" <+> (text . show) t
  let (tx, ts) = T.tLetView t
  reportSDoc "function.go" 50 $ " compile tx:" <+> (text . show) tx
  reportSDoc "function.go" 50 $ " compile ts:" <+> (text . show) ts
  go t
  where
    go :: T.TTerm -> TCM Exp
    go = \case
      T.TVar x -> return $ GoVar $ paramCount - x
      T.TDef q -> do
        d <- getConstInfo q
        name <- liftTCM $ fullName q
        case theDef d of
          -- Datatypes and records are erased
          Datatype {} -> return (String "*")
          Record {} -> return (String "*")
          --in case of qname, we call a function with no arguments
          _ -> return $ GoMethodCall name []
      T.TApp (T.TCon q) [x] | Just q == (nameOfSharp <$> snd kit) -> do
        reportSDoc "function.go" 30 $ "\n sharp"
        unit
      T.TApp (T.TCon q) x -> do
        reportSDoc "function.go" 30 $ "\n contructor"
        l <- fullName q
        transformedArgs <- mapM go (filter filterErased x)
        return $ GoCreateStruct l transformedArgs
      T.TApp (T.TDef q) x -> do
        reportSDoc "function.go" 15 $ "function definition call"
        reportSDoc "function.go" 15 $ "\n q:" <+> (text . show) q
        name <- liftTCM $ fullName q
        transformedArgs <- mapM go (filter filterErased x)
        return $ GoMethodCall name (getTypelessMethodCallParams transformedArgs)
      T.TApp (T.TVar v1) x  -> do
        reportSDoc "function.go" 30 $ "function var function"
        transformedArgs <- mapM go (filter filterErased x)
        let typedMethodParam = getPiTypedMethodParams (args !! (paramCount - v1)) transformedArgs
        return $ GoMethodCall (MemberId (getVarName (paramCount - v1))) [typedMethodParam]  
      T.TApp (T.TPrim T.PIf) [c, x, y]  -> do
        GoIf <$> (go c) <*> (go x) <*> (go y)
      T.TApp (T.TPrim primType) [x, y]  -> do
        BinOp <$> (go (T.TPrim primType)) <*> (go x)  <*> (go y)  
      T.TApp t' xs | Just f <- getDef t' -> do
        used <- either getCompiledArgUse (\x -> fmap (map not) $ getErasedConArgs x) f
        reportSDoc "function.go" 30 $ "\n just f used:" <+> (text . show) used
        reportSDoc "function.go" 30 $ "\n just f:" <+> (text . show) (getDef t')
        reportSDoc "function.go" 30 $ "\n TApp xs:" <+> (text . show) xs
        unit
      T.TApp t xs -> do
        reportSDoc "function.go" 30 $ "\n TApp xs:" <+> (text . show) xs
        unit
      T.TLam t -> do
        go t
      T.TLet varDef nextExp -> do
        GoLet <$> (return (getVarName (paramCount + 1))) <*> (go varDef) <*> (compileTerm kit (paramCount + 1) args nextExp)
      T.TLit l -> do
        reportSDoc "function.go" 30 $ "\n TLit l:" <+> (text . show) l 
        return $ literal l
      T.TCon q -> do
        d <- getConstInfo q
        reportSDoc "function.go" 30 $ "\n TCon d:" <+> (text . show) d
        name <- liftTCM $ fullName q
        return $ GoCreateStruct name []
      T.TCase sc ct def alts | T.CTData dt <- T.caseType ct -> do
        cases <- mapM (compileAlt kit paramCount args (paramCount - sc)) alts
        return $ GoSwitch (GoVar (paramCount - sc)) cases
      T.TCase _ _ _ _ -> __IMPOSSIBLE__
      T.TPrim p -> do
        reportSDoc "function.go" 30 $ "\n prim:" <+> (text . show) p 
        return $ compilePrim p
      T.TUnit -> unit
      T.TSort -> unit
      T.TErased -> unit
      T.TError T.TUnreachable -> return Undefined
      T.TCoerce t -> go t

    getDef (T.TDef f) = Just (Left f)
    getDef (T.TCon c) = Just (Right c)
    getDef (T.TCoerce x) = getDef x
    getDef _ = Nothing

    unit = return Null

eraseLocalVars :: [Bool] -> T.TTerm -> T.TTerm
eraseLocalVars [] x = x
eraseLocalVars (False: es) x = eraseLocalVars es x
eraseLocalVars (True: es) x = eraseLocalVars es (TC.subst (length es) T.TErased x)

writeModule :: Module -> TCM ()
writeModule m = do
  out <- outFile (modName m)
  reportSDoc "function.go" 4 $ "out: :" <+> (text . show) out
  reportSDoc "compile.go" 10 $ "module: :" <+> (multiLineText (show m))
  liftIO (writeFile out (GoPretty.prettyPrintGo m))

outFile :: GlobalId -> TCM FilePath
outFile m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName (goFileName m)
  let dir = mdir </> fdir
      fp  = dir </> fn
  reportSDoc "function.go" 5 $ " dir o:" <+> (text . show) dir    
  liftIO $ createDirectoryIfMissing True dir
  return fp

goTypeApproximation :: Int -> Type -> TCM TypeId
goTypeApproximation fv t = do
  let go n t = do
        int  <- getBuiltinName builtinInteger
        nat  <- getBuiltinName builtinNat
        let tu = unSpine t
        let is q b = Just q == b
        case tu of
          Pi a b -> do
            reportSDoc "function.go" 10 $ "in pi: :" <+> (text . show) b
            p1 <- goTypeApproximationF n (unDom a)
            p2 <- goTypeApproximationF (n + k) (unAbs b)
            reportSDoc "function.go" 10 $ "in p1: :" <+> (text . show) p1
            reportSDoc "function.go" 10 $ "in p2: :" <+> (text . show) p2
            return $ PiType p1 p2
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` int -> return $ ConstructorType (getVarName n) "*big.Int"
            | q `is` nat -> return $ ConstructorType (getVarName n) "*big.Int"
            | otherwise -> do
              (MemberId name) <- liftTCM $ fullName q
              return $ ConstructorType (getVarName n) name
          Sort{} -> return EmptyType
          _ -> return $ ConstructorType (getVarName n) "interface{}"
  go fv (unEl t)

goTypeApproximationF :: Int -> Type -> TCM TypeId
goTypeApproximationF fv t = do
  let go n t = do
        int  <- getBuiltinName builtinInteger
        nat  <- getBuiltinName builtinNat
        let tu = unSpine t
        let is q b = Just q == b
        case tu of
          Pi a b -> do
            reportSDoc "function.go" 10 $ "in pi: :" <+> (text . show) b
            p1 <- go n (unEl $ unDom a)
            p2 <- go (n + k) (unEl $ unAbs b)
            reportSDoc "function.go" 10 $ "in p1: :" <+> (text . show) p1
            reportSDoc "function.go" 10 $ "in p2: :" <+> (text . show) p2
            return $ PiType p1 p2
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` int -> return $ ConstructorType (getVarName n) "*big.Int"
            | q `is` nat -> return $ ConstructorType (getVarName n) "*big.Int"
            | otherwise -> do
              (MemberId name) <- liftTCM $ fullName q
              return $ ConstructorType (getVarName n) name
          Sort{} -> return EmptyType
          Var varN [] -> return $ GenericFunctionType (getVarName n) ("T" ++ (show varN))
          _ -> return $ ConstructorType (getVarName n) "interface{}"
  go fv (unEl t)

goTypeApproximation' :: Int -> Type -> TCM TypeId
goTypeApproximation' fv t = do
  let go n t = do
        int  <- getBuiltinName builtinInteger
        nat  <- getBuiltinName builtinNat
        let tu = unSpine t
        let is q b = Just q == b
        case tu of
          Pi a b -> do
            reportSDoc "function.go" 10 $ "in pi: :" <+> (text . show) b
            p1 <- goTypeApproximationF n (unDom a)
            p2 <- goTypeApproximationF (n + k) (unAbs b)
            reportSDoc "function.go" 10 $ "in p1: :" <+> (text . show) p1
            reportSDoc "function.go" 10 $ "in p2: :" <+> (text . show) p2
            return $ PiType p1 p2
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` int -> return $ ConstructorType (getVarName n) "interface{}"
            | q `is` nat -> return $ ConstructorType (getVarName n) "interface{}"
            | otherwise -> do
              (MemberId name) <- liftTCM $ fullName q
              return $ ConstructorType (getVarName n) name
          Sort{} -> return EmptyType
          _ -> return $ ConstructorType (getVarName n) "interface{}"
  go fv (unEl t)

goTypeApproximationRet :: Int -> Type -> TCM TypeId
goTypeApproximationRet fv t = do
  let go n t = do
        int  <- getBuiltinName builtinInteger
        nat  <- getBuiltinName builtinNat
        let tu = unSpine t
        let is q b = Just q == b
        case tu of
          Pi a b -> do
            reportSDoc "function.go" 10 $ "in pi: :" <+> (text . show) b
            p1 <- go n (unEl $ unDom a)
            p2 <- go (n + k) (unEl $ unAbs b)
            reportSDoc "function.go" 10 $ "in p1: :" <+> (text . show) p1
            reportSDoc "function.go" 10 $ "in p2: :" <+> (text . show) p2
            return $ PiType p1 p2
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` int -> return $ ConstructorType (getVarName n) "*big.Int"
            | q `is` nat -> return $ ConstructorType (getVarName n) "*big.Int"
            | otherwise -> do
              (MemberId name) <- liftTCM $ fullName q
              return $ ConstructorType (getVarName n) name
          Sort{} -> return EmptyType
          _ -> return $ ConstructorType (getVarName n) "interface{}"
  go fv (unEl t)

goTelApproximation :: Type -> [Bool] -> TCM ([TypeId], TypeId)
goTelApproximation t erased = do
  TelV tel res <- telView t
  let args = map (snd . unDom) (telToList tel)
  reportSDoc "compile.go" 20 $ " args:" <+> (text . show) args
  reportSDoc "compile.go" 20 $ " used:" <+> (text . show) erased
  reportSDoc "compile.go" 20 $ " len:" <+> (text . show) (length args)
  let filteredArgs = map2 erased $ filter isSortType args
  reportSDoc "compile.go" 20 $ " filteredArgs:" <+> (text . show) filteredArgs
  (,) <$> zipWithM (goTypeApproximation) [0..] filteredArgs <*> goTypeApproximationRet (length args) res

goTelApproximationFunction :: Type -> [Bool] -> TCM ([TypeId], TypeId)
goTelApproximationFunction t erased = do
  TelV tel res <- telView t
  let args = map (snd . unDom) (telToList tel)
  reportSDoc "function.go" 20 $ " args:" <+> (text . show) args
  reportSDoc "function.go" 20 $ " res:" <+> (text . show) res
  reportSDoc "function.go" 20 $ " used:" <+> (text . show) erased
  reportSDoc "function.go" 20 $ " len:" <+> (text . show) (length args)
  let filteredArgs = filter isSortType $ map2 erased args 
  reportSDoc "function.go" 20 $ " filteredArgs:" <+> (text . show) filteredArgs
  (,) <$> zipWithM (goTypeApproximation') [0..] filteredArgs <*> goTypeApproximationRet (length args) res  

isSortType :: Type -> Bool
isSortType t = do
  let tu = unSpine (unEl t)
  case tu of
    Sort{} -> False
    _ -> True

applyReturnType :: TypeId -> Exp -> Exp
applyReturnType retT exp = do
  case exp of 
    GoVar x -> ReturnExpression (GoVar x) retT
    GoMethodCall x y -> ReturnExpression (GoMethodCall x y) retT
    GoCreateStruct x y -> ReturnExpression (GoCreateStruct x y) retT
    BinOp x y z -> ReturnExpression (BinOp x y z) retT
    String x -> ReturnExpression (String x) retT
    Integer x -> ReturnExpression (Integer x) retT
    Const x -> ReturnExpression (Const x) retT
    GoInterface x -> GoInterface x
    GoStruct x y -> GoStruct x y
    GoFunction x y -> GoFunction x $ (applyReturnType retT) y
    GoSwitch x y -> GoSwitch x $ map (applyReturnType retT) y
    GoCase memId a b c x -> do
      if (isLastExpression (last x)) == True
        then GoCase memId a b c $ (init x) ++ [(ReturnExpression (last x) retT)]
        else GoCase memId a b c $ (init x) ++ [(applyReturnType retT (last x))]
    GoIf x y z -> GoIf x (applyReturnType retT y) (applyReturnType retT z)
    GoLet x y z -> GoLet x y (applyReturnType retT z)
    n -> n


isLastExpression :: Exp -> Bool
isLastExpression = \case
  GoMethodCall x y -> True
  GoCreateStruct x y -> True
  GoVar x -> True
  BinOp x y z -> True
  String x -> True
  Integer x -> True
  Const x -> True
  _ -> False
outFile_ :: TCM FilePath
outFile_ = do
  m <- curMName
  outFile (goMod m)

literal :: Literal -> Exp
literal = \case
  (LitNat    x) -> Integer x
  (LitWord64 x) -> __IMPOSSIBLE__
  (LitFloat  x) -> __IMPOSSIBLE__
  (LitString x) -> __IMPOSSIBLE__
  (LitChar   x) -> __IMPOSSIBLE__
  (LitQName  x) -> __IMPOSSIBLE__
  LitMeta{}     -> __IMPOSSIBLE__

compilePrim :: T.TPrim -> Exp
compilePrim p =
  case p of
    T.PEqI -> Const "helper.Equals"
    T.PSub -> Const "helper.Minus"
    T.PMul -> Const "helper.Multiply"
    T.PAdd -> Const "helper.Add"
    T.PGeq -> Const "helper.MoreOrEquals"
    T.PLt -> Const "helper.Less"
    T.PEqC -> Const "=="
    T.PEqS -> Const "=="
    T.PEq64 -> Const "helper.Equals"
    T.PLt64 -> Const "helper.Less"
    T.PEqF -> Const "PEqF"
    T.PEqQ -> Const "PEqQ"
    T.PRem -> Const "PRem"
    T.PQuot -> Const "PQuot"
    T.PAdd64 -> Const "helper.Add"
    T.PSub64 -> Const "helper.Minus"
    T.PMul64 -> Const "helper.Multiply"
    T.PRem64 -> Const "PRem64" 
    T.PQuot64 -> Const "PQuot64"
    T.PITo64 -> Const "PITo64"
    T.P64ToI -> Const "P64ToI"
    T.PSeq -> Const "PSeq"
    T.PIf -> __IMPOSSIBLE__


-- | Cubical primitives that are (currently) not compiled.
--
-- TODO: Primitives that are neither part of this set nor of
-- 'primitives', and for which 'defGoDef' does not return anything,
-- are silently compiled to 'Undefined'. Thus, if a cubical primitive
-- is by accident omitted from 'cubicalPrimitives', then programs that
-- should be rejected are compiled to something which might not work
-- as intended. A better approach might be to list exactly those
-- primitives which should be compiled to 'Undefined'.

cubicalPrimitives :: Set String
cubicalPrimitives = Set.fromList
  [ "primIMin"
  , "primIMax"
  , "primINeg"
  , "primPartial"
  , "primPartialP"
  , "primPFrom1"
  , "primPOr"
  , "primComp"
  , "primTransp"
  , "primHComp"
  , "primSubOut"
  ]

-- | Primitives implemented in the Go Agda RTS.
primitives :: Set String
primitives = Set.fromList
  [  "primShowInteger"

  -- Natural number functions
  -- , "primNatPlus"                 -- missing
  , "primNatMinus"
  -- , "primNatTimes"                -- missing
  -- , "primNatDivSucAux"            -- missing
  -- , "primNatModSucAux"            -- missing
  -- , "primNatEquality"             -- missing
  -- , "primNatLess"                 -- missing
  -- , "primShowNat"                 -- missing

  -- Machine words
  , "primWord64ToNat"
  , "primWord64FromNat"
  -- , "primWord64ToNatInjective"    -- missing

  -- Level functions
  -- , "primLevelZero"               -- missing
  -- , "primLevelSuc"                -- missing
  -- , "primLevelMax"                -- missing

  -- Sorts
  -- , "primSetOmega"                -- missing
  -- , "primStrictSetOmega"          -- missing

  -- Floating point functions
  , "primFloatEquality"
  , "primFloatInequality"
  , "primFloatLess"
  , "primFloatIsInfinite"
  , "primFloatIsNaN"
  , "primFloatIsNegativeZero"
  , "primFloatIsSafeInteger"
  , "primFloatToWord64"
  -- , "primFloatToWord64Injective"  -- missing
  , "primNatToFloat"
  , "primIntToFloat"
  -- , "primFloatRound"              -- in Agda.Builtin.Float
  -- , "primFloatFloor"              -- in Agda.Builtin.Float
  -- , "primFloatCeiling"            -- in Agda.Builtin.Float
  -- , "primFloatToRatio"            -- in Agda.Builtin.Float
  , "primRatioToFloat"
  -- , "primFloatDecode"             -- in Agda.Builtin.Float
  -- , "primFloatEncode"             -- in Agda.Builtin.Float
  , "primShowFloat"
  , "primFloatPlus"
  , "primFloatMinus"
  , "primFloatTimes"
  , "primFloatNegate"
  , "primFloatDiv"
  , "primFloatSqrt"
  , "primFloatExp"
  , "primFloatLog"
  , "primFloatSin"
  , "primFloatCos"
  , "primFloatTan"
  , "primFloatASin"
  , "primFloatACos"
  , "primFloatATan"
  , "primFloatATan2"
  , "primFloatSinh"
  , "primFloatCosh"
  , "primFloatTanh"
  , "primFloatASinh"
  , "primFloatACosh"
  , "primFloatATanh"
  , "primFloatPow"

  -- Character functions
  -- , "primCharEquality"            -- missing
  -- , "primIsLower"                 -- missing
  -- , "primIsDigit"                 -- missing
  -- , "primIsAlpha"                 -- missing
  -- , "primIsSpace"                 -- missing
  -- , "primIsAscii"                 -- missing
  -- , "primIsLatin1"                -- missing
  -- , "primIsPrint"                 -- missing
  -- , "primIsHexDigit"              -- missing
  -- , "primToUpper"                 -- missing
  -- , "primToLower"                 -- missing
  -- , "primCharToNat"               -- missing
  -- , "primCharToNatInjective"      -- missing
  -- , "primNatToChar"               -- missing
  -- , "primShowChar"                -- in Agda.Builtin.String

  -- String functions
  -- , "primStringToList"            -- in Agda.Builtin.String
  -- , "primStringToListInjective"   -- missing
  -- , "primStringFromList"          -- in Agda.Builtin.String
  -- , "primStringFromListInjective" -- missing
  -- , "primStringAppend"            -- in Agda.Builtin.String
  -- , "primStringEquality"          -- in Agda.Builtin.String
  -- , "primShowString"              -- in Agda.Builtin.String
  -- , "primStringUncons"            -- in Agda.Builtin.String

  -- Other stuff
  -- , "primEraseEquality"           -- missing
  -- , "primForce"                   -- missing
  -- , "primForceLemma"              -- missing
  , "primQNameEquality"
  , "primQNameLess"
  , "primShowQName"
  , "primQNameFixity"
  -- , "primQNameToWord64s"          -- missing
  -- , "primQNameToWord64sInjective" -- missing
  -- , "primMetaEquality"            -- missing
  -- , "primMetaLess"                -- missing
  -- , "primShowMeta"                -- missing
  -- , "primMetaToNat"               -- missing
  -- , "primMetaToNatInjective"      -- missing
  -- , "primIMin"                    -- missing
  -- , "primIMax"                    -- missing
  -- , "primINeg"                    -- missing
  -- , "primPOr"                     -- missing
  -- , "primComp"                    -- missing
  -- , builtinTrans                  -- missing
  -- , builtinHComp                  -- missing
  -- , "primIdJ"                     -- missing
  -- , "primPartial"                 -- missing
  -- , "primPartialP"                -- missing
  -- , builtinGlue                   -- missing
  -- , builtin_glue                  -- missing
  -- , builtin_unglue                -- missing
  -- , builtinFaceForall             -- missing
  -- , "primDepIMin"                 -- missing
  -- , "primIdFace"                  -- missing
  -- , "primIdPath"                  -- missing
  -- , builtinIdElim                 -- missing
  -- , builtinSubOut                 -- missing
  -- , builtin_glueU                 -- missing
  -- , builtin_unglueU               -- missing
  ]
