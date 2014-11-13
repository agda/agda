{-# LANGUAGE CPP #-}

-- | Convert the AuxAST code to UHC Core code.
module Agda.Compiler.UHC.Core
  ( toCore
  , coreImpossible
  , mkHsName
  , createMainModule
  ) where

import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Maybe (fromJust, catMaybes)
import Control.Applicative
import qualified Data.Set as S

import Agda.TypeChecking.Monad
import Agda.Syntax.Abstract.Name
import Control.Monad.IO.Class
import Control.Monad.Trans.Class (lift)
import Control.Monad.State.Class
import Control.Monad.State

import Agda.Compiler.UHC.AuxAST hiding (apps)
import Agda.Compiler.UHC.CompileState hiding (newName)
import Agda.Compiler.UHC.Interface

--import EH99.Core hiding (acoreCaseDflt)
import EH99.Core.API
import EH99.Base.HsName
import EH99.Base.Common
import EH99.Module.ImportExport

import Agda.Compiler.UHC.CoreSyntax

import Agda.Utils.Impossible

opts :: EHCOpts
opts = defaultEHCOpts

data ToCoreState = ToCoreState
  { tcsNameSupply :: [AName] }
type ToCore = State ToCoreState

newName :: ToCore AName
newName = do
  (n:ns) <- gets tcsNameSupply
  modify (\x -> x { tcsNameSupply = ns })
  return n

createMainModule :: String -> AName -> CModule
createMainModule mainMod main = makeModule (hsnFromString "Main") [makeImport $ mkHsName x | x <-
        [ "UHC.Run"
        , mainMod ]] [] (makeMain (toCoreName main))

toCore :: AMod
    -> [Interface] -- ^ Top level imports
    -> Compile TCM (CModule, ModEntRel, S.Set HsName)
toCore mod modImps = do
  ns <- gets nameSupply
  let ((funs, expExprs), ns') = runState (funsToCore (xmodName mod) (xmodFunDefs mod)) (ToCoreState ns)
  modify (\x -> x { nameSupply = tcsNameSupply ns' })

  let cMetaDeclL = buildCMetaDeclL (xmodDataTys mod)
  -- import resolution fails if we just use hsnFromString, as it produces a _Base hsname, but the Map used for the lookups stores _Modf names. Is this a bug?
  let imps = [ mkHsName x | x <-
        [ "UHC.Base"
        , "UHC.Agda.Builtins"
        ] ++ map (show . iModuleName ) modImps]
  let impsCr = map makeImport imps
  let cmod = makeModule (hsnFromString $ xmodName mod) impsCr cMetaDeclL funs
  let hiImps = S.fromList imps
  return (cmod, expExprs, hiImps)

funsToCore :: String -> [Fun] -> ToCore (CExpr, ModEntRel)
funsToCore mod funs = do
  binds <- mapM funToBind funs
  let body = acoreLetRec binds (acoreInt opts 0)

  let expExprs = map (mkEntRel . xfunName) funs

  return (body, S.unions expExprs)
  where mkEntRel :: AName -> ModEntRel
        mkEntRel nm = S.singleton (snd $ hsnInitLast $ toCoreName nm, ModEnt IdOcc_Val (IdOcc (toCoreName nm) IdOcc_Val) S.empty Range_Unknown)

buildCMetaDeclL :: [ADataTy] -> [CDeclMeta]
buildCMetaDeclL dts = map f dts
    where f :: ADataTy -> CDeclMeta
          f d@(ADataTy{}) = makeMetaData (toCoreName $ xdatName d) (map g (xdatCons d))
          g :: ADataCon -> CDataCon
          g c@(ADataCon{}) = makeMetaDataCon (toCoreName $ unqname $ xconQName c) (xconTag c) (xconArity c)


funToBind :: Fun -> ToCore CBind
funToBind (Fun _ name mqname comment vars e) = do -- TODO what is mqname?
  e' <- exprToCore e
  let body = acoreLam (map toCoreName vars) e'
  return $ acoreBind1 (toCoreName name) body
funToBind (CoreFun name _ _ crExpr) = return $ acoreBind1 (toCoreName name) crExpr

exprToCore :: Expr -> ToCore CExpr
exprToCore (Var v)      = return $ acoreVar $ toCoreName v
exprToCore (Lit l)      = return $ litToCore l
exprToCore (Lam v body) = exprToCore body >>= return . acoreLam [toCoreName v]
exprToCore (Con t qn es) = do
    es' <- mapM exprToCore es
    let ctag = mkCTag t qn
    return $ acoreTagTup ctag es'
exprToCore (App fv es)   = do
    es' <- mapM exprToCore es
    let fv' = acoreVar $ toCoreName fv
    return $ acoreApp fv' es'
exprToCore (Case e brs) = do
    var <- newName
    (def, branches) <- branchesToCore brs
    let cas = acoreCaseDflt (acoreVar $ toCoreName var) branches (Just def)
    e' <- exprToCore e
    return $ acoreLet1Strict (toCoreName var) e' cas
exprToCore (Let v e1 e2) = do
    e1' <- exprToCore e1
    e2' <- exprToCore e2
    return $ acoreLet1Plain (toCoreName v) e1' e2'
exprToCore UNIT         = return $ acoreUnit opts
exprToCore IMPOSSIBLE   = return $ coreImpossible ""

branchesToCore :: [Branch] -> ToCore (CExpr, [CAlt])
branchesToCore brs = do
    let defs = filter isDefault brs
    def <- if null defs then return (coreImpossible "Default branch reached, but doesn't exit.") else let (Default x) = head defs in exprToCore x
    brs' <- mapM f brs

    return (def, concat brs')
    where
          f (Branch tag qn vars e)  = do
            let ctag = mkCTag tag qn
            let patFlds = [acorePatFldBind (hsnFromString "", acoreInt opts i) (acoreBind1Nm1 (toCoreName v)) | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [acoreAlt (acorePatCon ctag acorePatRestEmpty patFlds) e']
          f (CoreBranch con vars e) = do
            let ctag = conSpecToTag con
            let patFlds = [acorePatFldBind (hsnFromString "", acoreInt opts i) (acoreBind1Nm1 (toCoreName v)) | (i, v) <- zip [0..] vars]
            e' <- exprToCore e
            return [acoreAlt (acorePatCon ctag acorePatRestEmpty patFlds) e']
          f (Default e) = return []
          -- UHC resets the tags for some constructors, but only those wo are defined in the same module. So just set it anyway, to be safe.
          conSpecToTag (dt, ctor, tag) = CTag (mkHsName dt) (mkHsName $ (modNm dt) ++ "." ++ ctor) tag (-1) (-1)
          modNm s = reverse $ tail $ dropWhile (/= '.') $ reverse s
          isDefault (Default _) = True
          isDefault _ = False

qnameTypeName :: QName -> HsName
qnameTypeName = toCoreName . unqname . qnameFromList . init . qnameToList

qnameCtorName :: QName -> HsName
qnameCtorName = mkHsName . show . last . qnameToList

mkCTag :: Tag -> QName -> CTag
mkCTag t qn = CTag (qnameTypeName qn) (qnameCtorName qn) t (-1) (-1)

litToCore :: Lit -> CExpr
-- should we put this into a let?
litToCore (LInt i) = appS "UHC.Agda.Builtins.primIntegerToNat" (acoreBuiltinInteger opts i)
litToCore (LString s) = acoreBuiltinString opts s
litToCore l = error $ "Not implemented literal: " ++ show l

coreImpossible :: String -> CExpr
coreImpossible msg = acoreBuiltinError opts $ "BUG! Impossible code reached. " ++ msg


toCoreName :: AName -> HsName
toCoreName (ANmCore n) = mkHsName n
toCoreName (ANmAgda n) = mkHsName $
    case elemIndex '.' nr of
        Just i -> let (n', ns') = splitAt i nr
                   in (reverse ns') ++ "agda_c1_" ++ (reverse n')
        Nothing -> n -- local (generated) name
    where nr = reverse n

-- | Creates a Haskell Name from a String.
mkHsName :: String -> HsName
mkHsName x = -- UHC expects names to be of the _Modf variety. If _Base/hsnFromString is used
  -- instead things start to break, e.g. calling functions defined in other packages.
  hsnMkModf (init xs) (hsnFromString $ last xs) M.empty
  where xs = splitBy '.' x
        splitBy :: Eq a => a -> [a] -> [[a]]
        splitBy sep = (foldr (\x (a1:as) -> if x == sep then ([]:a1:as) else ((x:a1):as)) [[]])

-- | Apply the named function to one argument.
appS :: String -> CExpr -> CExpr
appS f x = acoreApp (acoreVar $ mkHsName f) [x]
