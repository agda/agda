{-# LANGUAGE CPP             #-}
{-# LANGUAGE DoAndIfThenElse #-}

-- | Convert the AuxAST code to UHC Core code.
module Agda.Compiler.UHC.Core
  ( toCore
  , mkHsName
  , createMainModule
  ) where

import Data.List
import qualified Data.Map as M
import Data.Maybe (fromMaybe, catMaybes)
import qualified Data.Set as Set
#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
#endif
import Control.Monad.State
import Control.Monad.Reader

import Agda.Interaction.Options
import Agda.TypeChecking.Monad
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Utils.Pretty

import Agda.Compiler.UHC.AuxAST
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Primitives

import Agda.Compiler.UHC.Bridge


#include "undefined.h"
import Agda.Utils.Impossible

opts :: EHCOpts
opts = defaultEHCOpts

-- stores tracing level
type ToCoreT m = FreshNameT (ReaderT Int m)

createMainModule :: AModuleInfo -> HsName -> CModule
createMainModule mainMod main = mkModule (mkHsName [] "Main") [] [mkImport $ mkHsName1 "UHC.Run", mkImport mainModAux] [] (mkMain main)
  where mainModAux = snd $ fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amifNameMp $ amiInterface mainMod) (amiModule mainMod)

getExports :: AModuleInfo -> [CExport]
getExports modInfo = map (mkExport . cnName) (expFuns ++ expDtFuns ++ expConFuns)
  where expFuns = getExportsFor EtFunction
        -- there is a function for each datatype, named as the datatype itself.
        -- This is used as type-dummy, returning always unit.
        -- We need to export those too.
        expDtFuns = getExportsFor EtDatatype
        -- and the constructor wrapper functions
        expConFuns = getExportsFor EtConstructor

        getExportsFor ty = let items = M.elems $ getNameMappingFor (amifNameMp $ amiInterface modInfo) ty
                            in filter needsExport items
        needsExport x = cnAgdaExported x


toCore :: AMod      -- ^ The current module to compile.
    -> AModuleInfo  -- ^ Info about current module.
    -> AModuleInterface -- ^ Transitive interface.
    -> [AModuleInfo] -- ^ Top level imports
    -> TCM CModule
toCore amod modInfo transModIface modImps = do

  traceLvl <- optUHCTraceLevel <$> commandLineOptions
  funs <- flip runReaderT traceLvl $ evalFreshNameT "nl.uu.agda.to_core" $ funsToCore (xmodFunDefs amod)

  let cMetaDeclL = buildCMetaDeclL (xmodDataTys amod)

  let imps = map mkHsName1
        ( Set.toList
        $ Set.insert "UHC.Base"
        $ Set.insert "UHC.Agda.Builtins"
        $ xmodCrImports amod
        ) ++ map (mnmToCrNm . amiModule) modImps
  let impsCr = map mkImport imps
      exps = getExports modInfo
      crModNm = mnmToCrNm $ xmodName amod
      cmod = mkModule crModNm exps impsCr cMetaDeclL funs
  return cmod
  where mnmToCrNm :: ModuleName -> HsName
        mnmToCrNm mnm = snd (fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amifNameMp transModIface) mnm)

funsToCore :: Monad m => [Fun] -> ToCoreT m CExpr
funsToCore funs = do
  binds <- mapM funToBind funs
  let body = mkLetRec binds (mkInt opts 0)
  return body

buildCMetaDeclL :: [ADataTy] -> [CDeclMeta]
buildCMetaDeclL dts = catMaybes $ map f dts
    where f :: ADataTy -> Maybe CDeclMeta
          -- foreign/builtin datatypes are defined somewhere else. For normal datatypes, core name is always defined.
          f d@(ADataTy{xdatImplType = ADataImplNormal}) = Just $ mkMetaData (fromMaybe __IMPOSSIBLE__ $ xdatName d) (map g (xdatCons d))
          f _ = Nothing
          g :: ADataCon -> CDataCon
          -- mkMetaDataConFromCTag can return Nothing for the tuple/record/() ctag, but should never happen
          g c@(ADataCon{}) = fromMaybe __IMPOSSIBLE__ $ mkMetaDataConFromCTag (xconCTag c)


funToBind :: Monad m => Fun -> ToCoreT m CBind
funToBind (CoreFun name _ _ crExpr) = return $ mkBind1 name crExpr

