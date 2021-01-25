{-# LANGUAGE CPP             #-}

-- | Convert from Agda's internal representation to UHC Core via Treeless.
--
--
-- The coinduction kit is translated the same way as in MAlonzo:
-- flat = id
-- sharp = id
-- -> There is no runtime representation of Coinductive values.
module Agda.Compiler.UHC.FromAgda where

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
import Data.Traversable (traverse)
#endif

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Set as Set

import Agda.Syntax.Internal hiding (Term(..))
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal  as TL
import Agda.Syntax.Treeless (TTerm (..), TAlt (..))
import qualified Agda.Syntax.Treeless as C
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.Utils.List
import qualified Agda.Utils.Pretty as P
import qualified Agda.Utils.HashMap as HMap
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Compiler.Treeless.NormalizeNames
import Agda.Compiler.Treeless.Pretty
import Agda.Compiler.UHC.Pragmas.Base
import Agda.Compiler.UHC.Pragmas.Parse (coreExprToCExpr)
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Primitives
import Agda.Compiler.UHC.MagicTypes

import Agda.Compiler.UHC.Bridge as CA

import Agda.Utils.Maybe
import Agda.Utils.Except ( MonadError (catchError) )
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

opts :: EHCOpts
opts = defaultEHCOpts

-- | Convert from Agda's internal representation to our auxiliary AST.
fromAgdaModule :: ModuleName
    -> [ModuleName]      -- imported modules.
    -> Interface         -- interface to compile
    -> TCM CModule
fromAgdaModule modNm curModImps iface = do

  -- Set correct pragma options
  setCommandLineOptions =<< gets (stPersistentOptions . stPersistentState)
  mapM_ setOptionsFromPragma (iPragmaOptions iface)

  -- sort defs to ensure consistent order (see Issue 1900)
  let defs = sortDefs $ iSignature iface ^. sigDefinitions

  runCompileT modNm (do
    lift $ reportSLn "compile.uhc" 10 "Translate datatypes..."

    funs' <- concat <$> mapM translateDefn defs
    let funs = mkLetRec funs' (mkInt opts 0)



    additionalImports <- lift getHaskellImportsUHC
    let imps = map mkImport $ nub $
          [ mkHsName1 "UHC.Base"
          , mkHsName1 "UHC.Agda.Builtins" ]
          ++ map moduleNameToCoreName curModImps
          ++ map mkHsName1 (Set.toList additionalImports)

        crModNm = moduleNameToCoreName modNm

    mkModule crModNm
      <$> getExports <*> pure imps <*> getDeclMetas <*> pure funs
    )


-- | Translate an Agda definition to an UHC Core function where applicable
translateDefn :: (QName, Definition) -> Compile [CBind]
translateDefn (n, defini) = do

  crName <- getCoreName n
  let crRep = compiledCore $ defCompiledRep defini
  kit <- lift coinductionKit
  case theDef defini of
    d@(Datatype {}) -> do

        unless (isJust crRep || Just n == (nameOfInf <$> kit)) $ do
          addMetaData n (mkMetaData crName)

        vars <- replicateM (dataPars d + dataIxs d) freshLocalName
        addExports [crName]
        return [mkBind1 crName (mkLam vars $ mkUnit opts)]
    (Function{}) | Just n == (nameOfFlat <$> kit) -> do
        addExports [crName]
        (\x -> [x]) <$> mkIdentityFun n "coind-flat" 0
    f@(Function{}) | otherwise -> do
        let ty    = (defType defini)
        lift $ reportSDoc "compile.uhc.fromagda" 5 $ text "compiling fun:" <+> prettyTCM n
        lift $ reportSDoc "compile.uhc.fromagda" 15 $ text "type:" <+> (text . show) ty

        caseMaybeM (lift $ toTreeless n) (pure []) $ \ treeless -> do
          funBody <- convertGuards <$> lift (normalizeNames treeless)
          lift $ reportSDoc "compile.uhc.fromagda" 30 $ text " compiled treeless fun:" <+> (text . show) funBody
          funBody' <- runTT $ compileTerm funBody
          lift $ reportSDoc "compile.uhc.fromagda" 30 $ text " compiled UHC Core fun:" <+> (text . show) funBody'

          addExports [crName]
          return [mkBind1 crName funBody']

    Constructor{} | Just n == (nameOfSharp <$> kit) -> do
        addExports [crName]
        (\x -> [x]) <$> mkIdentityFun n "coind-sharp" 0

    (Constructor{}) | Nothing <- crRep -> do -- become functions returning a constructor with their tag
      -- we have to ignore instantiated constructors here!
      n' <- lift $ canonicalName n
      if (n /= n')
        then return []
        else do
          addExports [crName]
          ctag <- getConstrCTag n

          addMetaCon n (fromJust $ mkMetaDataConFromCTag ctag)

          vars <- replicateM (getCTagArity ctag) freshLocalName
          let conWrapper = mkLam vars (mkTagTup ctag $ map mkVar vars)
          return [mkBind1 crName conWrapper]
    Constructor{} -> return []
    -- either foreign or builtin type. We can just assume existence of the wrapper functions then.

    r@(Record{}) -> do
        unless (isJust crRep) $ do
          addMetaData n (mkMetaData crName)

        vars <- replicateM (recPars r) freshLocalName
        addExports [crName]
        return [mkBind1 crName (mkLam vars $ mkUnit opts)]
    (Axiom{}) -> do -- Axioms get their code from COMPILED_UHC pragmas
        addExports [crName]
        case crRep of
            Nothing -> return [mkBind1 crName
                (coreError $ "Axiom " ++ show n ++ " used but has no computation.")]
            Just (CrDefn x) -> do
                        x' <- case coreExprToCExpr x of
                                -- This can only happen if an *.agdai file was generated by an Agda version
                                -- without UHC support enabled.
                                Left err -> internalError $ "Invalid COMPILED_UHC pragma value: " ++ err
                                Right y -> return y
                        return [mkBind1 crName x']
            _ -> __IMPOSSIBLE__

    p@(Primitive{}) -> do -- Primitives use primitive functions from UHC.Agda.Builtins of the same name.
      addExports [crName]

      case primName p `M.lookup` primFunctions of
        Nothing     -> internalError $ "Primitive " ++ show (primName p) ++ " declared, but no such primitive exists."
        (Just expr) -> do
                expr' <- expr
                return [mkBind1 crName expr']
    AbstractDefn -> __IMPOSSIBLE__
  where
    -- | Produces an identity function, optionally ignoring the first n arguments.
    mkIdentityFun :: QName
        -> String -- ^ comment
        -> Int      -- ^ How many arguments to ignore.
        -> Compile CBind
    mkIdentityFun nm comment ignArgs = do
        crName <- getCoreName nm
        xs <- replicateM (ignArgs + 1) freshLocalName
        return $ mkBind1 crName (mkLam xs (mkVar $ last xs))


runTT :: TT a -> Compile a
runTT r = do
  r `runReaderT` (TTEnv [])

data TTEnv = TTEnv
  { nmEnv :: [HsName] -- maps de-bruijn indices to names
  }

type TT = ReaderT TTEnv Compile


addToEnv :: [HsName] -> TT a -> TT a
addToEnv nms cont =
  local (\e -> e { nmEnv = nms ++ (nmEnv e) }) cont

data BuiltinKit = BuiltinKit
  { isNat :: QName -> Bool
  , isInt :: QName -> Bool
  }

builtinKit :: TCM BuiltinKit
builtinKit =
  BuiltinKit <$> is dat builtinNat
             <*> is dat builtinInteger
  where
    dat (I.Def d _) = pure d
    dat _           = Nothing

    is a b = maybe (const False) (==) . (a =<<) <$> getBuiltin' b

-- | Translate the actual Agda terms, with an environment of all the bound variables
--   from patternmatching. Agda terms are in de Bruijn so we just check the new
--   names in the position.
compileTerm :: C.TTerm -> TT CExpr
compileTerm term = do
  builtinKit' <- lift $ lift builtinKit
  case term of
    C.TPrim t -> return $ compilePrim t
    C.TVar x -> do
      nm <- fromMaybe __IMPOSSIBLE__ . (!!! x) <$> asks nmEnv
      return $ mkVar nm
    C.TDef nm -> do
      nm' <- lift $ getCoreName nm
      return $ mkVar nm'
    C.TApp t xs -> do
      mkApp <$> compileTerm t <*> mapM compileTerm xs
    C.TLam t -> do
       name <- lift freshLocalName
       addToEnv [name] $ do
         mkLam [name] <$> compileTerm t
    C.TLit l -> return $ litToCore l
    C.TCon c -> do
        con <- lift $ getConstrFun c
        return $ mkVar con
    C.TLet x body -> do
        nm <- lift freshLocalName
        mkLet1Plain nm
          <$> compileTerm x
          <*> addToEnv [nm] (compileTerm body)
    C.TCase sc (C.CTData dt) def alts | not (isNat builtinKit' dt || isInt builtinKit' dt) -> do
      -- normal constructor case
      caseScr <- lift freshLocalName
      defVar <- lift freshLocalName
      def' <- compileTerm def

      branches <- traverse compileConAlt alts
      defBranches <- defaultBranches dt alts (mkVar defVar)
      let cas = mkCase (mkVar caseScr) (branches ++ defBranches)
      caseScr' <- compileTerm (C.TVar sc)

      return $ mkLet1Plain defVar def' (mkLet1Strict caseScr caseScr' cas)

    C.TCase sc ct def alts | otherwise -> do
      -- cases on literals
      sc <- compileTerm (C.TVar sc)
      var <- lift freshLocalName
      def <- compileTerm def

      css <- buildPrimCases eq (mkVar var) alts def
      return $ mkLet1Strict var sc css
      where
        eq :: CExpr
        eq = case ct of
          C.CTChar -> mkVar $ primFunNm "primCharEquality"
          C.CTString -> mkVar $ primFunNm "primStringEquality"
          C.CTQName -> mkVar $ primFunNm "primQNameEquality"
          C.CTFloat -> mkVar $ primFunNm "primFloatEquality"
          C.CTNat -> mkVar $ primFunNm "primIntegerEquality"
          C.CTInt -> mkVar $ primFunNm "primIntegerEquality"
          _ -> __IMPOSSIBLE__

    C.TUnit -> unit
    C.TSort -> unit
    C.TErased -> unit
    C.TError e -> return $ case e of
      C.TUnreachable -> coreError $ "Unreachable code reached. This should never happen! Crashing..."
  where unit = return $ mkUnit opts


buildPrimCases :: CExpr -- ^ equality function
    -> CExpr    -- ^ case scrutinee (in WHNF)
    -> [C.TAlt]
    -> CExpr    -- ^ default value
    -> TT CExpr
buildPrimCases _ _ [] def = return def
buildPrimCases eq scr (b:brs) def = do
    var <- lift     freshLocalName
    e' <- compileTerm (C.aBody b)
    rec' <- buildPrimCases eq scr brs def

    let lit = litToCore $ C.aLit b
        eqTest = mkApp eq [scr, lit]

    return $ mkLet1Strict var eqTest (mkIfThenElse (mkVar var) e' rec')

-- move to UHC Core API
mkIfThenElse :: CExpr -> CExpr -> CExpr -> CExpr
mkIfThenElse c t e = mkCase c [b1, b2]
  where b1 = mkAlt (mkPatCon (ctagTrue opts) mkPatRestEmpty []) t
        b2 = mkAlt (mkPatCon (ctagFalse opts) mkPatRestEmpty []) e

compileConAlt :: C.TAlt -> TT CAlt
compileConAlt a =
  makeConAlt (C.aCon a)
    (\vars -> addToEnv (reverse vars) $ compileTerm (C.aBody a))

makeConAlt :: QName -> ([HsName] -> TT CExpr) -> TT CAlt
makeConAlt con mkBody = do
  ctag <- lift $ getConstrCTag con
  vars <- lift $ replicateM (getCTagArity ctag) freshLocalName
  body <- mkBody vars

  let patFlds = [mkPatFldBind (mkHsName [] "", mkInt opts i) (mkBind1Nm1 v) | (i, v) <- zip [0..] vars]
  return $ mkAlt (mkPatCon ctag mkPatRestEmpty patFlds) body

-- | Constructs an alternative for all constructors not explicitly matched by a branch.
defaultBranches :: QName -> [C.TAlt] -> CExpr -> TT [CAlt]
defaultBranches dt alts def = do
  dtCons <- dataRecCons . theDef <$> (lift . lift) (getConstInfo dt)
  let altCons = map C.aCon alts
      missingCons = dtCons \\ altCons

  mapM (\a -> makeConAlt a (\_ -> return def)) missingCons

litToCore :: Literal -> CExpr
litToCore (LitNat _ i)   = mkApp (mkVar $ primFunNm "primIntegerToNat") [mkInteger opts i]
litToCore (LitString _ s) = mkString opts s
litToCore (LitChar _ c)  = mkChar c
-- UHC and GHC handle trailing zeros slightly different. Work around to make sure
-- we have the same semantics as MAlonzo.
litToCore (LitFloat _ f) = mkApp (mkVar $ primFunNm "primMkFloat") [mkString opts (show f)]
litToCore (LitQName _ q) = mkApp (mkVar $ primFunNm "primMkQName")
                             [mkInteger opts $ fromIntegral n, mkInteger opts $ fromIntegral m,
                              mkString opts $ P.prettyShow q]
  where NameId n m = nameId $ qnameName q
litToCore LitMeta{} = __IMPOSSIBLE__

getCTagArity :: CTag -> Int
-- for records/datatypes, we can always extract the arity. If there is no arity,
-- it is the unit constructor, so just return zero.
getCTagArity = destructCTag 0 (\_ _ _ ar -> ar)

coreError :: String -> CExpr
coreError msg = mkError opts $ "Fatal error: " ++ msg

compilePrim :: C.TPrim -> CExpr
compilePrim C.PQuot = mkVar $ primFunNm "primIntegerQuot"
compilePrim C.PRem = mkVar $ primFunNm "primIntegerRem"
compilePrim C.PSub = mkVar $ primFunNm "primIntegerMinus"
compilePrim C.PAdd = mkVar $ primFunNm "primIntegerPlus"
compilePrim C.PMul = mkVar $ primFunNm "primIntegerTimes"
compilePrim C.PIf  = mkVar $ primFunNm "primIfThenElse"
compilePrim C.PGeq = mkVar $ primFunNm "primIntegerGreaterOrEqual"
compilePrim C.PLt  = mkVar $ primFunNm "primIntegerLess"
compilePrim p | C.isPrimEq p = mkVar $ primFunNm "primIntegerEquality"
compilePrim C.PSeq = mkVar $ primFunNm "primSeq"
compilePrim _ = __IMPOSSIBLE__


createMainModule :: ModuleName -> HsName -> CModule
createMainModule mainMod main = mkModule (mkHsName [] "Main") [] [mkImport $ mkHsName1 "UHC.Run", mkImport mainModAux] [] (mkMain main)
  where mainModAux = moduleNameToCoreName mainMod
