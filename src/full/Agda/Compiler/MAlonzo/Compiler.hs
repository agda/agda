{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Agda.Compiler.MAlonzo.Compiler where

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (foldl, mapM_, mapM, sequence, concat)
#endif

import Control.Applicative
import Control.Monad.Reader hiding (mapM_, forM_, mapM, forM, sequence)
import Control.Monad.State  hiding (mapM_, forM_, mapM, forM, sequence)

import Data.Generics.Geniplate
import Data.Foldable hiding (any, foldr)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable hiding (for)

import qualified Language.Haskell.Exts.Extension as HS
import qualified Language.Haskell.Exts.Parser as HS
import qualified Language.Haskell.Exts.Pretty as HS
import qualified Language.Haskell.Exts.Syntax as HS

import System.Directory (createDirectoryIfMissing)
import System.FilePath hiding (normalise)

import Agda.Compiler.CallCompiler
import Agda.Compiler.Common
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty
import Agda.Compiler.MAlonzo.Primitives
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.Unused

import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options

import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Treeless as T
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Level (reallyUnLevelView)

import Agda.TypeChecking.CompiledClause

import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.IO.Directory
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.IO.UTF8 as UTF8
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Singleton
import Agda.Utils.Tuple

import Paths_Agda

#include "undefined.h"
import Agda.Utils.Impossible

compilerMain :: IsMain -> Interface -> TCM ()
compilerMain isMain i =
  inCompilerEnv i $ do
    doCompile isMain i $
      \_ -> compile
    copyRTEModules
    callGHC isMain i

compile :: Interface -> TCM ()
compile i = do
  ifM uptodate noComp $ {- else -} do
    yesComp
    writeModule =<< decl <$> curHsMod <*> (definitions =<< curDefs) <*> imports
  where
  decl mn ds imp = HS.Module dummy mn [] Nothing Nothing imp ds
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.") . show . A.mnameToConcrete =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show . A.mnameToConcrete <$> curMName, ifile, outFile_] :: TCM ()

--------------------------------------------------
-- imported modules
--   I use stImportedModules in a non-standard way,
--   accumulating in it what are acutally used in Misc.xqual
--------------------------------------------------

imports :: TCM [HS.ImportDecl]
imports = (++) <$> hsImps <*> imps where
  hsImps :: TCM [HS.ImportDecl]
  hsImps = ((unqualRTE :) . List.map decl . Set.toList .
            Set.insert mazRTE . Set.map HS.ModuleName) <$>
             getHaskellImports

  unqualRTE :: HS.ImportDecl
  unqualRTE = HS.ImportDecl dummy mazRTE False False False Nothing Nothing $ Just $
#if MIN_VERSION_haskell_src_exts(1,17,0)
              (False, [HS.IVar $ HS.Ident x | x <- [mazCoerceName, mazErasedName]])
#else
              (False, [HS.IVar HS.NoNamespace $ HS.Ident x | x <- [mazCoerceName, mazErasedName]])
#endif

  imps :: TCM [HS.ImportDecl]
  imps = List.map decl . uniq <$>
           ((++) <$> importsForPrim <*> (List.map mazMod <$> mnames))

  decl :: HS.ModuleName -> HS.ImportDecl
  decl m = HS.ImportDecl dummy m True False False Nothing Nothing Nothing

  mnames :: TCM [ModuleName]
  mnames = (++) <$> (Set.elems <$> use stImportedModules)
                <*> (List.map fst . iImportedModules <$> curIF)

  uniq :: [HS.ModuleName] -> [HS.ModuleName]
  uniq = List.map head . List.group . List.sort

--------------------------------------------------
-- Main compiling clauses
--------------------------------------------------

definitions :: Definitions -> TCM [HS.Decl]
definitions defs = do
  kit <- coinductionKit
  HMap.foldr (liftM2 (++) . (definition kit <=< instantiateFull))
             (return []) defs

-- | Note that the INFINITY, SHARP and FLAT builtins are translated as
-- follows (if a 'CoinductionKit' is given):
--
-- @
--   type Infinity a b = b
--
--   sharp :: a -> a
--   sharp x = x
--
--   flat :: a -> a
--   flat x = x
-- @

definition :: Maybe CoinductionKit -> Definition -> TCM [HS.Decl]
-- ignore irrelevant definitions
{- Andreas, 2012-10-02: Invariant no longer holds
definition kit (Defn Forced{}  _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition kit (Defn UnusedArg _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
definition kit (Defn NonStrict _ _  _ _ _ _ _ _) = __IMPOSSIBLE__
-}
definition kit Defn{defArgInfo = info, defName = q} | isIrrelevant info = do
  reportSDoc "malonzo.definition" 10 $
    text "Not compiling" <+> prettyTCM q <> text "."
  return []
definition kit Defn{defName = q, defType = ty, defCompiledRep = compiled, theDef = d} = do
  reportSDoc "malonzo.definition" 10 $ vcat
    [ text "Compiling" <+> prettyTCM q <> text ":"
    , nest 2 $ text (show d)
    ]
  checkTypeOfMain q ty $ do
    infodecl q <$> case d of

      _ | Just (HsDefn ty hs) <- compiledHaskell compiled ->
        return $ fbWithType ty (fakeExp hs)

      -- Special treatment of coinductive builtins.
      Datatype{} | Just q == (nameOfInf <$> kit) -> do
        let infT = unqhname "T" q
            infV = unqhname "d" q
            a    = ihname "a" 0
            b    = ihname "a" 1
            vars = [a, b]
        return [ HS.TypeDecl dummy infT
                             (List.map HS.UnkindedVar vars)
                             (HS.TyVar b)
               , HS.FunBind [HS.Match dummy infV
                                      (List.map HS.PVar vars) Nothing
                                      (HS.UnGuardedRhs HS.unit_con)
                                      emptyBinds]
               ]
      Constructor{} | Just q == (nameOfSharp <$> kit) -> do
        let sharp = unqhname "d" q
            x     = ihname "x" 0
        return $
          [ HS.TypeSig dummy [sharp] $ fakeType $
              "forall a. a -> a"
          , HS.FunBind [HS.Match dummy sharp
                                 [HS.PVar x]
                                 Nothing
                                 (HS.UnGuardedRhs (HS.Var (HS.UnQual x)))
                                 emptyBinds]
          ]
      Function{} | Just q == (nameOfFlat <$> kit) -> do
        let flat = unqhname "d" q
            x    = ihname "x" 0
        return $
          [ HS.TypeSig dummy [flat] $ fakeType $
              "forall a. a -> a"
          , HS.FunBind [HS.Match dummy flat
                                 [HS.PVar x]
                                 Nothing
                                 (HS.UnGuardedRhs (HS.Var (HS.UnQual x)))
                                 emptyBinds]
          ]

      Axiom{} -> return $ fb axiomErr
      Primitive{ primName = s } -> fb <$> primBody s

      Function{} -> function (exportHaskell compiled) $ functionViaTreeless q

      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs }
        | Just (HsType ty) <- compiledHaskell compiled -> do
        ccscov <- ifM (noCheckCover q) (return []) $ do
            ccs <- List.concat <$> mapM checkConstructorType cs
            cov <- checkCover q ty np cs
            return $ ccs ++ cov
        return $ tvaldecl q (dataInduction d) 0 (np + ni) [] (Just __IMPOSSIBLE__) ++ ccscov
      Datatype{ dataPars = np, dataIxs = ni, dataClause = cl, dataCons = cs } -> do
        (ars, cds) <- unzip <$> mapM condecl cs
        return $ tvaldecl q (dataInduction d) (List.maximum (np:ars) - np) (np + ni) cds cl
      Constructor{} -> return []
      Record{ recClause = cl, recConHead = con, recFields = flds } -> do
        let c = conName con
        let noFields = length flds
        let ar = I.arity ty
        cd <- snd <$> condecl c
  --       cd <- case c of
  --         Nothing -> return $ cdecl q noFields
  --         Just c  -> snd <$> condecl c
        return $ tvaldecl q Inductive noFields ar [cd] cl
  where
  function :: Maybe HaskellExport -> TCM [HS.Decl] -> TCM [HS.Decl]
  function mhe fun = do
    ccls <- mkwhere <$> fun
    case mhe of
      Nothing -> return ccls
      Just (HsExport t name) -> do
        let tsig :: HS.Decl
            tsig = HS.TypeSig dummy [HS.Ident name] (fakeType t)

            def :: HS.Decl
            def = HS.FunBind [HS.Match dummy (HS.Ident name) [] Nothing (HS.UnGuardedRhs (hsVarUQ $ dname q)) emptyBinds]
        return ([tsig,def] ++ ccls)

  functionViaTreeless :: QName -> TCM [HS.Decl]
  functionViaTreeless q = caseMaybeM (toTreeless q) (pure []) $ \ treeless -> do

    used <- getCompiledArgUse q
    let dostrip = any not used

    e <- if dostrip then closedTerm (stripUnusedArguments used treeless)
                    else closedTerm treeless
    let (ps, b) = lamView e
        lamView e =
          case stripTopCoerce e of
            HS.Lambda _ ps b -> (ps, b)
            b                -> ([], b)
        stripTopCoerce (HS.Lambda i ps b) = HS.Lambda i ps $ stripTopCoerce b
        stripTopCoerce e =
          case hsAppView e of
            [c,  e] | c == mazCoerce -> e
            _                        -> e

        funbind f ps b = HS.FunBind [HS.Match dummy f ps Nothing (HS.UnGuardedRhs b) emptyBinds]

    -- The definition of the non-stripped function
    (ps0, _) <- lamView <$> closedTerm (foldr ($) T.TErased $ replicate (length used) T.TLam)
    let b0 = foldl HS.App (hsVarUQ $ duname q) [ hsVarUQ x | (~(HS.PVar x), True) <- zip ps0 used ]

    return $ if dostrip
      then [ funbind (dname q) ps0 b0
           , funbind (duname q) ps b ]
      else [ funbind (dname q) ps b ]

  mkwhere :: [HS.Decl] -> [HS.Decl]
  mkwhere (HS.FunBind [m0, HS.Match _     dn ps mt rhs emptyBinds] :
           fbs@(_:_)) =
          [HS.FunBind [m0, HS.Match dummy dn ps mt rhs bindsAux]]
    where
#if MIN_VERSION_haskell_src_exts(1,17,0)
    bindsAux :: Maybe HS.Binds
    bindsAux = Just $ HS.BDecls fbs
#else
    bindsAux :: HS.Binds
    bindsAux = HS.BDecls fbs
#endif
  mkwhere fbs = fbs

  fbWithType :: HaskellType -> HS.Exp -> [HS.Decl]
  fbWithType ty e =
    [ HS.TypeSig dummy [unqhname "d" q] $ fakeType ty ] ++ fb e

  fb :: HS.Exp -> [HS.Decl]
  fb e  = [HS.FunBind [HS.Match dummy (unqhname "d" q) [] Nothing
                                (HS.UnGuardedRhs $ e) emptyBinds]]

  axiomErr :: HS.Exp
  axiomErr = rtmError $ "postulate evaluated: " ++ show (A.qnameToConcrete q)

-- | Environment for naming of local variables.
--   Invariant: @reverse ccCxt ++ ccNameSupply@
data CCEnv = CCEnv
  { ccNameSupply :: NameSupply  -- ^ Supply of fresh names
  , ccCxt        :: CCContext   -- ^ Names currently in scope
  }

type NameSupply = [HS.Name]
type CCContext  = [HS.Name]

mapNameSupply :: (NameSupply -> NameSupply) -> CCEnv -> CCEnv
mapNameSupply f e = e { ccNameSupply = f (ccNameSupply e) }

mapContext :: (CCContext -> CCContext) -> CCEnv -> CCEnv
mapContext f e = e { ccCxt = f (ccCxt e) }

-- | Initial environment for expression generation.
initCCEnv :: CCEnv
initCCEnv = CCEnv
  { ccNameSupply = map (ihname "v") [0..]  -- DON'T CHANGE THESE NAMES!
  , ccCxt        = []
  }

-- | Term variables are de Bruijn indices.
lookupIndex :: Int -> CCContext -> HS.Name
lookupIndex i xs = fromMaybe __IMPOSSIBLE__ $ xs !!! i

type CC = ReaderT CCEnv TCM

freshNames :: Int -> ([HS.Name] -> CC a) -> CC a
freshNames n _ | n < 0 = __IMPOSSIBLE__
freshNames n cont = do
  (xs, rest) <- splitAt n <$> asks ccNameSupply
  local (mapNameSupply (const rest)) $ cont xs

-- | Introduce n variables into the context.
intros :: Int -> ([HS.Name] -> CC a) -> CC a
intros n cont = freshNames n $ \xs ->
  local (mapContext (reverse xs ++)) $ cont xs

checkConstructorType :: QName -> TCM [HS.Decl]
checkConstructorType q = do
  Just (HsDefn ty hs) <- compiledHaskell . defCompiledRep <$> getConstInfo q
  return [ HS.TypeSig dummy [unqhname "check" q] $ fakeType ty
         , HS.FunBind [HS.Match dummy (unqhname "check" q) [] Nothing
                                (HS.UnGuardedRhs $ fakeExp hs) emptyBinds]
         ]

checkCover :: QName -> HaskellType -> Nat -> [QName] -> TCM [HS.Decl]
checkCover q ty n cs = do
  let tvs = [ "a" ++ show i | i <- [1..n] ]
      makeClause c = do
        (a, _) <- conArityAndPars c
        Just (HsDefn _ hsc) <- compiledHaskell . defCompiledRep <$> getConstInfo c
        let pat = HS.PApp (HS.UnQual $ HS.Ident hsc) $ replicate a HS.PWildCard
        return $ HS.Alt dummy pat (HS.UnGuardedRhs $ HS.unit_con) emptyBinds

  cs <- mapM makeClause cs
  let rhs = case cs of
              [] -> fakeExp "()" -- There is no empty case statement in Haskell
              _  -> HS.Case (HS.Var $ HS.UnQual $ HS.Ident "x") cs

  return [ HS.TypeSig dummy [unqhname "cover" q] $ fakeType $ unwords (ty : tvs) ++ " -> ()"
         , HS.FunBind [HS.Match dummy (unqhname "cover" q) [HS.PVar $ HS.Ident "x"]
                                Nothing (HS.UnGuardedRhs rhs) emptyBinds]
         ]

closedTerm :: T.TTerm -> TCM HS.Exp
closedTerm v = hsCast <$> term v `runReaderT` initCCEnv

-- | Extract Agda term to Haskell expression.
--   Erased arguments are extracted as @()@.
--   Types are extracted as @()@.
term :: T.TTerm -> CC HS.Exp
term tm0 = case tm0 of
  T.TVar i -> do
    x <- lookupIndex i <$> asks ccCxt
    return $ hsVarUQ x
  T.TApp (T.TDef f) ts -> do
    used <- lift $ getCompiledArgUse f
    if any not used && length ts >= length used
      then do
        f <- lift $ HS.Var <$> xhqn "du" f  -- used stripped function
        f `apps` [ t | (t, True) <- zip ts $ used ++ repeat True ]
      else do
        t' <- term (T.TDef f)
        t' `apps` ts
  T.TApp t ts -> do
    t' <- term t
    t' `apps` ts
  T.TLam at -> do
    (nm:_) <- asks ccNameSupply
    intros 1 $ \ [x] ->
      hsLambda [HS.PVar x] <$> term at
  T.TLet t1 t2 -> do
    t1' <- term t1
    intros 1 $ \[x] -> do
      t2' <- term t2
      return $ hsLet x (hsCast t1') t2'

  T.TCase sc ct def alts -> do
    sc' <- term (T.TVar sc)
    alts' <- traverse (alt sc) alts
    def' <- term def
    let defAlt = HS.Alt dummy HS.PWildCard (HS.UnGuardedRhs def') emptyBinds

    return $ HS.Case (hsCast sc') (alts' ++ [defAlt])

  T.TLit l -> lift $ literal l
  T.TDef q -> do
    HS.Var <$> (lift $ xhqn "d" q)
  T.TCon q -> do
    kit <- lift coinductionKit
    if Just q == (nameOfSharp <$> kit)
      then HS.Var <$> lift (xhqn "d" q)
      else hsCast' . HS.Con <$> lift (conhqn q)
  T.TPrim p  -> return $ compilePrim p
  T.TUnit    -> return HS.unit_con
  T.TSort    -> return HS.unit_con
  T.TErased  -> return $ hsVarUQ $ HS.Ident mazErasedName
  T.TError e -> return $ case e of
    T.TUnreachable ->  rtmUnreachableError
  where apps =  foldM (\ h a -> HS.App h <$> term a)

compilePrim :: T.TPrim -> HS.Exp
compilePrim s =
  case s of
    T.PQuot -> fakeExp "(Prelude.quot :: Integer -> Integer -> Integer)"
    T.PRem -> fakeExp "(Prelude.rem :: Integer -> Integer -> Integer)"
    T.PSub -> fakeExp "((Prelude.-) :: Integer -> Integer -> Integer)"
    T.PAdd -> fakeExp "((Prelude.+) :: Integer -> Integer -> Integer)"
    T.PMul -> fakeExp "((Prelude.*) :: Integer -> Integer -> Integer)"
    T.PGeq -> fakeExp "((Prelude.>=) :: Integer -> Integer -> Bool)"
    T.PLt  -> fakeExp "((Prelude.<) :: Integer -> Integer -> Bool)"
    T.PEq  -> fakeExp "((Prelude.==) :: Integer -> Integer -> Bool)"
    T.PSeq -> HS.Var (hsName "seq")
    -- primitives only used by GuardsToPrims transformation, which MAlonzo doesn't use
    T.PIf  -> __IMPOSSIBLE__

alt :: Int -> T.TAlt -> CC HS.Alt
alt sc a = do
  case a of
    T.TACon {} -> do
      intros (T.aArity a) $ \xs -> do
        hConNm <- lift $ conhqn $ T.aCon a
        mkAlt (HS.PApp hConNm $ map HS.PVar xs)
    T.TAGuard g b -> do
      g <- term g
      b <- term b
      return $ HS.Alt dummy HS.PWildCard
                      (HS.GuardedRhss [HS.GuardedRhs dummy [HS.Qualifier g] b])
                      emptyBinds
    T.TALit { T.aLit = (LitQName _ q) } -> mkAlt (litqnamepat q)
    T.TALit { T.aLit = (LitString _ s) , T.aBody = b } -> do
      b <- term b
      sc <- term (T.TVar sc)
      let guard =
            HS.Var (HS.UnQual (HS.Ident "(==)")) `HS.App`
              sc`HS.App`
              litString s
      return $ HS.Alt dummy HS.PWildCard
                      (HS.GuardedRhss [HS.GuardedRhs dummy [HS.Qualifier guard] b])
                      emptyBinds
    T.TALit {} -> mkAlt (HS.PLit HS.Signless $ hslit $ T.aLit a)
  where
    mkAlt :: HS.Pat -> CC HS.Alt
    mkAlt pat = do
        body' <- term $ T.aBody a
        return $ HS.Alt dummy pat (HS.UnGuardedRhs $ hsCast body') emptyBinds

literal :: Literal -> TCM HS.Exp
literal l = case l of
  LitNat    _ _   -> return $ typed "Integer"
  LitFloat  _ _   -> return $ typed "Double"
  LitQName  _ x   -> return $ litqname x
  LitString _ s   -> return $ litString s
  _               -> return $ l'
  where l'    = HS.Lit $ hslit l
        typed = HS.ExpTypeSig dummy l' . HS.TyCon . rtmQual

hslit :: Literal -> HS.Literal
hslit l = case l of LitNat    _ x -> HS.Int    x
                    LitFloat  _ x -> HS.Frac   (toRational x)
                    LitChar   _ x -> HS.Char   x
                    LitQName  _ x -> __IMPOSSIBLE__
                    LitString _ _ -> __IMPOSSIBLE__

litString :: String -> HS.Exp
litString s =
  HS.Var (HS.Qual (HS.ModuleName "Data.Text") (HS.Ident "pack")) `HS.App`
    (HS.Lit $ HS.String s)

litqname :: QName -> HS.Exp
litqname x =
  HS.Con (HS.Qual mazRTE $ HS.Ident "QName") `HS.App`
  hsTypedInt n `HS.App`
  hsTypedInt m `HS.App`
  (rtmError "primQNameType: not implemented") `HS.App`
  (rtmError "primQNameDefinition: not implemented") `HS.App`
  HS.Lit (HS.String $ show x )
  where
    NameId n m = nameId $ qnameName x

litqnamepat :: QName -> HS.Pat
litqnamepat x =
  HS.PApp (HS.Qual mazRTE $ HS.Ident "QName")
          [ HS.PLit HS.Signless (HS.Int n)
          , HS.PLit HS.Signless (HS.Int m)
          , HS.PWildCard
          , HS.PWildCard
          , HS.PWildCard]
  where
    NameId n m = nameId $ qnameName x

condecl :: QName -> TCM (Nat, HS.ConDecl)
condecl q = do
  (ar, np) <- conArityAndPars q
  return $ (ar + np, cdecl q ar)

cdecl :: QName -> Nat -> HS.ConDecl
cdecl q n = HS.ConDecl (unqhname "C" q)
            [ HS.TyVar $ ihname "a" i | i <- [0 .. n - 1] ]

tvaldecl :: QName
         -> Induction
            -- ^ Is the type inductive or coinductive?
         -> Nat -> Nat -> [HS.ConDecl] -> Maybe Clause -> [HS.Decl]
tvaldecl q ind ntv npar cds cl =
  HS.FunBind [HS.Match dummy vn pvs Nothing
                       (HS.UnGuardedRhs HS.unit_con) emptyBinds] :
  maybe [HS.DataDecl dummy kind [] tn tvs
                     (List.map (HS.QualConDecl dummy [] []) cds) []]
        (const []) cl
  where
  (tn, vn) = (unqhname "T" q, unqhname "d" q)
  tvs = [ HS.UnkindedVar $ ihname "a" i | i <- [0 .. ntv  - 1]]
  pvs = [ HS.PVar        $ ihname "a" i | i <- [0 .. npar - 1]]

  -- Inductive data types consisting of a single constructor with a
  -- single argument are translated into newtypes.
  kind = case (ind, cds) of
    (Inductive, [HS.ConDecl _ [_]]) -> HS.NewType
    (Inductive, [HS.RecDecl _ [_]]) -> HS.NewType
    _                               -> HS.DataType

infodecl :: QName -> [HS.Decl] -> [HS.Decl]
infodecl _ [] = []
infodecl q ds = fakeD (unqhname "name" q) (show $ prettyShow q) : ds

--------------------------------------------------
-- Inserting unsafeCoerce
--------------------------------------------------

hsCast :: HS.Exp -> HS.Exp
{-
hsCast = addcast . go where
  addcast [e@(HS.Var(HS.UnQual(HS.Ident(c:ns))))] | c == 'v' && all isDigit ns = e
  addcast es = foldl HS.App mazCoerce es
  -- this need to be extended if you generate other kinds of exps.
  go (HS.App e1 e2    ) = go e1 ++ [hsCast e2]
  go (HS.Lambda _ ps e) = [ HS.Lambda dummy ps (hsCast e) ]
  go e = [e]
-}

-- TODO: what's the specification for hsCast, hsCast' and hsCoerce???
hsCast e = hsCoerce (hsCast' e)

hsCast' :: HS.Exp -> HS.Exp
hsCast' (HS.InfixApp e1 op e2) = hsCoerce $ HS.InfixApp (hsCast' e1) op (hsCast' e2)
hsCast' (HS.Lambda _ ps e)     = HS.Lambda dummy ps $ hsCast' e
hsCast' (HS.Let bs e)          = HS.Let bs $ hsCast' e
hsCast' (HS.Case sc alts)      = HS.Case (hsCast' sc) (map (hsMapAlt hsCast') alts)
hsCast' e =
  case hsAppView e of
    f : es -> foldl HS.App (hsCoerce f) (map hsCastApp es)
    _      -> __IMPOSSIBLE__

-- We still have to coerce function applications in arguments to coerced
-- functions.
hsCastApp :: HS.Exp -> HS.Exp
hsCastApp (HS.Lambda i ps b) = HS.Lambda i ps (hsCastApp b)
hsCastApp (HS.Case sc bs) = HS.Case (hsCastApp sc) (map (hsMapAlt hsCastApp) bs)
hsCastApp (HS.InfixApp e1 op e2) = HS.InfixApp (hsCastApp e1) op (hsCastApp e2)
hsCastApp e =
  case hsAppView e of
    f : es@(_:_) -> foldl HS.App (hsCoerce f) $ map hsCastApp es
    _ -> e

-- No coercion for literal integers
hsCoerce :: HS.Exp -> HS.Exp
hsCoerce e@(HS.ExpTypeSig _ (HS.Lit (HS.Int{})) _) = e
hsCoerce (HS.Case sc alts) = HS.Case sc (map (hsMapAlt hsCoerce) alts)
hsCoerce (HS.Let bs e) = HS.Let bs $ hsCoerce e
hsCoerce e =
  case hsAppView e of
    c : _ | c == mazCoerce || c == mazIncompleteMatch -> e
    _ -> mazCoerce `HS.App` e

--------------------------------------------------
-- Writing out a haskell module
--------------------------------------------------

copyRTEModules :: TCM ()
copyRTEModules = do
  dataDir <- lift getDataDir
  let srcDir = dataDir </> "MAlonzo" </> "src"
  (lift . copyDirContent srcDir) =<< compileDir

writeModule :: HS.Module -> TCM ()
writeModule (HS.Module l m ps w ex imp ds) = do
  -- Note that GHC assumes that sources use ASCII or UTF-8.
  out <- outFile m
  liftIO $ UTF8.writeFile out $ prettyPrint $
    HS.Module l m (p : ps) w ex imp ds
  where
  p = HS.LanguagePragma dummy $ List.map HS.Ident $
        [ "EmptyDataDecls"
        , "ExistentialQuantification"
        , "ScopedTypeVariables"
        , "NoMonomorphismRestriction"
        , "Rank2Types"
        ]


outFile' :: (HS.Pretty a, TransformBi HS.ModuleName (Wrap a)) =>
            a -> TCM (FilePath, FilePath)
outFile' m = do
  mdir <- compileDir
  let (fdir, fn) = splitFileName $ repldot pathSeparator $
                   prettyPrint m
  let dir = mdir </> fdir
      fp  = dir </> replaceExtension fn "hs"
  liftIO $ createDirectoryIfMissing True dir
  return (mdir, fp)
  where
  repldot c = List.map $ \ c' -> if c' == '.' then c else c'

outFile :: HS.ModuleName -> TCM FilePath
outFile m = snd <$> outFile' m

outFile_ :: TCM FilePath
outFile_ = outFile =<< curHsMod

callGHC :: IsMain -> Interface -> TCM ()
callGHC modIsMain i = do
  setInterface i
  mdir          <- compileDir
  hsmod         <- prettyPrint <$> curHsMod
  MName agdaMod <- curMName
  let outputName = case agdaMod of
        [] -> __IMPOSSIBLE__
        ms -> last ms
  (mdir, fp) <- outFile' =<< curHsMod
  opts       <- optGhcFlags <$> commandLineOptions

  let overridableArgs =
        [ "-O"] ++
        (if modIsMain == IsMain then ["-o", mdir </> show (nameConcrete outputName)] else []) ++
        [ "-Werror"]
      otherArgs       =
        [ "-i" ++ mdir] ++
        (if modIsMain == IsMain then ["-main-is", hsmod] else []) ++
        [ fp
        , "--make"
        , "-fwarn-incomplete-patterns"
        , "-fno-warn-overlapping-patterns"
        ]
      args     = overridableArgs ++ opts ++ otherArgs
      compiler = "ghc"

  -- Note: Some versions of GHC use stderr for progress reports. For
  -- those versions of GHC we don't print any progress information
  -- unless an error is encountered.
  callCompiler compiler args
