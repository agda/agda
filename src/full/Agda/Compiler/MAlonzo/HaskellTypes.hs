
-- | Translating Agda types to Haskell types. Used to ensure that imported
--   Haskell functions have the right type.

module Agda.Compiler.MAlonzo.HaskellTypes
  ( haskellType
  , checkConstructorCount
  , hsTelApproximation, hsTelApproximation'
  ) where

import Control.Monad         ( zipWithM )
import Control.Monad.Except  ( ExceptT(ExceptT), runExceptT, mapExceptT, catchError, throwError )
import Control.Monad.Trans   ( lift )
-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Telescope

import Agda.Compiler.MAlonzo.Pragmas
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty () --instance only

import qualified Agda.Utils.Haskell.Syntax as HS
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty (prettyShow)

import Agda.Utils.Impossible

hsQCon :: String -> String -> HS.Type
hsQCon m f = HS.TyCon $ HS.Qual (HS.ModuleName m) (HS.Ident f)

hsCon :: String -> HS.Type
hsCon = HS.TyCon . HS.UnQual . HS.Ident

hsUnit :: HS.Type
hsUnit = hsCon "()"

hsVar :: HS.Name -> HS.Type
hsVar = HS.TyVar

hsApp :: HS.Type -> [HS.Type] -> HS.Type
hsApp d ds = foldl HS.TyApp d ds

hsForall :: HS.Name -> HS.Type -> HS.Type
hsForall x = HS.TyForall [HS.UnkindedVar x]

-- Issue #5207: From ghc-9.0 we have to be careful with nested foralls.
hsFun :: HS.Type -> HS.Type -> HS.Type
hsFun a (HS.TyForall vs b) = HS.TyForall vs $ hsFun a b
hsFun a b = HS.TyFun a b

data WhyNot = NoPragmaFor QName
            | WrongPragmaFor Range QName
            | BadLambda Term
            | BadMeta Term
            | BadDontCare Term
            | NotCompiled QName

type ToHs = ExceptT WhyNot HsCompileM

notAHaskellType :: Term -> WhyNot -> TCM a
notAHaskellType top offender = typeError . GenericDocError =<< do
  fsep (pwords "The type" ++ [prettyTCM top] ++
        pwords "cannot be translated to a corresponding Haskell type, because it contains" ++
        reason offender) $$ possibleFix offender
  where
    reason (BadLambda        v) = pwords "the lambda term" ++ [prettyTCM v <> "."]
    reason (BadMeta          v) = pwords "a meta variable" ++ [prettyTCM v <> "."]
    reason (BadDontCare      v) = pwords "an erased term" ++ [prettyTCM v <> "."]
    reason (NotCompiled      x) = pwords "a name that is not compiled"
                                  ++ [parens (prettyTCM x) <> "."]
    reason (NoPragmaFor      x) = prettyTCM x : pwords "which does not have a COMPILE pragma."
    reason (WrongPragmaFor _ x) = prettyTCM x : pwords "which has the wrong kind of COMPILE pragma."

    possibleFix BadLambda{}     = empty
    possibleFix BadMeta{}       = empty
    possibleFix BadDontCare{}   = empty
    possibleFix NotCompiled{}   = empty
    possibleFix (NoPragmaFor d) = suggestPragma d $ "add a pragma"
    possibleFix (WrongPragmaFor r d) = suggestPragma d $
      sep [ "replace the value-level pragma at", nest 2 $ pretty r, "by" ]

    suggestPragma d action = do
      def    <- theDef <$> getConstInfo d
      let dataPragma n = ("data type HsD", "data HsD (" ++ intercalate " | " [ "C" ++ show i | i <- [1..n] ] ++ ")")
          typePragma   = ("type HsT", "type HsT")
          (hsThing, pragma) =
            case def of
              Datatype{ dataCons = cs } -> dataPragma (length cs)
              Record{}                  -> dataPragma 1
              _                         -> typePragma
      vcat [ sep ["Possible fix:", action]
           , nest 2 $ hsep [ "{-# COMPILE GHC", prettyTCM d, "=", text pragma, "#-}" ]
           , text ("for a suitable Haskell " ++ hsThing ++ ".")
           ]

runToHs :: Term -> ToHs a -> HsCompileM a
runToHs top m = either (liftTCM . notAHaskellType top) return =<< runExceptT m

liftE1' :: (forall b. (a -> m b) -> m b) -> (a -> ExceptT e m b) -> ExceptT e m b
liftE1' f k = ExceptT (f (runExceptT . k))

-- Only used in hsTypeApproximation below, and in that case we catch the error.
getHsType' :: QName -> HsCompileM HS.Type
getHsType' q = runToHs (Def q []) (getHsType q)

getHsType :: QName -> ToHs HS.Type
getHsType x = do
  unlessM (isCompiled x) $ throwError $ NotCompiled x

  d   <- liftTCM $ getHaskellPragma x
  env <- askGHCEnv
  let is t p = Just t == p env

      namedType = do
        -- For these builtin types, the type name (xhqn ...) refers to the
        -- generated, but unused, datatype and not the primitive type.
        if  | x `is` ghcEnvNat ||
              x `is` ghcEnvInteger -> return $ hsCon "Integer"
            | x `is` ghcEnvBool    -> return $ hsCon "Bool"
            | otherwise            ->
              lift $ hsCon . prettyShow <$> xhqn TypeK x
  mapExceptT (setCurrentRange d) $ case d of
    _ | x `is` ghcEnvList ->
        lift $ hsCon . prettyShow <$> xhqn TypeK x
        -- we ignore Haskell pragmas for List
    _ | x `is` ghcEnvMaybe ->
        lift $ hsCon . prettyShow <$> xhqn TypeK x
        -- we ignore Haskell pragmas for Maybe
    _ | x `is` ghcEnvInf ->
        return $ hsQCon "MAlonzo.RTE" "Infinity"
    Just HsDefn{}      -> throwError $ WrongPragmaFor (getRange d) x
    Just HsType{}      -> namedType
    Just HsData{}      -> namedType
    _                  -> throwError $ NoPragmaFor x

-- | Is the given thing compiled?

isCompiled :: HasConstInfo m => QName -> m Bool
isCompiled q = usableModality <$> getConstInfo q

-- | Does the name stand for a data or record type?

isData :: HasConstInfo m => QName -> m Bool
isData q = do
  def <- theDef <$> getConstInfo q
  return $ case def of
    Datatype{} -> True
    Record{}   -> True
    _          -> False

getHsVar :: (MonadFail tcm, MonadTCM tcm) => Nat -> tcm HS.Name
getHsVar i =
  HS.Ident . encodeString (VarK X) . prettyShow <$> nameOfBV i

haskellType' :: Type -> HsCompileM HS.Type
haskellType' t = runToHs (unEl t) (fromType t)
  where
    fromArgs = mapM (fromTerm . unArg)
    fromType = fromTerm . unEl
    fromTerm v = do
      v   <- liftTCM $ unSpine <$> reduce v
      reportSDoc "compile.haskell.type" 25 $ "toHaskellType " <+> prettyTCM v
      reportSDoc "compile.haskell.type" 50 $ "toHaskellType " <+> pretty v
      kit <- liftTCM coinductionKit
      case v of
        Var x es -> do
          let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          hsApp . hsVar <$> getHsVar x <*> fromArgs args
        Def d es -> do
          let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          hsApp <$> getHsType d <*> fromArgs args
        Pi a b ->
          if isBinderUsed b  -- Andreas, 2012-04-03.  Q: could we rely on Abs/NoAbs instead of again checking freeness of variable?
          then do
            hsA <- fromType (unDom a)
            liftE1' (underAbstraction a b) $ \ b ->
              hsForall <$> getHsVar 0 <*> (hsFun hsA <$> fromType b)
          else hsFun <$> fromType (unDom a) <*> fromType (noabsApp __IMPOSSIBLE__ b)
        Con c ci es -> do
          let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          hsApp <$> getHsType (conName c) <*> fromArgs args
        Lam{}      -> throwError (BadLambda v)
        Level{}    -> return hsUnit
        Lit{}      -> return hsUnit
        Sort{}     -> return hsUnit
        MetaV{}    -> throwError (BadMeta v)
        DontCare{} -> throwError (BadDontCare v)
        Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

haskellType :: QName -> HsCompileM HS.Type
haskellType q = do
  def <- getConstInfo q
  let (np, erased) =
        case theDef def of
          Constructor{ conPars, conErased }
            -> (conPars, fromMaybe [] conErased ++ repeat False)
          _ -> (0, repeat False)
      stripErased (True  : es) (HS.TyFun _ t)     = stripErased es t
      stripErased (False : es) (HS.TyFun s t)     = HS.TyFun s $ stripErased es t
      stripErased es           (HS.TyForall xs t) = HS.TyForall xs $ stripErased es t
      stripErased _            t                  = t
      underPars 0 a = stripErased erased <$> haskellType' a
      underPars n a = do
        a <- reduce a
        case unEl a of
          Pi a (NoAbs _ b) -> underPars (n - 1) b
          Pi a b  -> underAbstraction a b $ \b -> hsForall <$> getHsVar 0 <*> underPars (n - 1) b
          _       -> __IMPOSSIBLE__
  ty <- underPars np $ defType def
  reportSDoc "tc.pragma.compile" 10 $ (("Haskell type for" <+> prettyTCM q) <> ":") <?> pretty ty
  return ty

checkConstructorCount :: QName -> [QName] -> [HaskellCode] -> TCM ()
checkConstructorCount d cs hsCons
  | n == hn   = return ()
  | otherwise = do
    let n_forms_are = case hn of
          1 -> "1 Haskell constructor is"
          n -> show n ++ " Haskell constructors are"
        only | hn == 0   = ""
             | hn < n    = "only "
             | otherwise = ""

    genericDocError =<<
      fsep (prettyTCM d : pwords ("has " ++ show n ++
            " constructors, but " ++ only ++ n_forms_are ++ " given [" ++ unwords hsCons ++ "]"))
  where
    n  = length cs
    hn = length hsCons

-- Type approximations ----------------------------------------------------

data PolyApprox = PolyApprox | NoPolyApprox
  deriving (Eq)

hsTypeApproximation :: PolyApprox -> Int -> Type -> HsCompileM HS.Type
hsTypeApproximation poly fv t = do
  env <- askGHCEnv
  let is q b = Just q == b env
      tyCon  = HS.TyCon . HS.UnQual . HS.Ident
      rteCon = HS.TyCon . HS.Qual mazRTE . HS.Ident
      tyVar n i = HS.TyVar $ HS.Ident $ "a" ++ show (n - i)
  let go n t = do
        reportSDoc "compile.haskell.type" 25 $ "hsTypeApproximation " <+> prettyTCM t
        reportSDoc "compile.haskell.type" 50 $ "hsTypeApproximation " <+> pretty t
        t <- unSpine <$> reduce t
        case t of
          Var i _ | poly == PolyApprox -> return $ tyVar n i
          Pi a b -> hsFun <$> go n (unEl $ unDom a) <*> go (n + k) (unEl $ unAbs b)
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` ghcEnvList
            , Just k <- ghcEnvListArity env
            , [Apply t] <- drop (k-1) els ->
              HS.TyApp (tyCon "[]") <$> go n (unArg t)
            | q `is` ghcEnvMaybe
            , Just k <- ghcEnvMaybeArity env
            , [Apply t] <- drop (k-1) els ->
              HS.TyApp (tyCon "Maybe") <$> go n (unArg t)
            | q `is` ghcEnvBool    -> return $ tyCon "Bool"
            | q `is` ghcEnvInteger -> return $ tyCon "Integer"
            | q `is` ghcEnvNat     -> return $ tyCon "Integer"
            | q `is` ghcEnvWord64  -> return $ rteCon "Word64"
            | otherwise -> do
                let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims els
                foldl HS.TyApp <$> getHsType' q <*> mapM (go n . unArg) args
              `catchError` \ _ -> -- Not a Haskell type
                ifM (and2M (isCompiled q) (isData q))
                  (HS.TyCon <$> xhqn TypeK q)
                  (return mazAnyType)
          Sort{} -> return $ HS.FakeType "()"
          _ -> return mazAnyType
  go fv (unEl t)

-- Approximating polymorphic types is not actually a good idea unless we
-- actually keep track of type applications in recursive functions, and
-- generate parameterised datatypes. Otherwise we'll just coerce all type
-- variables to `Any` at the first `unsafeCoerce`.
hsTelApproximation :: Type -> HsCompileM ([HS.Type], HS.Type)
hsTelApproximation = hsTelApproximation' NoPolyApprox

hsTelApproximation' :: PolyApprox -> Type -> HsCompileM ([HS.Type], HS.Type)
hsTelApproximation' poly t = do
  TelV tel res <- telViewPath t
  let args = map (snd . unDom) (telToList tel)
  (,) <$> zipWithM (hsTypeApproximation poly) [0..] args <*> hsTypeApproximation poly (length args) res
