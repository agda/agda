
-- | Translating Agda types to Haskell types. Used to ensure that imported
--   Haskell functions have the right type.

module Agda.Compiler.MAlonzo.HaskellTypes
  ( haskellType
  , checkConstructorCount
  , hsTelApproximation, hsTelApproximation'
  ) where

import Control.Monad (zipWithM)
import Control.Monad.Fail (MonadFail)
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive (getBuiltinName)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Telescope

import Agda.Compiler.MAlonzo.Pragmas
import Agda.Compiler.MAlonzo.Misc
import Agda.Compiler.MAlonzo.Pretty () --instance only

import qualified Agda.Utils.Haskell.Syntax as HS
import Agda.Utils.Except
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Null

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

data WhyNot = NoPragmaFor QName
            | WrongPragmaFor Range QName
            | BadLambda Term
            | BadMeta Term
            | BadDontCare Term

type ToHs = ExceptT WhyNot TCM

notAHaskellType :: Term -> WhyNot -> TCM a
notAHaskellType top offender = typeError . GenericDocError =<< do
  fsep (pwords "The type" ++ [prettyTCM top] ++
        pwords "cannot be translated to a corresponding Haskell type, because it contains" ++
        reason offender) $$ possibleFix offender
  where
    reason (BadLambda        v) = pwords "the lambda term" ++ [prettyTCM v <> "."]
    reason (BadMeta          v) = pwords "a meta variable" ++ [prettyTCM v <> "."]
    reason (BadDontCare      v) = pwords "an erased term" ++ [prettyTCM v <> "."]
    reason (NoPragmaFor      x) = [prettyTCM x] ++ pwords "which does not have a COMPILE pragma."
    reason (WrongPragmaFor _ x) = [prettyTCM x] ++ pwords "which has the wrong kind of COMPILE pragma."

    possibleFix BadLambda{}     = empty
    possibleFix BadMeta{}       = empty
    possibleFix BadDontCare{}   = empty
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

runToHs :: Term -> ToHs a -> TCM a
runToHs top m = either (notAHaskellType top) return =<< runExceptT m

liftE1 :: (forall a. m a -> m a) -> ExceptT e m a -> ExceptT e m a
liftE1 f = mkExceptT . f . runExceptT

liftE1' :: (forall b. (a -> m b) -> m b) -> (a -> ExceptT e m b) -> ExceptT e m b
liftE1' f k = mkExceptT (f (runExceptT . k))

-- Only used in hsTypeApproximation below, and in that case we catch the error.
getHsType' :: QName -> TCM HS.Type
getHsType' q = runToHs (Def q []) (getHsType q)

getHsType :: QName -> ToHs HS.Type
getHsType x = do
  d <- liftTCM $ getHaskellPragma x
  list <- liftTCM $ getBuiltinName builtinList
  inf  <- liftTCM $ getBuiltinName builtinInf
  let namedType = liftTCM $ do
        -- For these builtin types, the type name (xhqn ...) refers to the
        -- generated, but unused, datatype and not the primitive type.
        nat  <- getBuiltinName builtinNat
        int  <- getBuiltinName builtinInteger
        bool <- getBuiltinName builtinBool
        if  | Just x `elem` [nat, int] -> return $ hsCon "Integer"
            | Just x == bool           -> return $ hsCon "Bool"
            | otherwise                -> hsCon . prettyShow <$> xhqn "T" x
  liftE1 (setCurrentRange d) $ case d of
    _ | Just x == list -> liftTCM $ hsCon . prettyShow <$> xhqn "T" x -- we ignore Haskell pragmas for List
    _ | Just x == inf  -> return $ hsQCon "MAlonzo.RTE" "Infinity"
    Just HsDefn{}      -> throwError $ WrongPragmaFor (getRange d) x
    Just HsType{}      -> namedType
    Just HsData{}      -> namedType
    _                  -> throwError $ NoPragmaFor x

getHsVar :: (MonadFail tcm, MonadTCM tcm) => Nat -> tcm HS.Name
getHsVar i = HS.Ident . encodeName <$> nameOfBV i
  where
    encodeName x = "x" ++ concatMap encode (prettyShow x)
    okChars = ['a'..'z'] ++ ['A'..'Y'] ++ "_'"
    encode 'Z' = "ZZ"
    encode c
      | c `elem` okChars = [c]
      | otherwise        = "Z" ++ show (fromEnum c)

haskellType' :: Type -> TCM HS.Type
haskellType' t = runToHs (unEl t) (fromType t)
  where
    fromArgs = mapM (fromTerm . unArg)
    fromType = fromTerm . unEl
    fromTerm v = do
      v   <- liftTCM $ unSpine <$> reduce v
      reportSLn "compile.haskell.type" 50 $ "toHaskellType " ++ show v
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
              hsForall <$> getHsVar 0 <*> (HS.TyFun hsA <$> fromType b)
          else HS.TyFun <$> fromType (unDom a) <*> fromType (noabsApp __IMPOSSIBLE__ b)
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

haskellType :: QName -> TCM HS.Type
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
      fsep ([prettyTCM d] ++ pwords ("has " ++ show n ++
            " constructors, but " ++ only ++ n_forms_are ++ " given [" ++ unwords hsCons ++ "]"))
  where
    n  = length cs
    hn = length hsCons

-- Type approximations ----------------------------------------------------

data PolyApprox = PolyApprox | NoPolyApprox
  deriving (Eq)

hsTypeApproximation :: PolyApprox -> Int -> Type -> TCM HS.Type
hsTypeApproximation poly fv t = do
  list <- getBuiltinName builtinList
  bool <- getBuiltinName builtinBool
  int  <- getBuiltinName builtinInteger
  nat  <- getBuiltinName builtinNat
  word <- getBuiltinName builtinWord64
  let is q b = Just q == b
      tyCon  = HS.TyCon . HS.UnQual . HS.Ident
      rteCon = HS.TyCon . HS.Qual mazRTE . HS.Ident
      tyVar n i = HS.TyVar $ HS.Ident $ "a" ++ show (n - i)
  let go n t = do
        t <- unSpine <$> reduce t
        case t of
          Var i _ | poly == PolyApprox -> return $ tyVar n i
          Pi a b -> HS.TyFun <$> go n (unEl $ unDom a) <*> go (n + k) (unEl $ unAbs b)
            where k = case b of Abs{} -> 1; NoAbs{} -> 0
          Def q els
            | q `is` list, Apply t <- last ([Proj ProjSystem __IMPOSSIBLE__] ++ els)
                        -> HS.TyApp (tyCon "[]") <$> go n (unArg t)
            | q `is` bool -> return $ tyCon "Bool"
            | q `is` int  -> return $ tyCon "Integer"
            | q `is` nat  -> return $ tyCon "Integer"
            | q `is` word -> return $ rteCon "Word64"
            | otherwise -> do
                let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims els
                foldl HS.TyApp <$> getHsType' q <*> mapM (go n . unArg) args
              `catchError` \ _ -> do -- Not a Haskell type
                def <- theDef <$> getConstInfo q
                let isData | Datatype{} <- def = True
                           | Record{}   <- def = True
                           | otherwise         = False
                if isData then HS.TyCon <$> xhqn "T" q
                          else return mazAnyType
          Sort{} -> return $ HS.FakeType "()"
          _ -> return mazAnyType
  go fv (unEl t)

-- Approximating polymorphic types is not actually a good idea unless we
-- actually keep track of type applications in recursive functions, and
-- generate parameterised datatypes. Otherwise we'll just coerce all type
-- variables to `Any` at the first `unsafeCoerce`.
hsTelApproximation :: Type -> TCM ([HS.Type], HS.Type)
hsTelApproximation = hsTelApproximation' NoPolyApprox

hsTelApproximation' :: PolyApprox -> Type -> TCM ([HS.Type], HS.Type)
hsTelApproximation' poly t = do
  TelV tel res <- telView t
  let args = map (snd . unDom) (telToList tel)
  (,) <$> zipWithM (hsTypeApproximation poly) [0..] args <*> hsTypeApproximation poly (length args) res
