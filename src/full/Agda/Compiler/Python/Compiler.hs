{-# LANGUAGE CPP #-}
module Agda.Compiler.Python.Compiler where

import Agda.Compiler.Common
import Agda.Compiler.MAlonzo.Compiler (ccNameSupply)
import Agda.Compiler.ToTreeless
import Agda.Compiler.Treeless.EliminateLiteralPatterns
import Agda.Compiler.Treeless.GuardsToPrims
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Treeless as T
import Agda.Syntax.Internal (Type)
import Agda.TypeChecking.Monad.Imports (getVisitedModules)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.Utils.Monad
import Agda.Utils.Maybe

import Agda.Compiler.Python.Lang        as Py hiding ((<.>), PythonCode)
import Language.Python.Common.AST       as Py
import Language.Python.Common.Pretty    as Py
import Language.Python.Common.PrettyAST as Py

import Control.Monad
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (asks)
import Data.List (intercalate)
import qualified Data.Map as Map (elems)

import Text.PrettyPrint

#include "undefined.h"
import Agda.Utils.Impossible

import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>), (<.>), dropFileName, joinPath)

infixl 4 <$$>

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
f <$$> x = fmap (fmap f) x

compilerMain' :: Interface -> TCM ()
compilerMain' i = compile i

compile :: Interface -> TCM ()
compile i = do
    writeModule =<< definitions =<< curDefs

{-
-- | A module name is just a qualified name.
--
-- The 'SetRange' instance for module names sets all individual ranges
-- to the given one.
newtype ModuleName = MName { mnameToList :: [Name] }
  deriving (Eq, Ord, Typeable)-}

writeModule :: Py.Module () -> TCM ()
writeModule m = do
  mname <- curMName
  liftIO $ do
    print $ "Compiling " ++ pythonModulePath mname
    createPythonModule mname
    writeFile (pythonModulePath mname) . renderStyle style' $ Py.pretty m
  where
    style' = style {lineLength = 80}

pythonModulePath :: ModuleName -> FilePath
pythonModulePath mname = joinPath (show <$> mnameToList mname) <.> "py"

pythonQName :: QName -> String
pythonQName q = intercalate "_" $ show <$> (nameConcrete <$> mnameToList (qnameModule q)) ++ [nameConcrete (qnameName q)]

createPythonModule :: ModuleName -> IO ()
createPythonModule mname = do
  let modulePath = pythonModulePath mname
  createDirectoryIfMissing True $ dropFileName modulePath
  writeFile (dropFileName modulePath </> "__init__.py") ""

closedTerm :: TTerm -> TCM ()
closedTerm _ = pure ()

type Expression = Either Py.Exp Py.Stmt

asExpr :: Py.Exp -> Expression
asExpr = Left

asStmt :: Py.Stmt -> Expression
asStmt = Right

returnExpr :: Monad m => Py.Exp -> m Expression
returnExpr = return . asExpr

-- TODO
freshName' :: String -> TCM String
freshName' = pure

-- | Extract Agda term to Haskell expression.
--   Erased arguments are extracted as @()@.
--   Types are extracted as @()@.
term :: T.TTerm -> TCM Expression
term tm0 = case tm0 of
  T.TVar i -> do
    returnExpr $ Py.Var (Py.ident ("tvar" ++ show i)) ()
    --__UNDEFINED__
    {- do
    x <- lookupIndex i <$> asks ccCxt
    return $ hsVarUQ x -}
  {-
  T.TApp (T.TDef f) ts -> __UNDEFINED__ do
    used <- lift $ getCompiledArgUse f
    if any not used && length ts >= length used
      then do
        f <- lift $ HS.Var <$> xhqn "du" f  -- used stripped function
        f `apps` [ t | (t, True) <- zip ts $ used ++ repeat True ]
      else do
        t' <- term (T.TDef f)
        t' `apps` ts -}
  T.TApp t ts -> do
    t' <- termE t
    t' `apps` ts
  T.TLam at -> do
    x <- freshName' "x"
    asExpr . Py.lambda [x] <$> termE at
  T.TLet t1 t2 -> __UNDEFINED__ {- do
    t1' <- term t1
    intros 1 $ \[x] -> do
      t2' <- term t2
      return $ hsLet x (hsCast t1') t2' -}

  T.TCase sc ct def alts -> __UNDEFINED__ {- do
    sc' <- term (T.TVar sc)
    alts' <- traverse (alt sc) alts
    def' <- term def
    let defAlt = HS.Alt dummy HS.PWildCard (HS.UnGuardedRhs def') emptyBinds

    return $ HS.Case (hsCast sc') (alts' ++ [defAlt]) -}

  T.TLit l -> asExpr <$> literal l

  T.TDef q -> do
    d <- getConstInfo q
    case theDef d of
        -- Datatypes and records are erased
        Datatype {} -> returnExpr $ Py.string_lit "*datatype"
        Record {} -> returnExpr $ Py.string_lit "*record"
        q' -> returnExpr $ Py.string_lit (show q') -- __UNDEFINED__ -- qname q

  T.TCon q -> __UNDEFINED__ {- do
    kit <- lift coinductionKit
    if Just q == (nameOfSharp <$> kit)
      then HS.Var <$> lift (xhqn "d" q)
      else hsCast' . HS.Con <$> lift (conhqn q) -}
  T.TPrim p  -> compilePrim p
  T.TUnit    -> returnExpr $ Py.unit_con {- return HS.unit_con -}
  T.TSort    -> returnExpr $ Py.unit_con {- return HS.unit_con -}
  T.TErased  -> returnExpr $ Py.unit_con
  T.TError e -> returnExpr $ case e of
    T.TUnreachable ->  rtmUnreachableError
  where
    apps t ts = do
      ts' <- mapM termE ts
      liftIO $ print $ length ts
      returnExpr $ Py.Call t (flip Py.ArgExpr () <$> ts') ()

termE :: T.TTerm -> TCM Py.Exp
termE = fmap (either id __IMPOSSIBLE__) . term

termS :: T.TTerm -> TCM Py.Stmt
termS = fmap (either __IMPOSSIBLE__ id) . term

definitions :: Definitions -> TCM (Py.Module ())
definitions defs = do
  -- es <- catMaybes <$> (mapM definition =<< (sortDefs <$> curDefs))
  (Py.Module . catMaybes) <$> mapM definition (sortDefs defs)

definition :: (QName, Definition) -> TCM (Maybe (Py.Statement ()))
definition (qname, def) = do
  def <- instantiateFull def
  let ls = []
  liftIO $ print def
  defn qname ls (defType def) Nothing (theDef def) -- TODO: Fix Nothing parameter
  -- return $ Py.Print False [Py.string_lit $ show def] False ()

pyMember :: Name -> Py.Expr ()
pyMember n =
  -- Anonymous fields are used for where clauses,
  -- and they're all given the concrete name "_",
  -- so we disambiguate them using their name id.
  case show n of
    "_" -> Py.Var (Py.ident ("_" ++ show (nameId n))) ()
    l   -> Py.Var (Py.ident l) ()


defn :: QName -> [MemberId] -> Type -> Maybe PythonCode -> Defn -> TCM (Maybe (Py.Statement ()))
{-
defn q ls t (Just e) Axiom =
  return $ Just $ PlainPython e
defn q ls t Nothing Axiom =
  return $ Just Undefined
defn q ls t (Just e) (Function {}) =
  return $ Just $ PlainPython e
-}
defn q ls t Nothing (Function {}) = do
  caseMaybeM (toTreeless q) (pure Nothing) $ \ treeless -> do
    funBody <- eliminateLiteralPatterns $ convertGuards $ treeless
    funBody' <- (either ((`Py.Return` ()) . Just) id)  <$> term funBody
    return . return $ Py.Fun (Py.ident (pythonQName q)) [] Nothing [funBody'] ()
{-
defn q ls t _ p@(Primitive {}) | primName p `Set.member` primitives =
  return $ Just $ PlainPython $ "agdaRTS." ++ primName p
defn q ls t (Just e) (Primitive {}) =
  return $ Just $ PlainPython e
defn q ls t _ (Primitive {}) =
  return $ Just Undefined
defn q ls t _ (Datatype {}) =
  return $ Just emp
defn q ls t (Just e) (Constructor {}) =
  return $ Just $ PlainPython e
defn q ls t _ (Constructor { conData = p, conPars = nc }) = do
  np <- return (arity t - nc)
  d <- getConstInfo p
  case theDef d of
    Record { recFields = flds } ->
      return $ Just (curriedLambda np (Object (fromList
        ( (last ls , Lambda 1
             (Apply (Lookup (Local (LocalId 0)) (last ls))
               [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
        : (zip [ jsMember (qnameName (unArg fld)) | fld <- flds ]
             [ Local (LocalId (np - i)) | i <- [1 .. np] ])))))
    _ ->
      return $ Just (curriedLambda (np + 1)
        (Apply (Lookup (Local (LocalId 0)) (last ls))
          [ Local (LocalId (np - i)) | i <- [0 .. np-1] ]))
defn q ls t _ (Record {}) =
  return $ Just emp
-}

defn _ _ _ _ _ = error "defn is not totally defined"

rtmUnreachableError :: Py.Exp
rtmUnreachableError = error "rtmUnreachableError"

mazErasedName :: String
mazErasedName = "erased"

compilePrim :: T.TPrim -> TCM Expression
compilePrim p =
  case p of
    T.PQuot -> returnExpr $ Py.op2lambda Py.Divide -- fakeExp "(Prelude.quot :: Integer -> Integer -> Integer)"
    T.PRem  -> returnExpr $ Py.op2lambda Py.Modulo -- fakeExp "(Prelude.rem :: Integer -> Integer -> Integer)"
    T.PSub  -> returnExpr $ Py.op2lambda Py.Divide -- fakeExp "((Prelude.-) :: Integer -> Integer -> Integer)"
    T.PAdd  -> returnExpr $ Py.op2lambda Py.Plus     -- fakeExp "((Prelude.+) :: Integer -> Integer -> Integer)"
    T.PMul  -> returnExpr $ Py.op2lambda Py.Multiply -- fakeExp "((Prelude.*) :: Integer -> Integer -> Integer)"
    T.PGeq  -> returnExpr $ Py.op2lambda Py.GreaterThanEquals -- fakeExp "((Prelude.>=) :: Integer -> Integer -> Bool)"
    T.PLt   -> returnExpr $ Py.op2lambda Py.LessThan -- fakeExp "((Prelude.<) :: Integer -> Integer -> Bool)"
    T.PEqI  -> returnExpr $ Py.op2lambda Py.Equality
    T.PEqF  -> returnExpr $ Py.op2lambda Py.Equality
    T.PEqS  -> returnExpr $ Py.op2lambda Py.Equality
    T.PEqC  -> returnExpr $ Py.op2lambda Py.Equality
    T.PEqQ  -> returnExpr $ Py.op2lambda Py.Equality
    T.PSeq  -> returnExpr $ Py.None () -- ??? How to compile
    T.PIf   -> do
      c <- freshName' "c"
      t <- freshName' "t"
      f <- freshName' "f"
      returnExpr $ Py.lambda [c, t, f] $
        Py.CondExpr (var t) (var c) (var f) ()


fakeExp :: String -> Py.Exp
fakeExp n = __UNDEFINED__

literal :: Literal -> TCM Py.Exp
literal l = case l of
  LitNat    _ x -> return $ Py.int_lit x
  LitFloat  _ x -> return $ Py.Float  x (show x) ()
  LitChar   _ x -> return $ Py.Strings [[x]] ()
  LitQName  _ x -> return $ litqname x
  LitString _ s -> return $ Py.Strings [s] ()
  LitMeta{}     -> __IMPOSSIBLE__

-- FIXME: Qualified module name and normal function call
litqname :: QName -> Py.Exp
litqname x =
  Py.Call
    (Py.string_lit "QName")
    [Py.ArgExpr (Py.word64_lit n) (), Py.ArgExpr (Py.word64_lit m) ()]
    ()
  where
    NameId n m = nameId $ qnameName x

{-
https://hackage.haskell.org/package/language-python-0.5.3/docs/Language-Python-Common-AST.html#t:Statement
https://hackage.haskell.org/package/language-python-0.5.3/docs/Language-Python-Common-AST.html#t:Expr
-}
