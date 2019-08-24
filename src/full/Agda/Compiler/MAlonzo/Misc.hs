
module Agda.Compiler.MAlonzo.Misc where

import Data.Char

import qualified Agda.Utils.Haskell.Syntax as HS

import Agda.Compiler.Common

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Pretty

import Agda.Utils.Impossible

--------------------------------------------------
-- Setting up Interface before compile
--------------------------------------------------

curHsMod :: TCM HS.ModuleName
curHsMod = mazMod <$> curMName

--------------------------------------------------
-- utilities for haskell names
--------------------------------------------------

-- The following naming scheme seems to be used:
--
-- * Types coming from Agda are named "T\<number\>".
--
-- * Other definitions coming from Agda are named "d\<number\>".
--   Exception: the main function is named "main".
--
-- * Names coming from Haskell must always be used qualified.
--   Exception: names from the Prelude.

ihname :: String -> Nat -> HS.Name
ihname s i = HS.Ident $ s ++ show i

unqhname :: String -> QName -> HS.Name
{- NOT A GOOD IDEA, see Issue 728
unqhname s q | ("d", "main") == (s, show(qnameName q)) = HS.Ident "main"
             | otherwise = ihname s (idnum $ nameId $ qnameName $ q)
-}
unqhname s q = ihname s (idnum $ nameId $ qnameName $ q)
   where idnum (NameId x _) = fromIntegral x

-- the toplevel module containing the given one
tlmodOf :: ModuleName -> TCM HS.ModuleName
tlmodOf = fmap mazMod . topLevelModuleName


-- qualify HS.Name n by the module of QName q, if necessary;
-- accumulates the used module in stImportedModules at the same time.
xqual :: QName -> HS.Name -> TCM HS.QName
xqual q n = do m1 <- topLevelModuleName (qnameModule q)
               m2 <- curMName
               if m1 == m2 then return (HS.UnQual n)
                  else addImport m1 >> return (HS.Qual (mazMod m1) n)

xhqn :: String -> QName -> TCM HS.QName
xhqn s q = xqual q (unqhname s q)

hsName :: String -> HS.QName
hsName s = HS.UnQual (HS.Ident s)

-- always use the original name for a constructor even when it's redefined.
conhqn :: QName -> TCM HS.QName
conhqn q = xhqn "C" =<< canonicalName q

-- qualify name s by the module of builtin b
bltQual :: String -> String -> TCM HS.QName
bltQual b s = do
  Def q _ <- getBuiltin b
  xqual q (HS.Ident s)

dname :: QName -> HS.Name
dname q = unqhname "d" q

-- | Name for definition stripped of unused arguments
duname :: QName -> HS.Name
duname q = unqhname "du" q

hsPrimOp :: String -> HS.QOp
hsPrimOp s = HS.QVarOp $ HS.UnQual $ HS.Symbol s

hsPrimOpApp :: String -> HS.Exp -> HS.Exp -> HS.Exp
hsPrimOpApp op e e1 = HS.InfixApp e (hsPrimOp op) e1

hsInt :: Integer -> HS.Exp
hsInt n = HS.Lit (HS.Int n)

hsTypedInt :: Integral a => a -> HS.Exp
hsTypedInt n = HS.ExpTypeSig (HS.Lit (HS.Int $ fromIntegral n)) (HS.TyCon (hsName "Integer"))

hsTypedDouble :: Real a => a -> HS.Exp
hsTypedDouble n = HS.ExpTypeSig (HS.Lit (HS.Frac $ toRational n)) (HS.TyCon (hsName "Double"))

hsLet :: HS.Name -> HS.Exp -> HS.Exp -> HS.Exp
hsLet x e b =
  HS.Let (HS.BDecls [HS.FunBind [HS.Match x [] (HS.UnGuardedRhs e) emptyBinds]]) b

hsVarUQ :: HS.Name -> HS.Exp
hsVarUQ = HS.Var . HS.UnQual

hsAppView :: HS.Exp -> [HS.Exp]
hsAppView = reverse . view
  where
    view (HS.App e e1) = e1 : view e
    view (HS.InfixApp e1 op e2) = [e2, e1, hsOpToExp op]
    view e = [e]

hsOpToExp :: HS.QOp -> HS.Exp
hsOpToExp (HS.QVarOp x) = HS.Var x

hsLambda :: [HS.Pat] -> HS.Exp -> HS.Exp
hsLambda ps (HS.Lambda ps1 e) = HS.Lambda (ps ++ ps1) e
hsLambda ps e = HS.Lambda ps e

hsMapAlt :: (HS.Exp -> HS.Exp) -> HS.Alt -> HS.Alt
hsMapAlt f (HS.Alt p rhs wh) = HS.Alt p (hsMapRHS f rhs) wh

hsMapRHS :: (HS.Exp -> HS.Exp) -> HS.Rhs -> HS.Rhs
hsMapRHS f (HS.UnGuardedRhs def) = HS.UnGuardedRhs (f def)
hsMapRHS f (HS.GuardedRhss es)   = HS.GuardedRhss [ HS.GuardedRhs g (f e) | HS.GuardedRhs g e <- es ]

--------------------------------------------------
-- Hard coded module names
--------------------------------------------------

mazstr :: String
mazstr = "MAlonzo.Code"

mazName :: Name
mazName = mkName_ __IMPOSSIBLE__ mazstr

mazMod' :: String -> HS.ModuleName
mazMod' s = HS.ModuleName $ mazstr ++ "." ++ s

mazMod :: ModuleName -> HS.ModuleName
mazMod = mazMod' . prettyShow

mazerror :: String -> a
mazerror msg = error $ mazstr ++ ": " ++ msg

mazCoerceName :: String
mazCoerceName = "coe"

mazErasedName :: String
mazErasedName = "erased"

mazAnyTypeName :: String
mazAnyTypeName = "AgdaAny"

mazCoerce :: HS.Exp
-- mazCoerce = HS.Var $ HS.Qual unsafeCoerceMod (HS.Ident "unsafeCoerce")
-- mazCoerce = HS.Var $ HS.Qual mazRTE $ HS.Ident mazCoerceName
mazCoerce = HS.Var $ HS.UnQual $ HS.Ident mazCoerceName

-- Andreas, 2011-11-16: error incomplete match now RTE-call
mazIncompleteMatch :: HS.Exp
mazIncompleteMatch = HS.Var $ HS.Qual mazRTE $ HS.Ident "mazIncompleteMatch"

rtmIncompleteMatch :: QName -> HS.Exp
rtmIncompleteMatch q = mazIncompleteMatch `HS.App` hsVarUQ (unqhname "name" q)

mazUnreachableError :: HS.Exp
mazUnreachableError = HS.Var $ HS.Qual mazRTE $ HS.Ident "mazUnreachableError"

rtmUnreachableError :: HS.Exp
rtmUnreachableError = mazUnreachableError

mazAnyType :: HS.Type
mazAnyType = HS.TyCon (hsName mazAnyTypeName)

mazRTE :: HS.ModuleName
mazRTE = HS.ModuleName "MAlonzo.RTE"

rtmQual :: String -> HS.QName
rtmQual = HS.UnQual . HS.Ident

rtmVar :: String -> HS.Exp
rtmVar  = HS.Var . rtmQual

rtmError :: String -> HS.Exp
rtmError s = rtmVar "error" `HS.App`
             (HS.Lit $ HS.String $ "MAlonzo Runtime Error: " ++ s)

unsafeCoerceMod :: HS.ModuleName
unsafeCoerceMod = HS.ModuleName "Unsafe.Coerce"

--------------------------------------------------
-- Sloppy ways to declare <name> = <string>
--------------------------------------------------

fakeD :: HS.Name -> String -> HS.Decl
fakeD v s = HS.FunBind [HS.Match v [] (HS.UnGuardedRhs $ fakeExp s) emptyBinds]

fakeDS :: String -> String -> HS.Decl
fakeDS = fakeD . HS.Ident

fakeDQ :: QName -> String -> HS.Decl
fakeDQ = fakeD . unqhname "d"

fakeType :: String -> HS.Type
fakeType = HS.FakeType

fakeExp :: String -> HS.Exp
fakeExp = HS.FakeExp

fakeDecl :: String -> HS.Decl
fakeDecl = HS.FakeDecl

--------------------------------------------------
-- Auxiliary definitions
--------------------------------------------------

emptyBinds :: Maybe HS.Binds
emptyBinds = Nothing

--------------------------------------------------
-- Utilities for Haskell modules names
--------------------------------------------------

-- | Can the character be used in a Haskell module name part
-- (@conid@)? This function is more restrictive than what the Haskell
-- report allows.

isModChar :: Char -> Bool
isModChar c =
  isLower c || isUpper c || isDigit c || c == '_' || c == '\''
