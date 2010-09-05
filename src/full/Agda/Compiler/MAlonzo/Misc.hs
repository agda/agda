{-# LANGUAGE CPP #-}

module Agda.Compiler.MAlonzo.Misc where

import Control.Monad.State
import Data.Generics
import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Maybe
import Data.Function
import Language.Haskell.Syntax
import System.IO
import System.Time

import Agda.Interaction.Imports
import Agda.Interaction.Monad
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.Pretty

import Agda.Utils.Impossible
#include "../../undefined.h"

--------------------------------------------------
-- Setting up Interface before compile
--------------------------------------------------

setInterface :: Interface -> TCM ()
setInterface i = modify $ \s -> s
  { stImportedModules = S.empty
  , stCurrentModule   = Just $ iModuleName i
  }

curIF :: TCM Interface
curIF = do
  mName <- stCurrentModule <$> get
  case mName of
    Nothing   -> __IMPOSSIBLE__
    Just name -> do
      mm <- getVisitedModule (toTopLevelModuleName name)
      case mm of
        Nothing -> __IMPOSSIBLE__
        Just mi -> return $ miInterface mi

curSig :: TCM Signature
curSig = iSignature <$> curIF

curMName :: TCM ModuleName
curMName = sigMName <$> curSig

curHsMod :: TCM Module
curHsMod = mazMod <$> curMName

curDefs :: TCM Definitions
curDefs = sigDefinitions <$> curSig

sigMName :: Signature -> ModuleName
sigMName sig = case M.keys (sigSections sig) of
  []    -> __IMPOSSIBLE__
  m : _ -> m

--------------------------------------------------
-- utilities for haskell names
--------------------------------------------------

-- The following naming scheme seems to be used:
--
-- * Types coming from Agda are named "T<number>".
--
-- * Other definitions coming from Agda are named "d<number>".
--   Exception: the main function is named "main".
--
-- * Names coming from Haskell must always be used qualified.
--   Exception: names from the Prelude.

ihname :: String -> Nat -> HsName
ihname s i = HsIdent $ s ++ show i

unqhname :: String -> QName -> HsName
unqhname s q | ("d", "main") == (s, show(qnameName q)) = HsIdent "main"
             | otherwise = ihname s (idnum $ nameId $ qnameName $ q)
  where idnum (NameId x _) = fromIntegral x

-- the toplevel module containing the given one
tlmodOf :: ModuleName -> TCM Module
tlmodOf = fmap mazMod . tlmname

tlmname :: ModuleName -> TCM ModuleName
tlmname m = do
  ms <- sortBy (compare `on` (length . mnameToList)) .
        L.filter (flip (isPrefixOf `on` mnameToList) m) <$>
        L.map (iModuleName . miInterface) . M.elems <$>
        getVisitedModules
  return $ case ms of (m' : _) -> m'; _ -> __IMPOSSIBLE__

-- qualify HsName n by the module of QName q, if necessary;
-- accumulates the used module in stImportedModules at the same time.
xqual :: QName -> HsName -> TCM HsQName
xqual q n = do m1 <- tlmname (qnameModule q)
               m2 <- curMName
               if m1 == m2 then return (UnQual n)
                  else addImport m1 >> return (Qual (mazMod m1) n)

xhqn :: String -> QName -> TCM HsQName
xhqn s q = xqual q (unqhname s q)

-- always use the original name for a constructor even when it's redefined.
conhqn :: QName -> TCM HsQName
conhqn q = do
    cq   <- canonicalName q
    defn <- theDef <$> getConstInfo cq
    case defn of Constructor{conHsCode = Just (_, hs)} -> return $ UnQual $ HsIdent hs
                 _                                     -> xhqn "C" cq

-- qualify name s by the module of builtin b
bltQual :: String -> String -> TCM HsQName
bltQual b s = do (Def q _) <- getBuiltin b; xqual q (HsIdent s)

-- sub-naming for cascaded definitions for concsecutive clauses
dsubname q i | i == 0    = unqhname "d"                     q
             | otherwise = unqhname ("d_" ++ show i ++ "_") q

hsVarUQ :: HsName -> HsExp
hsVarUQ = HsVar . UnQual

--------------------------------------------------
-- Hard coded module names
--------------------------------------------------

mazstr  = "MAlonzo"
mazName = mkName_ dummy mazstr
mazMod' s = Module $ mazstr ++ "." ++ s
mazMod :: ModuleName -> Module
mazMod = mazMod' . show
mazerror msg = error $ mazstr ++ ": " ++ msg
mazCoerce = HsVar $ Qual unsafeCoerceMod (HsIdent "unsafeCoerce")

-- for Runtime module: Not really used (Runtime modules has been abolished).
rtmMod  = mazMod' "Runtime"
rtmQual = UnQual . HsIdent
rtmVar  = HsVar . rtmQual
rtmError s = rtmVar "error" `HsApp`
             (HsLit $ HsString $ "MAlonzo Runtime Error: " ++ s)

unsafeCoerceMod = Module "Unsafe.Coerce"

--------------------------------------------------
-- Sloppy ways to declare <name> = <string>
--------------------------------------------------

fakeD :: HsName -> String -> HsDecl
fakeD v s = HsFunBind [HsMatch dummy v []
                      (HsUnGuardedRhs $ hsVarUQ $ HsIdent $ s) [] ]

fakeDS :: String -> String -> HsDecl
fakeDS = fakeD . HsIdent

fakeDQ :: QName -> String -> HsDecl
fakeDQ = fakeD . unqhname "d"

fakeType :: String -> HsQualType
fakeType = HsQualType [] . HsTyVar . HsIdent

fakeExp :: String -> HsExp
fakeExp = HsVar . UnQual . HsIdent

dummy :: a
dummy = error "MAlonzo : this dummy value should not have been eval'ed."


--------------------------------------------------
-- For Debugging
--------------------------------------------------
gshow' :: Data a => a -> String
gshow' = ( \t ->
           "("
           ++ showConstr (toConstr t)
           ++ concat (gmapQ ((++) " " . gshow') t)
           ++ ")" )
         `extQ` (show :: String -> String)
         `extQ` (show :: Name -> String)
         `extQ` (show :: QName -> String)
         `extQ` (show :: ModuleName -> String)
         `extQ` (gshow' . M.toList :: M.Map QName [AbstractName] -> String)
         `extQ` (gshow' . M.toList :: M.Map QName [AbstractModule] -> String)
         `extQ` (gshow' . M.toList :: M.Map ModuleName Section -> String)
         `extQ` (gshow' . M.toList :: M.Map QName Definition -> String)
         `extQ` (gshow' . M.toList :: M.Map TermHead [Pattern] -> String)
         `extQ` (gshow' . M.toList :: M.Map TermHead [Arg Pattern] -> String)
         `extQ` (gshow' . M.toList :: M.Map String (Builtin String) -> String)
         `extQ` (show :: Scope -> String)


