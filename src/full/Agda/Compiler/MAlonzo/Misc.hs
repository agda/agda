{-# LANGUAGE CPP #-}

module Agda.Compiler.MAlonzo.Misc where

import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Data.Function

import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

--------------------------------------------------
-- Setting up Interface before compile
--------------------------------------------------

setInterface :: Interface -> TCM ()
setInterface i = do
  stImportedModules .= Set.empty
  stCurrentModule   .= Just (iModuleName i)

curIF :: TCM Interface
curIF = do
  mName <- use stCurrentModule
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

curHsMod :: TCM HS.ModuleName
curHsMod = mazMod <$> curMName

curDefs :: TCM Definitions
curDefs = sigDefinitions <$> curSig

sigMName :: Signature -> ModuleName
sigMName sig = case Map.keys (sigSections sig) of
  []    -> __IMPOSSIBLE__
  m : _ -> m

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
tlmodOf = fmap mazMod . tlmname

tlmname :: ModuleName -> TCM ModuleName
tlmname m = do
  -- get the names of the visited modules
  visited <- List.map (iModuleName . miInterface) . Map.elems <$>
    getVisitedModules
  -- find the module with the longest matching prefix to m
  let ms = sortBy (compare `on` (length . mnameToList)) $
       List.filter (\ m' -> mnameToList m' `isPrefixOf` mnameToList m) visited
  case ms of
    (m' : _) -> return m'
    -- if we did not get anything, it may be because m is a section
    -- (a module _ )
    []       -> curMName
{-  NOT IMPOSSIBLE!
    _ -> do
      reportSDoc "impossible" 10 $ sep
        [ text $ "m = " ++ show m
        , text $ "should be contained in the visited modules " ++ show visited
        ]
      __IMPOSSIBLE__
-}

-- qualify HS.Name n by the module of QName q, if necessary;
-- accumulates the used module in stImportedModules at the same time.
xqual :: QName -> HS.Name -> TCM HS.QName
xqual q n = do m1 <- tlmname (qnameModule q)
               m2 <- curMName
               if m1 == m2 then return (HS.UnQual n)
                  else addImport m1 >> return (HS.Qual (mazMod m1) n)

xhqn :: String -> QName -> TCM HS.QName
xhqn s q = xqual q (unqhname s q)

-- always use the original name for a constructor even when it's redefined.
conhqn :: QName -> TCM HS.QName
conhqn q = do
    cq  <- canonicalName q
    def <- getConstInfo cq
    case (compiledHaskell (defCompiledRep def), theDef def) of
      (Just (HsDefn _ hs), Constructor{}) -> return $ HS.UnQual $ HS.Ident hs
      _                                   -> xhqn "C" cq

-- qualify name s by the module of builtin b
bltQual :: String -> String -> TCM HS.QName
bltQual b s = do
  Def q _ <- ignoreSharing <$> getBuiltin b
  xqual q (HS.Ident s)

-- Sub-naming for cascaded definitions for consecutive clauses.
dsubname :: QName -> Nat -> HS.Name
dsubname q i | i == 0    = unqhname "d"                     q
             | otherwise = unqhname ("d_" ++ show i ++ "_") q

hsVarUQ :: HS.Name -> HS.Exp
hsVarUQ = HS.Var . HS.UnQual

hsAppView :: HS.Exp -> [HS.Exp]
hsAppView = reverse . view
  where
    view (HS.App e e1) = e1 : view e
    view e = [e]

hsLambda :: [HS.Pat] -> HS.Exp -> HS.Exp
hsLambda ps (HS.Lambda i ps1 e) = HS.Lambda i (ps ++ ps1) e
hsLambda ps e = HS.Lambda dummy ps e


--------------------------------------------------
-- Hard coded module names
--------------------------------------------------

mazstr :: String
mazstr = "MAlonzo.Code"

mazName :: Name
mazName = mkName_ dummy mazstr

mazMod' :: String -> HS.ModuleName
mazMod' s = HS.ModuleName $ mazstr ++ "." ++ s

mazMod :: ModuleName -> HS.ModuleName
mazMod = mazMod' . prettyShow

mazerror :: String -> a
mazerror msg = error $ mazstr ++ ": " ++ msg

mazCoerce :: HS.Exp
-- mazCoerce = HS.Var $ HS.Qual unsafeCoerceMod (HS.Ident "unsafeCoerce")
mazCoerce = HS.Var $ HS.Qual mazRTE $ HS.Ident "mazCoerce"

-- Andreas, 2011-11-16: error incomplete match now RTE-call
mazIncompleteMatch :: HS.Exp
mazIncompleteMatch = HS.Var $ HS.Qual mazRTE $ HS.Ident "mazIncompleteMatch"

rtmIncompleteMatch :: QName -> HS.Exp
rtmIncompleteMatch q = mazIncompleteMatch `HS.App` hsVarUQ (unqhname "name" q)

mazRTE :: HS.ModuleName
mazRTE = HS.ModuleName "MAlonzo.RTE"

-- for Runtime module: Not really used (Runtime modules has been abolished).
rtmMod :: HS.ModuleName
rtmMod = mazMod' "Runtime"

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
fakeD v s = HS.FunBind [ HS.Match dummy v [] Nothing
                           (HS.UnGuardedRhs $ hsVarUQ $ HS.Ident $ s)
                           (HS.BDecls [])
                       ]

fakeDS :: String -> String -> HS.Decl
fakeDS = fakeD . HS.Ident

fakeDQ :: QName -> String -> HS.Decl
fakeDQ = fakeD . unqhname "d"

fakeType :: String -> HS.Type
fakeType = HS.TyVar . HS.Ident

fakeExp :: String -> HS.Exp
fakeExp = HS.Var . HS.UnQual . HS.Ident

dummy :: a
dummy = error "MAlonzo : this dummy value should not have been eval'ed."
