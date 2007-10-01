{-# OPTIONS -cpp #-}

module TypeChecking.Rules.Decl where

import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map (Map)

import qualified Syntax.Abstract as A
import Syntax.Internal
import qualified Syntax.Info as Info
import Syntax.Position
import Syntax.Common

import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Monad.Mutual
import TypeChecking.Pretty
import TypeChecking.Constraints
import TypeChecking.Positivity
import TypeChecking.Primitive
import TypeChecking.Conversion
import TypeChecking.Substitute
import TypeChecking.Reduce

import TypeChecking.Rules.Term	  ( checkArguments, checkArguments_, checkTelescope, isType_, ExpandHidden(..) )
import TypeChecking.Rules.Data	  ( checkDataDef )
import TypeChecking.Rules.Record  ( checkRecDef )
import TypeChecking.Rules.Def	  ( checkFunDef )
import TypeChecking.Rules.Builtin ( bindBuiltin )

import Utils.Size
import Utils.Monad

#include "../../undefined.h"

-- | Type check a sequence of declarations.
checkDecls :: [A.Declaration] -> TCM ()
checkDecls ds = mapM_ checkDecl ds


-- | Type check a single declaration.
checkDecl :: A.Declaration -> TCM ()
checkDecl d =
    case d of
	A.Axiom i x e		     -> checkAxiom i x e
	A.Primitive i x e	     -> checkPrimitive i x e
	A.Definition i ts ds	     -> checkMutual i ts ds
	A.Section i x tel ds	     -> checkSection i x tel ds
	A.Apply i x tel m args rd rm -> checkSectionApplication i x tel m args rd rm
	A.Import i x		     -> checkImport i x
	A.Pragma i p		     -> checkPragma i p
	A.ScopedDecl scope ds	     -> setScope scope >> checkDecls ds
	    -- open is just an artifact from the concrete syntax


-- | Type check an axiom.
checkAxiom :: Info.DefInfo -> QName -> A.Expr -> TCM ()
checkAxiom _ x e = do
  t <- isType_ e
  reportSDoc "tc.decl.ax" 10 $ sep
    [ text "checked axiom"
    , nest 2 $ prettyTCM x <+> text ":" <+> prettyTCM t
    ]
  addConstant x (Defn x t (defaultDisplayForm x) 0 Axiom)


-- | Type check a primitive function declaration.
checkPrimitive :: Info.DefInfo -> QName -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) (qnameName x) e) $ do  -- TODO!! (qnameName)
    PrimImpl t' pf <- lookupPrimitiveFunction (nameString $ qnameName x)
    t <- isType_ e
    noConstraints $ equalType t t'
    let s  = show $ nameConcrete $ qnameName x
    bindPrimitive s $ pf { primFunName = x }
    addConstant x (Defn x t (defaultDisplayForm x) 0 $ Primitive (Info.defAbstract i) s [])
    where
	nameString (Name _ x _ _) = show x


-- | Check a pragma.
checkPragma :: Range -> A.Pragma -> TCM ()
checkPragma r p =
    traceCall (CheckPragma r p) $ case p of
	A.BuiltinPragma x e -> bindBuiltin x e
	A.OptionsPragma _   -> __IMPOSSIBLE__	-- not allowed here

-- | Type check a bunch of mutual inductive recursive definitions.
checkMutual :: Info.DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
checkMutual i ts ds = inMutualBlock $ do
  mapM_ checkTypeSignature ts
  mapM_ checkDefinition ds
  whenM positivityCheckEnabled $
      checkStrictlyPositive [ name | A.DataDef _ name _ _ <- ds ]


-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.ScopedDecl scope ds) = do
  setScope scope
  mapM_ checkTypeSignature ds
checkTypeSignature (A.Axiom i x e) =
    case Info.defAccess i of
	PublicAccess  -> inConcreteMode $ checkAxiom i x e
	PrivateAccess -> inAbstractMode $ checkAxiom i x e
checkTypeSignature _ = __IMPOSSIBLE__	-- type signatures are always axioms


-- | Check an inductive or recursive definition. Assumes the type has has been
--   checked and added to the signature.
checkDefinition :: A.Definition -> TCM ()
checkDefinition d =
    case d of
	A.FunDef i x cs	    -> abstract (Info.defAbstract i) $ checkFunDef i x cs
	A.DataDef i x ps cs -> abstract (Info.defAbstract i) $ checkDataDef i x ps cs
	A.RecDef i x ps cs  -> abstract (Info.defAbstract i) $ checkRecDef i x ps cs
    where
	-- Concrete definitions cannot use information about abstract things.
	abstract ConcreteDef = inConcreteMode
	abstract AbstractDef = inAbstractMode


-- | Type check a module.
checkSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkSection i x tel ds =
  checkTelescope tel $ \tel' -> do
    addSection x (size tel')
    verbose 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection x
      liftIO $ putStrLn $ "checking section " ++ show dx ++ " " ++ show dtel
      liftIO $ putStrLn $ "    actual tele: " ++ show dtel'
    withCurrentModule x $ checkDecls ds

-- | Check an application of a section.
checkSectionApplication ::
  Info.ModuleInfo -> ModuleName -> A.Telescope -> ModuleName -> [NamedArg A.Expr] ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
checkSectionApplication i m1 ptel m2 args rd rm =
  checkTelescope ptel $ \ptel -> do
  addSection m1 (size ptel)
  tel <- lookupSection m2
  vs  <- freeVarsToApply $ qnameFromList $ mnameToList m2
  reportSDoc "tc.section.apply" 15 $ vcat
    [ text "applying section" <+> prettyTCM m2
    , nest 2 $ text "ptel =" <+> prettyTCM ptel
    , nest 2 $ text "tel  =" <+> prettyTCM tel
    ]
  (ts, cs)  <- checkArguments_ DontExpandLast (getRange i) args (apply tel vs)
  noConstraints $ return cs
  reportSDoc "tc.section.apply" 20 $ vcat
    [ sep [ text "applySection", prettyTCM m1, text "=", prettyTCM m2, fsep $ map prettyTCM (vs ++ ts) ]
    , nest 2 $ text "  defs:" <+> text (show rd)
    , nest 2 $ text "  mods:" <+> text (show rm)
    ]
  args <- instantiateFull $ vs ++ ts
  applySection m1 ptel m2 args rd rm

-- | Type check an import declaration. Actually doesn't do anything, since all
--   the work is done when scope checking.
checkImport :: Info.ModuleInfo -> ModuleName -> TCM ()
checkImport i x = return ()


