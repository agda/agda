{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Decl where

import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Agda.Utils.IO.Locale as LocIO

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Mutual
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Forcing

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.Data    ( checkDataDef )
import Agda.TypeChecking.Rules.Record  ( checkRecDef )
import Agda.TypeChecking.Rules.Def     ( checkFunDef )
import Agda.TypeChecking.Rules.Builtin ( bindBuiltin, bindBuiltinType1 )

import Agda.Compiler.HaskellTypes

import Agda.Utils.Size
import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Type check a sequence of declarations.
checkDecls :: [A.Declaration] -> TCM ()
checkDecls ds = do
  mapM_ checkDecl ds
  whenM onTopLevel unfreezeMetas

-- | Type check a single declaration.
checkDecl :: A.Declaration -> TCM ()
checkDecl d = do
    leaveTopLevelConditionally d $ case d of
	A.Axiom i rel x e            -> checkAxiom i rel x e
        A.Field{}                    -> typeError FieldOutsideRecord
	A.Primitive i x e	     -> checkPrimitive i x e
	A.Definition i ts ds	     -> checkMutual i ts ds
	A.Section i x tel ds	     -> checkSection i x tel ds
	A.Apply i x tel m args rd rm -> checkSectionApplication i x tel m args rd rm
	A.Import i x		     -> checkImport i x
	A.Pragma i p		     -> checkPragma i p
	A.ScopedDecl scope ds	     -> setScope scope >> checkDecls ds
        A.Open _ _                   -> return ()
	    -- open is just an artifact from the concrete syntax
            -- retained for highlighting purposes
    solveSizeConstraints
    whenM onTopLevel freezeMetas
    where
      leaveTopLevelConditionally d =
        case d of
          A.Section{}    -> id
          A.ScopedDecl{} -> id
          _              -> leaveTopLevel

-- | Type check an axiom.
checkAxiom :: Info.DefInfo -> Relevance -> QName -> A.Expr -> TCM ()
checkAxiom _ rel x e = do
  t <- isType_ e
  reportSDoc "tc.decl.ax" 10 $ sep
    [ text "checked axiom"
    , nest 2 $ prettyTCM rel <> prettyTCM x <+> text ":" <+> (prettyTCM =<< instantiateFull t)
    ]
  -- Not safe. See Issue 330
  -- t <- addForcingAnnotations t
  addConstant x (Defn rel x t (defaultDisplayForm x) 0 $ Axiom Nothing Nothing)
  solveSizeConstraints


-- | Type check a primitive function declaration.
checkPrimitive :: Info.DefInfo -> QName -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) (qnameName x) e) $ do  -- TODO!! (qnameName)
    PrimImpl t' pf <- lookupPrimitiveFunction (nameString $ qnameName x)
    t <- isType_ e
    noConstraints $ equalType t t'
    let s  = show $ nameConcrete $ qnameName x
    bindPrimitive s $ pf { primFunName = x }
    addConstant x (Defn Relevant x t (defaultDisplayForm x) 0 $
                Primitive (Info.defAbstract i) s Nothing Nothing)
    where
	nameString (Name _ x _ _) = show x


-- | Check a pragma.
checkPragma :: Range -> A.Pragma -> TCM ()
checkPragma r p =
    traceCall (CheckPragma r p) $ case p of
	A.BuiltinPragma x e -> bindBuiltin x e
        A.CompiledTypePragma x hs -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> addHaskellType x hs
            _       -> typeError $ GenericError
                        "COMPILED_TYPE directive only works on postulates."
          -- TODO: hack
          when (hs == builtinIO) $
            bindBuiltinType1 builtinIO (A.Def x)
        A.CompiledDataPragma x hs hcs -> do
          def <- getConstInfo x
          -- Check that the pragma appears in the same module
          -- as the datatype.
          do m <- currentModule
             let m' = qnameModule $ defName def
             unless (m == m') $ typeError $ GenericError $
              "COMPILED_DATA directives must appear in the same module " ++
              "as their corresponding datatype definition,"
          case theDef def of
            Datatype{dataCons = cs}
              | length cs /= length hcs -> do
                  let n_forms_are = case length hcs of
                        1 -> "1 compiled form is"
                        n -> show n ++ " compiled forms are"
                      only | null hcs               = ""
                           | length hcs < length cs = "only "
                           | otherwise              = ""

                  err <- fsep $ [prettyTCM x] ++ pwords ("has " ++ show (length cs) ++
                                " constructors, but " ++ only ++ n_forms_are ++ " given [" ++ unwords hcs ++ "]")
                  typeError $ GenericError $ show err
              | otherwise -> do
                addHaskellType x hs
                let computeHaskellType c = do
                      def <- getConstInfo c
                      let Constructor{ conPars = np } = theDef def
                          underPars 0 a = haskellType a
                          underPars n a = do
                            a <- reduce a
                            case unEl a of
                              Pi a b  -> underAbstraction a b $ underPars (n - 1)
                              Fun a b -> underPars (n - 1) b
                              _       -> __IMPOSSIBLE__
                      ty <- underPars np $ defType def
                      reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show c ++ ": " ++ ty
                      return ty
                hts <- mapM computeHaskellType cs
                sequence_ $ zipWith3 addHaskellCode cs hts hcs
            _ -> typeError $ GenericError "COMPILED_DATA on non datatype"
        A.CompiledPragma x hs -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> do
              ty <- haskellType $ defType def
              reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show x ++ ": " ++ ty
              addHaskellCode x ty hs
            _   -> typeError $ GenericError "COMPILED directive only works on postulates."
        A.CompiledEpicPragma x ep -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> do
              --ty <- haskellType $ defType def
              --reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show x ++ ": " ++ ty
              addEpicCode x ep
            _   -> typeError $ GenericError "COMPILED_EPIC directive only works on postulates."
	A.OptionsPragma _   -> __IMPOSSIBLE__	-- not allowed here
        A.EtaPragma r -> modifySignature eta
          where
            eta sig = sig { sigDefinitions = Map.adjust setEta r defs }
              where
                setEta def = def { theDef = setEtad $ theDef def }
                setEtad d   = case d of
                  Record{}   -> d { recEtaEquality = True }
                  _          -> d
                defs	  = sigDefinitions sig

-- | Type check a bunch of mutual inductive recursive definitions.
checkMutual :: Info.DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
checkMutual i ts ds = inMutualBlock $ do
  mapM_ checkTypeSignature ts
  mapM_ checkDefinition ds
  checkStrictlyPositive =<< currentMutualBlock


-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.ScopedDecl scope ds) = do
  setScope scope
  mapM_ checkTypeSignature ds
checkTypeSignature (A.Axiom i rel x e) =
    case Info.defAccess i of
	PublicAccess  -> inConcreteMode $ checkAxiom i rel x e
	PrivateAccess -> inAbstractMode $ checkAxiom i rel x e
checkTypeSignature _ = __IMPOSSIBLE__	-- type signatures are always axioms


-- | Check an inductive or recursive definition. Assumes the type has has been
--   checked and added to the signature.
checkDefinition :: A.Definition -> TCM ()
checkDefinition d =
    case d of
	A.FunDef i x cs          -> abstract (Info.defAbstract i) $ checkFunDef NotDelayed i x cs
	A.DataDef i x ps cs      -> abstract (Info.defAbstract i) $ checkDataDef i x ps cs
	A.RecDef i x mIFS c ps tel cs -> abstract (Info.defAbstract i) $ checkRecDef i x mIFS c ps tel cs
        A.ScopedDef scope d      -> setScope scope >> checkDefinition d
    where
	-- Concrete definitions cannot use information about abstract things.
	abstract ConcreteDef = inConcreteMode
	abstract AbstractDef = inAbstractMode


-- | Type check a module.
checkSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkSection i x tel ds =
  checkTelescope_ tel $ \tel' -> do
    addSection x (size tel')
    verboseS "tc.section.check" 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection x
      liftIO $ LocIO.putStrLn $ "checking section " ++ show dx ++ " " ++ show dtel
      liftIO $ LocIO.putStrLn $ "    actual tele: " ++ show dtel'
    withCurrentModule x $ checkDecls ds

checkModuleArity :: ModuleName -> Telescope -> [NamedArg A.Expr] -> TCM Telescope
checkModuleArity m tel args = check tel args
  where
    bad = typeError $ ModuleArityMismatch m tel args

    check eta []             = return eta
    check EmptyTel (_:_)     = bad
    check (ExtendTel (Arg h _ _) (Abs y tel)) args0@(Arg h' _ (Named name _) : args) =
      case (h, h', name) of
        (ImplicitFromScope, NotHidden, _) -> check tel args0
        (ImplicitFromScope, Hidden, _) -> bad
        (ImplicitFromScope, ImplicitFromScope, Nothing) -> check tel args
        (ImplicitFromScope, ImplicitFromScope, Just x)
          | x == y                -> check tel args
          | otherwise             -> check tel args0
        (Hidden, NotHidden, _)    -> check tel args0
        (Hidden, ImplicitFromScope, _)    -> bad
        (Hidden, Hidden, Nothing) -> check tel args
        (Hidden, Hidden, Just x)
          | x == y                -> check tel args
          | otherwise             -> check tel args0
        (NotHidden, NotHidden, _) -> check tel args
        (NotHidden, Hidden, _)    -> bad
        (NotHidden, ImplicitFromScope, _)    -> bad

-- | Check an application of a section.
checkSectionApplication ::
  Info.ModuleInfo -> ModuleName -> A.Telescope -> ModuleName -> [NamedArg A.Expr] ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
checkSectionApplication i m1 ptel m2 args rd rm =
  traceCall (CheckSectionApplication (getRange i) m1 ptel m2 args) $
  checkTelescope_ ptel $ \ptel -> do
  tel <- lookupSection m2
  vs  <- freeVarsToApply $ qnameFromList $ mnameToList m2
  let tel' = apply tel vs
  etaTel <- checkModuleArity m2 tel' args
  let tel'' = telFromList $ take (size tel' - size etaTel) $ telToList tel'
  addCtxTel etaTel $ addSection m1 (size ptel + size etaTel)
  reportSDoc "tc.section.apply" 15 $ vcat
    [ text "applying section" <+> prettyTCM m2
    , nest 2 $ text "ptel =" <+> prettyTCM ptel
    , nest 2 $ text "tel  =" <+> prettyTCM tel
    , nest 2 $ text "tel' =" <+> prettyTCM tel'
    , nest 2 $ text "tel''=" <+> prettyTCM tel''
    , nest 2 $ text "eta  =" <+> prettyTCM etaTel
    ]
  (ts, cs)  <- checkArguments_ DontExpandLast (getRange i) args tel''
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
