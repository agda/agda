{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Decl where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Agda.Utils.IO.Locale as LocIO

import Agda.Syntax.Abstract (AnyAbstract(..))
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
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Forcing

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.Data    ( checkDataDef )
import Agda.TypeChecking.Rules.Record  ( checkRecDef )
import Agda.TypeChecking.Rules.Def     ( checkFunDef )
import Agda.TypeChecking.Rules.Builtin ( bindBuiltin )

import Agda.Compiler.HaskellTypes

import Agda.Utils.Size
import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Type check a sequence of declarations.
checkDecls :: [A.Declaration] -> TCM ()
checkDecls ds = do
  mapM_ checkDecl ds
  -- Andreas, 2011-05-30, unfreezing moved to Interaction/Imports
  -- whenM onTopLevel unfreezeMetas

-- | Type check a single declaration.
checkDecl :: A.Declaration -> TCM ()
checkDecl d = do
    -- Issue 418 fix: freeze metas before checking an abstract things
    when isAbstract freezeMetas
    case d of
	A.Axiom i rel x e        -> checkAxiom i rel x e
        A.Field{}                -> typeError FieldOutsideRecord
	A.Primitive i x e        -> checkPrimitive i x e
	A.Mutual i ds            -> topLevelChecks $ checkMutual i ds
	A.Section i x tel ds     -> checkSection i x tel ds
	A.Apply i x modapp rd rm -> checkSectionApplication i x modapp rd rm
	A.Import i x             -> checkImport i x
	A.Pragma i p             -> checkPragma i p
	A.ScopedDecl scope ds    -> setScope scope >> checkDecls ds
        A.FunDef i x cs          -> check x i $ checkFunDef NotDelayed i x cs
        A.DataDef i x ps cs      -> check x i $ checkDataDef i x ps cs
        A.RecDef i x c ps tel cs -> check x i $ topLevelChecks $ do
                                      checkRecDef i x c ps tel cs
                                      return (Set.singleton x)
        A.DataSig i x ps t       -> checkAxiom i Relevant x (A.Pi (Info.ExprRange (fuseRange ps t)) ps t)
        A.RecSig i x ps t        -> checkAxiom i Relevant x (A.Pi (Info.ExprRange (fuseRange ps t)) ps t)
        A.Open _ _               -> return ()
    where
        unScope (A.ScopedDecl scope ds) = setScope scope >> unScope d
        unScope d = return d

        check x i m = do
          reportSDoc "tc.decl" 5 $ text "Checking" <+> prettyTCM x <> text "."
          r <- abstract (Info.defAbstract i) m
          reportSDoc "tc.decl" 5 $ text "Checked" <+> prettyTCM x <> text "."
          return r

        isAbstract = fmap Info.defAbstract (A.getDefInfo d) == Just AbstractDef

        -- Concrete definitions cannot use information about abstract things.
        abstract ConcreteDef = inConcreteMode
        abstract AbstractDef = inAbstractMode
	    -- open is just an artifact from the concrete syntax
            -- retained for highlighting purposes

        -- Run priorChecks, then do some final checks/computations if
        -- we are not inside a mutual block; priorChecks should return
        -- the names of all definitions in a mutual block (or the name
        -- of a single non-mutual definition).
        topLevelChecks priorChecks =
          ifM (isJust . envMutualBlock <$> ask)
            (priorChecks >> return ())
            (do qs <- priorChecks

                checkStrictlyPositive qs

                -- Andreas, 2012-02-13: Polarity computation uses info from
                -- positivity check, so it needs happen after positivity
                -- check.
                mapM_ computePolarity =<<
                  (map fst . filter snd <$> mapM relevant (Set.toList qs))

                -- Non-mutual definitions can be considered for
                -- projection likeness
                case Set.toList qs of
                  [d] -> do
                    def <- getConstInfo d
                    case theDef def of
                      Function{} -> makeProjection (defName def)
                      _          -> return ()
                  _ -> return ()

                solveSizeConstraints
                freezeMetas
            )
          where
          -- | Do we need to compute polarity information for the definition
          -- corresponding to the given name?
          relevant q = do
            def <- theDef <$> getConstInfo q
            return (q, case def of
              Function{}    -> True
              Datatype{}    -> True
              Record{}      -> True
              Axiom{}       -> False
              Constructor{} -> False
              Primitive{}   -> False)

-- | Type check an axiom.
checkAxiom :: Info.DefInfo -> Relevance -> QName -> A.Expr -> TCM ()
checkAxiom i rel x e = do
  t <- isType_ e
  reportSDoc "tc.decl.ax" 10 $ sep
    [ text "checked axiom"
    , nest 2 $ prettyTCM rel <> prettyTCM x <+> text ":" <+> (prettyTCM =<< instantiateFull t)
    ]
  -- Not safe. See Issue 330
  -- t <- addForcingAnnotations t
  addConstant x (Defn rel x t (defaultDisplayForm x) 0 noCompiledRep Axiom)
  solveSizeConstraints
  -- Andreas, 2011-05-31, that freezing below is probably wrong:
  -- when (Info.defAbstract i == AbstractDef) $ freezeMetas

-- | Type check a primitive function declaration.
checkPrimitive :: Info.DefInfo -> QName -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) (qnameName x) e) $ do  -- TODO!! (qnameName)
    PrimImpl t' pf <- lookupPrimitiveFunction (nameString $ qnameName x)
    t <- isType_ e
    noConstraints $ equalType t t'
    let s  = show $ nameConcrete $ qnameName x
    bindPrimitive s $ pf { primFunName = x }
    addConstant x (Defn Relevant x t (defaultDisplayForm x) 0 noCompiledRep $
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
                              Pi a (NoAbs _ b) -> underPars (n - 1) b
                              Pi a b  -> underAbstraction a b $ underPars (n - 1)
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
        A.CompiledJSPragma x ep ->
          addJSCode x ep
        A.StaticPragma x -> do
            def <- getConstInfo x
            case theDef def of
                Function{} -> do
                    markStatic x
                _ -> typeError $ GenericError "STATIC directive only works on functions."
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
--
-- All definitions which have so far been assigned to the given mutual
-- block are returned.
checkMutual :: Info.DeclInfo -> [A.Declaration] -> TCM (Set QName)
checkMutual i ds = inMutualBlock $ do

  verboseS "tc.decl.mutual" 20 $ do
    blockId <- currentOrFreshMutualBlock
    reportSDoc "" 0 $ vcat $
      (text "Checking mutual block" <+> text (show blockId) <> text ":") :
      map (nest 2 . prettyA) ds

  mapM_ checkDecl ds

  lookupMutualBlock =<< currentOrFreshMutualBlock

-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.ScopedDecl scope ds) = do
  setScope scope
  mapM_ checkTypeSignature ds
checkTypeSignature (A.Axiom i rel x e) =
    case Info.defAccess i of
	PublicAccess  -> inConcreteMode $ checkAxiom i rel x e
	PrivateAccess -> inAbstractMode $ checkAxiom i rel x e
        OnlyQualified -> __IMPOSSIBLE__
checkTypeSignature _ = __IMPOSSIBLE__	-- type signatures are always axioms

-- | Type check a module.
checkSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkSection i x tel ds =
  checkTelescope_ tel $ \tel' -> do
    addSection x (size tel')
    verboseS "tc.section.check" 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection x
      reportSLn "" 0 $ "checking section " ++ show dx ++ " " ++ show dtel
      reportSLn "" 0 $ "    actual tele: " ++ show dtel'
    withCurrentModule x $ checkDecls ds

checkModuleArity :: ModuleName -> Telescope -> [NamedArg A.Expr] -> TCM Telescope
checkModuleArity m tel args = check tel args
  where
    bad = typeError $ ModuleArityMismatch m tel args

    check eta []             = return eta
    check EmptyTel (_:_)     = bad
    check (ExtendTel (Arg h _ _) btel) args0@(Arg h' _ (Named name _) : args) =
      let y   = absName btel
          tel = absBody btel in
      case (h, h', name) of
        (Instance, NotHidden, _) -> check tel args0
        (Instance, Hidden, _) -> bad
        (Instance, Instance, Nothing) -> check tel args
        (Instance, Instance, Just x)
          | x == y                -> check tel args
          | otherwise             -> check tel args0
        (Hidden, NotHidden, _)    -> check tel args0
        (Hidden, Instance, _)    -> bad
        (Hidden, Hidden, Nothing) -> check tel args
        (Hidden, Hidden, Just x)
          | x == y                -> check tel args
          | otherwise             -> check tel args0
        (NotHidden, NotHidden, _) -> check tel args
        (NotHidden, Hidden, _)    -> bad
        (NotHidden, Instance, _)    -> bad

-- | Check an application of a section.
checkSectionApplication ::
  Info.ModuleInfo -> ModuleName -> A.ModuleApplication ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
checkSectionApplication i m1 modapp rd rm =
  traceCall (CheckSectionApplication (getRange i) m1 modapp) $
  checkSectionApplication' i m1 modapp rd rm

checkSectionApplication' ::
  Info.ModuleInfo -> ModuleName -> A.ModuleApplication ->
  Map QName QName -> Map ModuleName ModuleName -> TCM ()
checkSectionApplication' i m1 (A.SectionApp ptel m2 args) rd rm =
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
  ts <- noConstraints $ checkArguments_ DontExpandLast (getRange i) args tel''
  reportSDoc "tc.section.apply" 20 $ vcat
    [ sep [ text "applySection", prettyTCM m1, text "=", prettyTCM m2, fsep $ map prettyTCM (vs ++ ts) ]
    , nest 2 $ text "  defs:" <+> text (show rd)
    , nest 2 $ text "  mods:" <+> text (show rm)
    ]
  args <- instantiateFull $ vs ++ ts
  applySection m1 ptel m2 args rd rm
checkSectionApplication' i m1 (A.RecordModuleIFS x) rd rm = do
  let name = mnameToQName x
  tel' <- lookupSection x
  vs <- freeVarsToApply name
  let tel = tel' `apply` vs
  case tel of
    EmptyTel -> typeError $ GenericError $ show name ++ " is not a parameterised section."
    _ -> return ()
  let telInst :: Telescope
      telInst = instFinal tel
      instFinal :: Telescope -> Telescope
      instFinal (ExtendTel _ NoAbs{}) = __IMPOSSIBLE__
      instFinal (ExtendTel (Arg h r t) (Abs n EmptyTel)) = ExtendTel (Arg Instance r t) (Abs n EmptyTel)
      instFinal (ExtendTel arg (Abs n tel)) = ExtendTel arg (Abs n (instFinal tel))
      instFinal EmptyTel = __IMPOSSIBLE__
      args = teleArgs tel
  reportSDoc "tc.section.apply" 20 $ vcat
    [ sep [ text "applySection", prettyTCM name, text "{{...}}" ]
    , nest 2 $ text "tel:" <+> prettyTCM tel
    , nest 2 $ text "telInst:" <+> prettyTCM telInst
    , nest 2 $ text "args:" <+> text (show args)
    ]

  addCtxTel telInst $ do
    vs <- freeVarsToApply name
    applySection m1 telInst x (vs ++ args) rd rm

-- | Type check an import declaration. Actually doesn't do anything, since all
--   the work is done when scope checking.
checkImport :: Info.ModuleInfo -> ModuleName -> TCM ()
checkImport i x = return ()
