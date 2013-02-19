{-# LANGUAGE CPP, TupleSections #-}

module Agda.TypeChecking.Rules.Decl where

import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.State (modify)

import qualified Data.Foldable as Fold
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Sequence ((|>))

import Agda.Syntax.Abstract (AnyAbstract(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Mutual
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Forcing
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.InstanceArguments (solveIrrelevantMetas)

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.Data    ( checkDataDef )
import Agda.TypeChecking.Rules.Record  ( checkRecDef )
import Agda.TypeChecking.Rules.Def     ( checkFunDef )
import Agda.TypeChecking.Rules.Builtin ( bindBuiltin )

import Agda.Compiler.HaskellTypes

import Agda.Utils.Size
import Agda.Utils.Monad
import qualified Agda.Utils.HashMap as HMap
-- import Agda.Utils.NubList -- reverted

import Agda.Interaction.Highlighting.Generate

import Agda.Termination.TermCheck
import Agda.Interaction.Options

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
    reportSDoc "tc.decl" 10 $ vcat
      [ text "checking declaration"
      , prettyA d
      ]

    -- Issue 418 fix: freeze metas before checking an abstract thing
    when isAbstract freezeMetas

    let -- What kind of final checks/computations should be performed
        -- if we're not inside a mutual block?
        none       m = m >> return Nothing
        meta       m = m >> return (Just (return []))
        mutual     m = m >>= return . Just . mutualChecks
        impossible m = m >> return __IMPOSSIBLE__
                       -- We're definitely inside a mutual block.

    topLevelKind <- case d of
      A.Axiom{}                -> meta $ checkTypeSignature d
      A.Field{}                -> typeError FieldOutsideRecord
      A.Primitive i x e        -> meta $ checkPrimitive i x e
      A.Mutual i ds            -> mutual $ checkMutual i ds
      A.Section i x tel ds     -> meta $ checkSection i x tel ds
      A.Apply i x modapp rd rm -> meta $ checkSectionApplication i x modapp rd rm
      A.Import i x             -> none $ checkImport i x
      A.Pragma i p             -> none $ checkPragma i p
      A.ScopedDecl scope ds    -> none $ setScope scope >> checkDecls ds
      A.FunDef i x delayed cs  -> impossible $ check x i $ checkFunDef delayed i x cs
      A.DataDef i x ps cs      -> impossible $ check x i $ checkDataDef i x ps cs
      A.RecDef i x ind c ps tel cs -> mutual $ check x i $ do
                                    checkRecDef i x ind c ps tel cs
                                    return (Set.singleton x)
      A.DataSig i x ps t       -> impossible $ checkSig i x ps t
      A.RecSig i x ps t        -> none $ checkSig i x ps t
                                  -- A record signature is always followed by a
                                  -- record definition. Metas should not be
                                  -- frozen until after the definition has been
                                  -- checked. NOTE: Metas are not frozen
                                  -- immediately after the last field. Perhaps
                                  -- they should be (unless we're in a mutual
                                  -- block).
      A.Open _ _               -> none $ return ()
                                  -- Open is just an artifact from the concrete
                                  -- syntax, retained for highlighting purposes.

    unlessM (isJust . envMutualBlock <$> ask) $ do
      termErrs <- case topLevelKind of
        Nothing           -> return []
        Just mutualChecks -> do

          solveSizeConstraints
          solveIrrelevantMetas
          wakeupConstraints_   -- solve emptyness constraints
          freezeMetas

          mutualChecks

      -- Syntax highlighting.
      let highlight d = generateAndPrintSyntaxInfo d (Full termErrs)
      case d of
        A.Axiom{}                -> highlight d
        A.Field{}                -> __IMPOSSIBLE__
        A.Primitive{}            -> highlight d
        A.Mutual{}               -> highlight d
        A.Apply{}                -> highlight d
        A.Import{}               -> highlight d
        A.Pragma{}               -> highlight d
        A.ScopedDecl{}           -> return ()
        A.FunDef{}               -> __IMPOSSIBLE__
        A.DataDef{}              -> __IMPOSSIBLE__
        A.DataSig{}              -> __IMPOSSIBLE__
        A.Open{}                 -> highlight d
        A.Section i x tel _      -> highlight (A.Section i x tel [])
          -- Each block in the section has already been highlighted,
          -- all that remains is the module declaration.
        A.RecSig{}               -> highlight d
        A.RecDef i x ind c ps tel cs ->
          highlight (A.RecDef i x ind c [] tel (fields cs))
          -- The telescope and all record module declarations except
          -- for the fields have already been highlighted.
          where
          fields (A.ScopedDecl _ ds1 : ds2) = fields ds1 ++ fields ds2
          fields (d@A.Field{}        : ds)  = d : fields ds
          fields (_                  : ds)  = fields ds
          fields []                         = []

    where
    unScope (A.ScopedDecl scope ds) = setScope scope >> unScope d
    unScope d = return d

    checkSig i x ps t = checkTypeSignature $
      A.Axiom i defaultArgInfo x (A.Pi (Info.ExprRange (fuseRange ps t)) ps t)

    check x i m = do
      reportSDoc "tc.decl" 5 $ text "Checking" <+> prettyTCM x <> text "."
      r <- abstract (Info.defAbstract i) m
      reportSDoc "tc.decl" 5 $ text "Checked" <+> prettyTCM x <> text "."
      return r

    isAbstract = fmap Info.defAbstract (A.getDefInfo d) == Just AbstractDef

    -- Concrete definitions cannot use information about abstract things.
    abstract ConcreteDef = inConcreteMode
    abstract AbstractDef = inAbstractMode

    -- Some checks that should be run at the end of a mutual
    -- block (or non-mutual record declaration). The set names
    -- contains the names defined in the mutual block.
    mutualChecks names = do

      checkStrictlyPositive names

      -- Andreas, 2012-02-13: Polarity computation uses info from
      -- positivity check, so it needs happen after positivity
      -- check.
      let -- | Do we need to compute polarity information for the
          -- definition corresponding to the given name?
          relevant q = do
            def <- theDef <$> getConstInfo q
            return $ case def of
              Function{}    -> Just q
              Datatype{}    -> Just q
              Record{}      -> Just q
              Axiom{}       -> Nothing
              Constructor{} -> Nothing
              Primitive{}   -> Nothing
      mapM_ computePolarity =<<
        (catMaybes <$> mapM relevant (Set.toList names))

      -- Andreas, 2012-09-11:  Injectivity check stores clauses
      -- whose 'Relevance' is affected by polarity computation,
      -- so do it here.

      let checkInj (q, def@Defn{ theDef = d@Function{ funClauses = cs }}) = do
            inv <- checkInjectivity q cs
            modifySignature $ updateDefinition q $ const $
              def { theDef = d { funInv = inv }}
          checkInj _ = return ()

      namesDefs <- mapM (\ q -> (q,) <$> getConstInfo q) $ Set.toList names
      reportSLn "tc.inj.decl" 20 $ "checkDecl: checking injectivity..."
      mapM_ checkInj namesDefs

      -- Non-mutual definitions can be considered for
      -- projection likeness
      case Set.toList names of
        [d] -> do
          def <- getConstInfo d
          case theDef def of
            Function{} -> makeProjection (defName def)
            _          -> return ()
        _ -> return ()

      -- Termination checking.
      termErrs <-
        ifM (optTerminationCheck <$> pragmaOptions)
          (disableDestructiveUpdate $ case d of
             A.RecDef {} -> return []
                            -- Record module definitions should not be
                            -- termination-checked twice.
             _           -> do
               termErrs <- {- nubList <$> -} termDecl d
               modify $ \st ->
                 st { stTermErrs = Fold.foldl' (|>) (stTermErrs st) termErrs }
               return termErrs)
          (return [])

      return termErrs

-- | Type check an axiom.
checkAxiom :: Info.DefInfo -> A.ArgInfo -> QName -> A.Expr -> TCM ()
checkAxiom i info0 x e = do
  -- Andreas, 2012-04-18  if we are in irrelevant context, axioms is irrelevant
  -- even if not declared as such (Issue 610).
  rel <- max (argInfoRelevance info0) <$> asks envRelevance
  let info = setArgInfoRelevance rel $ convArgInfo info0
  -- rel <- ifM ((Irrelevant ==) <$> asks envRelevance) (return Irrelevant) (return rel0)
  t <- isType_ e
  reportSDoc "tc.decl.ax" 10 $ sep
    [ text $ "checked type signature"
    , nest 2 $ prettyTCM rel <> prettyTCM x <+> text ":" <+> prettyTCM t
    ]
  -- Not safe. See Issue 330
  -- t <- addForcingAnnotations t
  addConstant x (Defn info x t [] [] (defaultDisplayForm x) 0 noCompiledRep Axiom)

  -- for top-level axioms (postulates) try to solve irrelevant metas
  -- when postulate $
  maybe solveIrrelevantMetas (const $ return ()) =<< asks envMutualBlock

  traceCall (IsType_ e) $ solveSizeConstraints  -- need Range for error message

  -- Andreas, 2011-05-31, that freezing below is probably wrong:
  -- when (Info.defAbstract i == AbstractDef) $ freezeMetas

-- | Type check a primitive function declaration.
checkPrimitive :: Info.DefInfo -> QName -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) (qnameName x) e) $ do  -- TODO!! (qnameName)
    (_, PrimImpl t' pf) <- lookupPrimitiveFunctionQ x
    t <- isType_ e
    noConstraints $ equalType t t'
    let s  = show $ nameConcrete $ qnameName x
    bindPrimitive s pf
    addConstant x (Defn defaultArgInfo x t [] [] (defaultDisplayForm x) 0 noCompiledRep $
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
            eta sig = sig { sigDefinitions = HMap.adjust setEta r defs }
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
checkMutual :: Info.MutualInfo -> [A.Declaration] -> TCM (Set QName)
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
checkTypeSignature (A.Axiom i info x e) =
    case Info.defAccess i of
	PublicAccess  -> inConcreteMode $ checkAxiom i info x e
	PrivateAccess -> inAbstractMode $ checkAxiom i info x e
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

checkModuleArity :: ModuleName -> Telescope -> [I.NamedArg A.Expr] -> TCM Telescope
checkModuleArity m tel args = check tel args
  where
    bad = typeError $ ModuleArityMismatch m tel args

    check eta []             = return eta
    check EmptyTel (_:_)     = bad
    check (ExtendTel (Dom info _) btel) args0@(Arg info' (Named name _) : args) =
      let y   = absName btel
          tel = absBody btel in
      case (argInfoHiding info, argInfoHiding info', name) of
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
      args'= map convArg args
  etaTel <- checkModuleArity m2 tel' $ args'
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
  ts <- noConstraints $ checkArguments_ DontExpandLast (getRange i) args' tel''
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
      instFinal (ExtendTel (Dom info t) (Abs n EmptyTel)) =
          ExtendTel (Dom (setArgInfoHiding Instance info) t) (Abs n EmptyTel)
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
