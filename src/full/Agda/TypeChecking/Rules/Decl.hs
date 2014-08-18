{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}

module Agda.TypeChecking.Rules.Decl where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State (modify)

import qualified Data.Foldable as Fold
import Data.Maybe
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Sequence ((|>))

import Agda.Compiler.HaskellTypes

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Generate

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Translation.InternalToAbstract

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Benchmark (billTop, reimburseTop)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.Data    ( checkDataDef )
import Agda.TypeChecking.Rules.Record  ( checkRecDef )
import Agda.TypeChecking.Rules.Def     ( checkFunDef )
import Agda.TypeChecking.Rules.Builtin ( bindBuiltin )

import Agda.Termination.TermCheck

import Agda.Utils.Size
import Agda.Utils.Maybe
import Agda.Utils.Monad
import qualified Agda.Utils.HashMap as HMap

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
checkDecl d = traceCall (SetRange (getRange d)) $ do
    reportSDoc "tc.decl" 10 $ vcat
      [ text "checking declaration"
      , prettyA d
      ]

    -- Issue 418 fix: freeze metas before checking an abstract thing
    when isAbstract freezeMetas

    let -- What kind of final checks/computations should be performed
        -- if we're not inside a mutual block?
        none        m = m >> return Nothing
        meta        m = m >> return (Just (return []))
        mutual i ds m = m >>= return . Just . mutualChecks i ds
        impossible  m = m >> return __IMPOSSIBLE__
                       -- We're definitely inside a mutual block.

    let mi = Info.MutualInfo TerminationCheck noRange

    finalChecks <- case d of
      A.Axiom{}                -> meta $ checkTypeSignature d
      A.Field{}                -> typeError FieldOutsideRecord
      A.Primitive i x e        -> meta $ checkPrimitive i x e
      A.Mutual i ds            -> mutual i ds $ checkMutual i ds
      A.Section i x tel ds     -> meta $ checkSection i x tel ds
      A.Apply i x modapp rd rm -> meta $ checkSectionApplication i x modapp rd rm
      A.Import i x             -> none $ checkImport i x
      A.Pragma i p             -> none $ checkPragma i p
      A.ScopedDecl scope ds    -> none $ setScope scope >> checkDecls ds
      A.FunDef i x delayed cs  -> impossible $ check x i $ checkFunDef delayed i x cs
      A.DataDef i x ps cs      -> impossible $ check x i $ checkDataDef i x ps cs
      A.RecDef i x ind c ps tel cs -> mutual mi [d] $ check x i $ do
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
      A.Open{}                 -> none $ return ()
      A.PatternSynDef{}        -> none $ return ()
                                  -- Open and PatternSynDef are just artifacts
                                  -- from the concrete syntax, retained for
                                  -- highlighting purposes.
      A.UnquoteDecl mi i x e   -> checkUnquoteDecl mi i x e

    unlessM (isJust . envMutualBlock <$> ask) $ do
      -- The termination errors are not returned, but used for highlighting.
      termErrs <- caseMaybe finalChecks (return []) $ \ theMutualChecks -> do
        solveSizeConstraints
        wakeupConstraints_   -- solve emptyness constraints
        freezeMetas

        theMutualChecks

      -- Syntax highlighting.
      let highlight d = generateAndPrintSyntaxInfo d (Full termErrs)
      reimburseTop Bench.Typing $ billTop Bench.Highlighting $ case d of
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
        A.PatternSynDef{}        -> highlight d
        A.UnquoteDecl{}          -> highlight d
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

    -- check record or data type signature
    checkSig i x ps t = checkTypeSignature $
      A.Axiom A.NoFunSig i defaultArgInfo x (A.Pi (Info.ExprRange (fuseRange ps t)) ps t)

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
    mutualChecks i ds names = do
      -- Andreas, 2014-04-11: instantiate metas in definition types
      mapM_ instantiateDefinitionType $ Set.toList names
      -- Andreas, 2013-02-27: check termination before injectivity,
      -- to avoid making the injectivity checker loop.
      termErrs <- case d of
        A.UnquoteDecl{} -> checkTermination_ $ A.Mutual i ds
        _               -> checkTermination_ d
      checkPositivity_         names
      checkCoinductiveRecords  ds
      -- Andreas, 2012-09-11:  Injectivity check stores clauses
      -- whose 'Relevance' is affected by polarity computation,
      -- so do it here.
      checkInjectivity_        names
      checkProjectionLikeness_ names
      return termErrs

    checkUnquoteDecl mi i x e = do
      reportSDoc "tc.unquote.decl" 20 $ text "Checking unquoteDecl" <+> prettyTCM x
      fundef <- primAgdaFunDef
      v      <- checkExpr e $ El (mkType 0) fundef
      reportSDoc "tc.unquote.decl" 20 $ text "unquoteDecl: Checked term"
      UnQFun a cs <- unquote v
      reportSDoc "tc.unquote.decl" 20 $
        vcat $ text "unquoteDecl: Unquoted term"
             : [ nest 2 $ text (show c) | c <- cs ]
      -- Add x to signature, otherwise reification gets unhappy.
      addConstant x $ defaultDefn defaultArgInfo x a emptyFunction
      a <- reifyUnquoted a
      reportSDoc "tc.unquote.decl" 10 $
        vcat [ text "unquoteDecl" <+> prettyTCM x <+> text "-->"
             , prettyTCM x <+> text ":" <+> prettyA a ]
      cs <- mapM (reifyUnquoted . QNamed x) cs
      reportSDoc "tc.unquote.decl" 10 $ vcat $ map prettyA cs
      let ds = [ A.Axiom A.FunSig i defaultArgInfo x a   -- TODO other than defaultArg
               , A.FunDef i x NotDelayed cs ]
      xs <- checkMutual mi ds
      return $ Just $ mutualChecks mi ds xs

-- | Instantiate all metas in 'Definition' associated to 'QName'. --   Makes sense after freezing metas.
--   Some checks, like free variable analysis, are not in 'TCM', --   so they will be more precise (see issue 1099) after meta instantiation.
-- --   Precondition: name has been added to signature already.
instantiateDefinitionType :: QName -> TCM ()
instantiateDefinitionType q = do
  reportSLn "tc.decl.inst" 20 $ "instantiating type of " ++ show q
  sig <- getSignature
  let t = defType $ fromMaybe __IMPOSSIBLE__ $ lookupDefinition q sig
  t <- instantiateFull t
  modifySignature $ updateDefinition q $ \ def -> def { defType = t }

-- Andreas, 2014-04-11
-- UNUSED, costs a couple of sec on the std-lib
-- -- | Instantiate all metas in 'Definition' associated to 'QName'.
-- --   Makes sense after freezing metas.
-- --   Some checks, like free variable analysis, are not in 'TCM',
-- --   so they will be more precise (see issue 1099) after meta instantiation.
-- --
-- --   Precondition: name has been added to signature already.
-- instantiateDefinition :: QName -> TCM ()
-- instantiateDefinition q = do
--   reportSLn "tc.decl.inst" 20 $ "instantiating " ++ show q
--   sig <- getSignature
--   let def = fromMaybe __IMPOSSIBLE__ $ lookupDefinition q sig
--   def <- instantiateFull def
--   modifySignature $ updateDefinition q $ const def


-- | Termination check a declaration and return a list of termination errors.
checkTermination_ :: A.Declaration -> TCM [TerminationError]
checkTermination_ d = reimburseTop Bench.Typing $ billTop Bench.Termination $ do
  reportSLn "tc.decl" 20 $ "checkDecl: checking termination..."
  ifNotM (optTerminationCheck <$> pragmaOptions) (return []) $ {- else -} do
    case d of
      -- Record module definitions should not be termination-checked twice.
      A.RecDef {} -> return []
      _ -> disableDestructiveUpdate $ do
        termErrs <- {- nubList <$> -} termDecl d
        modify $ \st ->
          st { stTermErrs = Fold.foldl' (|>) (stTermErrs st) termErrs }
        return termErrs

-- | Check a set of mutual names for positivity.
checkPositivity_ :: Set QName -> TCM ()
checkPositivity_ names = reimburseTop Bench.Typing $ billTop Bench.Positivity $ do
  -- Positivity checking.
  reportSLn "tc.decl" 20 $ "checkDecl: checking positivity..."
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
  mapM_ computePolarity =<< do mapMaybeM relevant $ Set.toList names

-- | Check that all coinductive records are actually recursive.
--   (Otherwise, one can implement invalid recursion schemes just like
--   for the old coinduction.)
checkCoinductiveRecords :: [A.Declaration] -> TCM ()
checkCoinductiveRecords ds = forM_ ds $ \ d -> case d of
  A.RecDef _ q (Just (Ranged r CoInductive)) _ _ _ _ -> traceCall (SetRange r) $ do
    unlessM (isRecursiveRecord q) $ typeError $ GenericError $
      "Only recursive records can be coinductive"
  _ -> return ()

-- | Check a set of mutual names for constructor-headedness.
checkInjectivity_ :: Set QName -> TCM ()
checkInjectivity_ names = reimburseTop Bench.Typing $ billTop Bench.Injectivity $ do
  reportSLn "tc.decl" 20 $ "checkDecl: checking injectivity..."

  -- OLD CODE, REFACTORED using for-loop
  -- let checkInj (q, def@Defn{ theDef = d@Function{ funClauses = cs, funTerminates = Just True }}) = do
  --       inv <- checkInjectivity q cs
  --       modifySignature $ updateDefinition q $ const $
  --         def { theDef = d { funInv = inv }}
  --     checkInj _ = return ()
  -- namesDefs <- mapM (\ q -> (q,) <$> getConstInfo q) $ Set.toList names
  -- mapM_ checkInj namesDefs

  Fold.forM_ names $ \ q -> do
    def <- getConstInfo q
    case theDef def of
      d@Function{ funClauses = cs, funTerminates = Just True } -> do
        inv <- checkInjectivity q cs
        modifySignature $ updateDefinition q $ const $
          def { theDef = d { funInv = inv }}
      _ -> return ()

-- | Check a set of mutual names for projection likeness.
checkProjectionLikeness_ :: Set QName -> TCM ()
checkProjectionLikeness_ names = reimburseTop Bench.Typing $ billTop Bench.ProjectionLikeness $ do
      -- Non-mutual definitions can be considered for
      -- projection likeness
      reportSLn "tc.decl" 20 $ "checkDecl: checking projection-likeness..."
      case Set.toList names of
        [d] -> do
          def <- getConstInfo d
          case theDef def of
            Function{} -> makeProjection (defName def)
            _          -> return ()
        _ -> return ()

-- | Type check an axiom.
checkAxiom :: A.Axiom -> Info.DefInfo -> A.ArgInfo -> QName -> A.Expr -> TCM ()
checkAxiom funSig i info0 x e = do
  -- Andreas, 2012-04-18  if we are in irrelevant context, axioms is irrelevant
  -- even if not declared as such (Issue 610).
  rel <- max (getRelevance info0) <$> asks envRelevance
  let info = setRelevance rel $ convColor info0
  -- rel <- ifM ((Irrelevant ==) <$> asks envRelevance) (return Irrelevant) (return rel0)
  t <- isType_ e
  reportSDoc "tc.decl.ax" 10 $ sep
    [ text $ "checked type signature"
    , nest 2 $ prettyTCM rel <> prettyTCM x <+> text ":" <+> prettyTCM t
    ]
  -- Not safe. See Issue 330
  -- t <- addForcingAnnotations t
  addConstant x $
    defaultDefn info x t $
      case funSig of
        A.FunSig   -> emptyFunction
        A.NoFunSig -> Axiom    -- NB: used also for data and record type sigs

  -- Add the definition to the instance table, if needed
  when (Info.defInstance i == InstanceDef) $ do
    addTypedInstance x t

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
    addConstant x $
      defaultDefn defaultArgInfo x t $
        Primitive (Info.defAbstract i) s [] Nothing
    where
	nameString (Name _ x _ _) = show x


-- | Check a pragma.
checkPragma :: Range -> A.Pragma -> TCM ()
checkPragma r p =
    traceCall (CheckPragma r p) $ case p of
	A.BuiltinPragma x e -> bindBuiltin x e
	A.RewritePragma q   -> addRewriteRule q
        A.CompiledTypePragma x hs -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> addHaskellType x hs
            _       -> typeError $ GenericError
                        "COMPILED_TYPE directive only works on postulates"
        A.CompiledDataPragma x hs hcs -> do
          def <- getConstInfo x
          -- Check that the pragma appears in the same module
          -- as the datatype.
          do m <- currentModule
             let m' = qnameModule $ defName def
             unless (m == m') $ typeError $ GenericError $
              "COMPILED_DATA directives must appear in the same module " ++
              "as their corresponding datatype definition,"
          let addCompiledData cs = do
                addHaskellType x hs
                let computeHaskellType c = do
                      def <- getConstInfo c
                      let Constructor{ conPars = np } = theDef def
                          underPars 0 a = haskellType a
                          underPars n a = do
                            a <- reduce a
                            case unEl a of
                              Pi a (NoAbs _ b) -> underPars (n - 1) b
                              Pi a b  -> underAbstraction a b $ \b -> hsForall <$> getHsVar 0 <*> underPars (n - 1) b
                              _       -> __IMPOSSIBLE__
                      ty <- underPars np $ defType def
                      reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show c ++ ": " ++ ty
                      return ty
                hts <- mapM computeHaskellType cs
                sequence_ $ zipWith3 addHaskellCode cs hts hcs
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
              | otherwise -> addCompiledData cs
            Record{recConHead = ch}
              | length hcs == 1 -> addCompiledData [conName ch]
              | otherwise -> do
                  err <- fsep $ [prettyTCM x] ++ pwords ("has 1 constructor, but " ++
                                show (length hcs) ++ " Haskell constructors are given [" ++ unwords hcs ++ "]")
                  typeError $ GenericError $ show err
            _ -> typeError $ GenericError "COMPILED_DATA on non datatype"
        A.CompiledPragma x hs -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> do
              ty <- haskellType $ defType def
              reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show x ++ ": " ++ ty
              addHaskellCode x ty hs
            _   -> typeError $ GenericError "COMPILED directive only works on postulates"
        A.CompiledExportPragma x hs -> do
          def <- getConstInfo x
          let correct = case theDef def of
                            -- Axiom{} -> do
                            --   ty <- haskellType $ defType def
                            --   reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show x ++ ": " ++ ty
                            --   addHaskellCode x ty hs
                            Function{} -> True
                            Constructor{} -> False
                            _   -> False
          if not correct
            then typeError $ GenericError "COMPILED_EXPORT directive only works on functions"
            else do
          ty <- haskellType $ defType def
          addHaskellExport x ty hs
        A.CompiledEpicPragma x ep -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> do
              --ty <- haskellType $ defType def
              --reportSLn "tc.pragma.compile" 10 $ "Haskell type for " ++ show x ++ ": " ++ ty
              addEpicCode x ep
            _   -> typeError $ GenericError "COMPILED_EPIC directive only works on postulates"
        A.CompiledJSPragma x ep ->
          addJSCode x ep
        A.StaticPragma x -> do
          def <- getConstInfo x
          case theDef def of
            Function{} -> markStatic x
            _          -> typeError $ GenericError "STATIC directive only works on functions"
	A.OptionsPragma{} -> typeError $ GenericError $ "OPTIONS pragma only allowed at beginning of file, before top module declaration"
        A.EtaPragma r -> do
          unlessM (isJust <$> isRecord r) $
            typeError $ GenericError $ "ETA pragma is only applicable to records"
          modifySignature $ updateDefinition r $ updateTheDef $ setEta
          where
            setEta d = case d of
              Record{} -> d { recEtaEquality = True }
              _        -> __IMPOSSIBLE__

-- | Type check a bunch of mutual inductive recursive definitions.
--
-- All definitions which have so far been assigned to the given mutual
-- block are returned.
checkMutual :: Info.MutualInfo -> [A.Declaration] -> TCM (Set QName)
checkMutual i ds = inMutualBlock $ do

  verboseS "tc.decl.mutual" 20 $ do
    blockId <- currentOrFreshMutualBlock
    reportSDoc "tc.decl.mutual" 20 $ vcat $
      (text "Checking mutual block" <+> text (show blockId) <> text ":") :
      map (nest 2 . prettyA) ds

  mapM_ checkDecl ds

  lookupMutualBlock =<< currentOrFreshMutualBlock

-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.ScopedDecl scope ds) = do
  setScope scope
  mapM_ checkTypeSignature ds
checkTypeSignature (A.Axiom funSig i info x e) =
    case Info.defAccess i of
	PublicAccess  -> inConcreteMode $ checkAxiom funSig i info x e
	PrivateAccess -> inAbstractMode $ checkAxiom funSig i info x e
        OnlyQualified -> __IMPOSSIBLE__
checkTypeSignature _ = __IMPOSSIBLE__	-- type signatures are always axioms

-- | Type check a module.
checkSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkSection i x tel ds =
  checkTelescope_ tel $ \tel' -> do
    addSection x (size tel')
    verboseS "tc.section.check" 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyAs tel
      dtel' <- prettyTCM =<< lookupSection x
      reportSLn "tc.section.check" 10 $ "checking section " ++ show dx ++ " " ++ show dtel
      reportSLn "tc.section.check" 10 $ "    actual tele: " ++ show dtel'
    withCurrentModule x $ checkDecls ds

-- | Helper for 'checkSectionApplication'.
--
--   Matches the arguments of the module application with the
--   module parameters.
--
--   Returns the remaining module parameters as an open telescope.
--   Warning: the returned telescope is /not/ the final result,
--   an actual instantiation of the parameters does not occur.
checkModuleArity
  :: ModuleName           -- ^ Name of applied module.
  -> Telescope            -- ^ The module parameters.
  -> [I.NamedArg A.Expr]  -- ^ The arguments this module is applied to.
  -> TCM Telescope        -- ^ The remaining module parameters (has free de Bruijn indices!).
checkModuleArity m tel args = check tel args
  where
    bad = typeError $ ModuleArityMismatch m tel args

    check tel []             = return tel
    check EmptyTel (_:_)     = bad
    check (ExtendTel (Dom info _) btel) args0@(Arg info' (Named rname _) : args) =
      let name = fmap rangedThing rname
          y    = absName btel
          tel  = absBody btel in
      case (argInfoHiding info, argInfoHiding info', name) of
        (Instance, NotHidden, _) -> check tel args0
        (Instance, Hidden, _)    -> check tel args0
        (Instance, Instance, Nothing) -> check tel args
        (Instance, Instance, Just x)
          | x == y                -> check tel args
          | otherwise             -> check tel args0
        (Hidden, NotHidden, _)    -> check tel args0
        (Hidden, Instance, _)     -> check tel args0
        (Hidden, Hidden, Nothing) -> check tel args
        (Hidden, Hidden, Just x)
          | x == y                -> check tel args
          | otherwise             -> check tel args0
        (NotHidden, NotHidden, _) -> check tel args
        (NotHidden, Hidden, _)    -> bad
        (NotHidden, Instance, _)    -> bad

-- | Check an application of a section (top-level function, includes @'traceCall'@).
checkSectionApplication
  :: Info.ModuleInfo
  -> ModuleName                 -- ^ Name @m1@ of module defined by the module macro.
  -> A.ModuleApplication        -- ^ The module macro @λ tel → m2 args@.
  -> Map QName QName            -- ^ Imported names (given as renaming).
  -> Map ModuleName ModuleName  -- ^ Imported modules (given as renaming).
  -> TCM ()
checkSectionApplication i m1 modapp rd rm =
  traceCall (CheckSectionApplication (getRange i) m1 modapp) $
  checkSectionApplication' i m1 modapp rd rm

-- | Check an application of a section.
checkSectionApplication'
  :: Info.ModuleInfo
  -> ModuleName                 -- ^ Name @m1@ of module defined by the module macro.
  -> A.ModuleApplication        -- ^ The module macro @λ tel → m2 args@.
  -> Map QName QName            -- ^ Imported names (given as renaming).
  -> Map ModuleName ModuleName  -- ^ Imported modules (given as renaming).
  -> TCM ()
checkSectionApplication' i m1 (A.SectionApp ptel m2 args) rd rm =
  -- Type-check the LHS (ptel) of the module macro.
  checkTelescope_ ptel $ \ ptel -> do
  -- We are now in the context @ptel@.
  -- Get the correct parameter telescope of @m2@.
  tel <- lookupSection m2
  vs  <- freeVarsToApply $ mnameToQName m2
  let tel'  = apply tel vs
      args' = convColor args
  -- Compute the remaining parameter telescope after stripping of
  -- the initial parameters that are determined by the @args@.
  -- Warning: @etaTel@ is not well-formed in @ptel@, since
  -- the actual application has not happened.
  etaTel <- checkModuleArity m2 tel' args'
  -- Take the module parameters that will be instantiated by @args@.
  let tel'' = telFromList $ take (size tel' - size etaTel) $ telToList tel'
  reportSDoc "tc.section.apply" 15 $ vcat
    [ text "applying section" <+> prettyTCM m2
    , nest 2 $ text "args =" <+> sep (map prettyA args)
    , nest 2 $ text "ptel =" <+> escapeContext (size ptel) (prettyTCM ptel)
    , nest 2 $ text "tel  =" <+> prettyTCM tel
    , nest 2 $ text "tel' =" <+> prettyTCM tel'
    , nest 2 $ text "tel''=" <+> prettyTCM tel''
    , nest 2 $ text "eta  =" <+> escapeContext (size ptel) (addContext tel'' $ prettyTCM etaTel)
    ]
  -- Now, type check arguments.
  ts <- noConstraints $ checkArguments_ DontExpandLast (getRange i) args' tel''
  -- Perform the application of the module parameters.
  let aTel = tel' `apply` ts
  reportSDoc "tc.section.apply" 15 $ vcat
    [ nest 2 $ text "aTel =" <+> prettyTCM aTel
    ]
  -- Andreas, 2014-04-06, Issue 1094:
  -- Add the section with well-formed telescope.
  addCtxTel aTel $ addSection m1 (size ptel + size aTel)

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
  vs   <- freeVarsToApply name
  let tel = tel' `apply` vs
      args = teleArgs tel

      telInst :: Telescope
      telInst = instFinal tel

      -- Locate last (rightmost) parameter and make it @Instance@.
      instFinal :: Telescope -> Telescope
      -- Telescopes do not have @NoAbs@.
      instFinal (ExtendTel _ NoAbs{}) = __IMPOSSIBLE__
      -- Found last parameter: switch it to @Instance@.
      instFinal (ExtendTel (Dom info t) (Abs n EmptyTel)) =
                 ExtendTel (Dom ifo' t) (Abs n EmptyTel)
        where ifo' = setHiding Instance info
      -- Otherwise, keep searchinf for last parameter:
      instFinal (ExtendTel arg (Abs n tel)) =
                 ExtendTel arg (Abs n (instFinal tel))
      -- Before instFinal is invoked, we have checked that the @tel@ is not empty.
      instFinal EmptyTel = __IMPOSSIBLE__

  reportSDoc "tc.section.apply" 20 $ vcat
    [ sep [ text "applySection", prettyTCM name, text "{{...}}" ]
    , nest 2 $ text "x       =" <+> prettyTCM x
    , nest 2 $ text "name    =" <+> prettyTCM name
    , nest 2 $ text "tel     =" <+> prettyTCM tel
    , nest 2 $ text "telInst =" <+> prettyTCM telInst
    , nest 2 $ text "vs      =" <+> sep (map prettyTCM vs)
    -- , nest 2 $ text "args    =" <+> sep (map prettyTCM args)
    ]
  reportSDoc "tc.section.apply" 60 $ vcat
    [ nest 2 $ text "vs      =" <+> text (show vs)
    -- , nest 2 $ text "args    =" <+> text (show args)
    ]
  when (tel == EmptyTel) $
    typeError $ GenericError $ show name ++ " is not a parameterised section"

  addCtxTel telInst $ do
    vs <- freeVarsToApply name
    reportSDoc "tc.section.apply" 20 $ vcat
      [ nest 2 $ text "vs      =" <+> sep (map prettyTCM vs)
      , nest 2 $ text "args    =" <+> sep (map (parens . prettyTCM) args)
      ]
    reportSDoc "tc.section.apply" 60 $ vcat
      [ nest 2 $ text "vs      =" <+> text (show vs)
      , nest 2 $ text "args    =" <+> text (show args)
      ]
    applySection m1 telInst x (vs ++ args) rd rm

-- | Type check an import declaration. Actually doesn't do anything, since all
--   the work is done when scope checking.
checkImport :: Info.ModuleInfo -> ModuleName -> TCM ()
checkImport i x = return ()
