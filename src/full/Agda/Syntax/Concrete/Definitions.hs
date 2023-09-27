{-# LANGUAGE GADTs              #-}

-- | Preprocess 'Agda.Syntax.Concrete.Declaration's, producing 'NiceDeclaration's.
--
--   * Attach fixity and syntax declarations to the definition they refer to.
--
--   * Distribute the following attributes to the individual definitions:
--       @abstract@,
--       @instance@,
--       @postulate@,
--       @primitive@,
--       @private@,
--       termination pragmas.
--
--   * Gather the function clauses belonging to one function definition.
--
--   * Expand ellipsis @...@ in function clauses following @with@.
--
--   * Infer mutual blocks.
--     A block starts when a lone signature is encountered, and ends when
--     all lone signatures have seen their definition.
--
--   * Handle interleaved mutual blocks.
--     In an `interleaved mutual' block we:
--     * leave the data and fun sigs in place
--     * classify signatures in `constructor' block based on their return type
--       and group them all as a data def at the position in the block where the
--       first constructor for the data sig in question occured
--     * classify fun clauses based on the declared function used and group them
--       all as a fundef at the position in the block where the first such fun
--       clause appeared
--
--   * Report basic well-formedness error,
--     when one of the above transformation fails.
--     When possible, errors should be deferred to the scope checking phase
--     (ConcreteToAbstract), where we are in the TCM and can produce more
--     informative error messages.


module Agda.Syntax.Concrete.Definitions
    ( NiceDeclaration(..)
    , NiceConstructor, NiceTypeSignature
    , Clause(..)
    , DeclarationException(..)
    , DeclarationWarning(..), DeclarationWarning'(..), unsafeDeclarationWarning
    , Nice, NiceEnv(..), runNice
    , niceDeclarations
    , notSoNiceDeclarations
    , niceHasAbstract
    , Measure
    , declarationWarningName
    ) where


import Prelude hiding (null)

import Control.Monad         ( forM, guard, unless, void, when )
import Control.Monad.Except  ( )
import Control.Monad.Reader  ( asks )
import Control.Monad.State   ( MonadState(..), gets, StateT, runStateT )
import Control.Monad.Trans   ( lift )

import Data.Bifunctor
import Data.Either (isLeft, isRight)
import Data.Function (on)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Semigroup ( Semigroup(..) )
import qualified Data.List as List
import qualified Data.Foldable as Fold
import qualified Data.Traversable as Trav

import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Pattern
import Agda.Syntax.Common hiding (TerminationCheck())
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Position
import Agda.Syntax.Notation
import Agda.Syntax.Concrete.Pretty () --instance only
import Agda.Syntax.Concrete.Fixity
import Agda.Syntax.Common.Pretty

import Agda.Syntax.Concrete.Definitions.Errors
import Agda.Syntax.Concrete.Definitions.Monad
import Agda.Syntax.Concrete.Definitions.Types

import Agda.Utils.AffineHole
import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List (isSublistOf, spanJust)
import Agda.Utils.List1 (List1, pattern (:|), (<|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Three
import Agda.Utils.Tuple
import Agda.Utils.Update

import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    The niceifier
 --------------------------------------------------------------------------}

-- | Check that declarations in a mutual block are consistently
--   equipped with MEASURE pragmas, or whether there is a
--   NO_TERMINATION_CHECK pragma.
combineTerminationChecks :: Range -> [TerminationCheck] -> Nice TerminationCheck
combineTerminationChecks r tcs = loop tcs where
  loop :: [TerminationCheck] -> Nice TerminationCheck
  loop []         = return TerminationCheck
  loop (tc : tcs) = do
    let failure r = declarationException $ InvalidMeasureMutual r
    tc' <- loop tcs
    case (tc, tc') of
      (TerminationCheck      , tc'                   ) -> return tc'
      (tc                    , TerminationCheck      ) -> return tc
      (NonTerminating        , NonTerminating        ) -> return NonTerminating
      (NoTerminationCheck    , NoTerminationCheck    ) -> return NoTerminationCheck
      (NoTerminationCheck    , Terminating           ) -> return Terminating
      (Terminating           , NoTerminationCheck    ) -> return Terminating
      (Terminating           , Terminating           ) -> return Terminating
      (TerminationMeasure{}  , TerminationMeasure{}  ) -> return tc
      (TerminationMeasure r _, NoTerminationCheck    ) -> failure r
      (TerminationMeasure r _, Terminating           ) -> failure r
      (NoTerminationCheck    , TerminationMeasure r _) -> failure r
      (Terminating           , TerminationMeasure r _) -> failure r
      (TerminationMeasure r _, NonTerminating        ) -> failure r
      (NonTerminating        , TerminationMeasure r _) -> failure r
      (NoTerminationCheck    , NonTerminating        ) -> failure r
      (Terminating           , NonTerminating        ) -> failure r
      (NonTerminating        , NoTerminationCheck    ) -> failure r
      (NonTerminating        , Terminating           ) -> failure r

combineCoverageChecks :: [CoverageCheck] -> CoverageCheck
combineCoverageChecks = Fold.fold

combinePositivityChecks :: [PositivityCheck] -> PositivityCheck
combinePositivityChecks = Fold.fold

data DeclKind
    = LoneSigDecl Range DataRecOrFun Name
    | LoneDefs DataRecOrFun [Name]
    | OtherDecl
  deriving (Eq, Show)

declKind :: NiceDeclaration -> DeclKind
declKind (FunSig r _ _ _ _ _ tc cc x _)      = LoneSigDecl r (FunName tc cc) x
declKind (NiceRecSig r _ _ _ pc uc x _ _)    = LoneSigDecl r (RecName pc uc) x
declKind (NiceDataSig r _ _ _ pc uc x _ _)   = LoneSigDecl r (DataName pc uc) x
declKind (FunDef r _ abs ins tc cc x _)      = LoneDefs (FunName tc cc) [x]
declKind (NiceDataDef _ _ _ pc uc x pars _)  = LoneDefs (DataName pc uc) [x]
declKind (NiceUnquoteData _ _ _ pc uc x _ _) = LoneDefs (DataName pc uc) [x]
declKind (NiceRecDef _ _ _ pc uc x _ pars _) = LoneDefs (RecName pc uc) [x]
declKind (NiceUnquoteDef _ _ _ tc cc xs _)   = LoneDefs (FunName tc cc) xs
declKind Axiom{}                             = OtherDecl
declKind NiceField{}                         = OtherDecl
declKind PrimitiveFunction{}                 = OtherDecl
declKind NiceMutual{}                        = OtherDecl
declKind NiceModule{}                        = OtherDecl
declKind NiceModuleMacro{}                   = OtherDecl
declKind NiceOpen{}                          = OtherDecl
declKind NiceImport{}                        = OtherDecl
declKind NicePragma{}                        = OtherDecl
declKind NiceFunClause{}                     = OtherDecl
declKind NicePatternSyn{}                    = OtherDecl
declKind NiceGeneralize{}                    = OtherDecl
declKind NiceUnquoteDecl{}                   = OtherDecl
declKind NiceLoneConstructor{}               = OtherDecl
declKind NiceOpaque{}                        = OtherDecl

-- | Replace (Data/Rec/Fun)Sigs with Axioms for postulated names
--   The first argument is a list of axioms only.
replaceSigs
  :: LoneSigs               -- ^ Lone signatures to be turned into Axioms
  -> [NiceDeclaration]      -- ^ Declarations containing them
  -> [NiceDeclaration]      -- ^ In the output, everything should be defined
replaceSigs ps = if Map.null ps then id else \case
  []     -> __IMPOSSIBLE__
  (d:ds) ->
    case replaceable d of
      -- If declaration d of x is mentioned in the map of lone signatures then replace
      -- it with an axiom
      Just (x, axiom)
        | (Just (LoneSig _ x' _), ps') <- Map.updateLookupWithKey (\ _ _ -> Nothing) x ps
        , getRange x == getRange x'
            -- Use the range as UID to ensure we do not replace the wrong signature.
            -- This could happen if the user wrote a duplicate definition.
        -> axiom : replaceSigs ps' ds
      _ -> d     : replaceSigs ps  ds

  where

    -- A @replaceable@ declaration is a signature. It has a name and we can make an
    -- @Axiom@ out of it.
    replaceable :: NiceDeclaration -> Maybe (Name, NiceDeclaration)
    replaceable = \case
      FunSig r acc abst inst _ argi _ _ x' e ->
        -- #4881: Don't use the unique NameId for NoName lookups.
        let x = if isNoName x' then noName (nameRange x') else x' in
        Just (x, Axiom r acc abst inst argi x' e)
      NiceRecSig r erased acc abst _ _ x pars t ->
        let e = Generalized $ makePi (lamBindingsToTelescope r pars) t in
        Just (x, Axiom r acc abst NotInstanceDef
                   (setQuantity (asQuantity erased) defaultArgInfo) x e)
      NiceDataSig r erased acc abst _ _ x pars t ->
        let e = Generalized $ makePi (lamBindingsToTelescope r pars) t in
        Just (x, Axiom r acc abst NotInstanceDef
                   (setQuantity (asQuantity erased) defaultArgInfo) x e)
      _ -> Nothing

-- | Main. Fixities (or more precisely syntax declarations) are needed when
--   grouping function clauses.
niceDeclarations :: Fixities -> [Declaration] -> Nice [NiceDeclaration]
niceDeclarations fixs ds = do

  -- Run the nicifier in an initial environment. But keep the warnings.
  st <- get
  put $ initNiceState { niceWarn = niceWarn st }
  nds <- nice ds

  -- Check that every signature got its definition.
  ps <- use loneSigs
  checkLoneSigs ps
  -- We postulate the missing ones and insert them in place of the corresponding @FunSig@
  let ds = replaceSigs ps nds

  -- Note that loneSigs is ensured to be empty.
  -- (Important, since inferMutualBlocks also uses loneSigs state).
  res <- inferMutualBlocks ds

  -- Restore the old state, but keep the warnings.
  warns <- gets niceWarn
  put $ st { niceWarn = warns }
  return res

  where

    inferMutualBlocks :: [NiceDeclaration] -> Nice [NiceDeclaration]
    inferMutualBlocks [] = return []
    inferMutualBlocks (d : ds) =
      case declKind d of
        OtherDecl    -> (d :) <$> inferMutualBlocks ds
        LoneDefs{}   -> (d :) <$> inferMutualBlocks ds  -- Andreas, 2017-10-09, issue #2576: report error in ConcreteToAbstract
        LoneSigDecl r k x  -> do
          _ <- addLoneSig r x k
          InferredMutual checks nds0 ds1 <- untilAllDefined (mutualChecks k) ds
          -- If we still have lone signatures without any accompanying definition,
          -- we postulate the definition and substitute the axiom for the lone signature
          ps <- use loneSigs
          checkLoneSigs ps
          let ds0 = replaceSigs ps (d : nds0) -- NB: don't forget the LoneSig the block started with!
          -- We then keep processing the rest of the block
          tc <- combineTerminationChecks (getRange d) (mutualTermination checks)
          let cc = combineCoverageChecks              (mutualCoverage checks)
          let pc = combinePositivityChecks            (mutualPositivity checks)
          (NiceMutual (getRange ds0) tc cc pc ds0 :) <$> inferMutualBlocks ds1
      where
        untilAllDefined :: MutualChecks -> [NiceDeclaration] -> Nice InferredMutual
        untilAllDefined checks ds = do
          done <- noLoneSigs
          if done then return (InferredMutual checks [] ds) else
            case ds of
              []     -> return (InferredMutual checks [] ds)
              d : ds -> case declKind d of
                LoneSigDecl r k x -> do
                  void $ addLoneSig r x k
                  extendInferredBlock  d <$> untilAllDefined (mutualChecks k <> checks) ds
                LoneDefs k xs -> do
                  mapM_ removeLoneSig xs
                  extendInferredBlock  d <$> untilAllDefined (mutualChecks k <> checks) ds
                OtherDecl -> extendInferredBlock d <$> untilAllDefined checks ds

    nice :: [Declaration] -> Nice [NiceDeclaration]
    nice [] = return []
    nice ds = do
      (xs , ys) <- nice1 ds
      (xs ++) <$> nice ys

    nice1 :: [Declaration] -> Nice ([NiceDeclaration], [Declaration])
    nice1 []     = return ([], []) -- Andreas, 2017-09-16, issue #2759: no longer __IMPOSSIBLE__
    nice1 (d:ds) = do
      let justWarning :: HasCallStack => DeclarationWarning' -> Nice ([NiceDeclaration], [Declaration])
          justWarning w = do
            -- NOTE: This is the location of the invoker of justWarning, not here.
            withCallerCallStack $ declarationWarning' w
            nice1 ds

      case d of

        TypeSig info _tac x t -> do
          termCheck <- use terminationCheckPragma
          covCheck  <- use coverageCheckPragma
          -- Andreas, 2020-09-28, issue #4950: take only range of identifier,
          -- since parser expands type signatures with several identifiers
          -- (like @x y z : A@) into several type signatures (with imprecise ranges).
          let r = getRange x
          -- register x as lone type signature, to recognize clauses later
          x' <- addLoneSig r x $ FunName termCheck covCheck
          return ([FunSig r PublicAccess ConcreteDef NotInstanceDef NotMacroDef info termCheck covCheck x' t] , ds)

        -- Should not show up: all FieldSig are part of a Field block
        FieldSig{} -> __IMPOSSIBLE__

        Generalize r [] -> justWarning $ EmptyGeneralize r
        Generalize r sigs -> do
          gs <- forM sigs $ \case
            sig@(TypeSig info tac x t) -> do
              -- Andreas, 2022-03-25, issue #5850:
              -- Warn about @variable {x} : A@ which is equivalent to @variable x : A@.
              when (getHiding info == Hidden) $
                declarationWarning $ HiddenGeneralize $ getRange x
              return $ NiceGeneralize (getRange sig) PublicAccess info tac x t
            _ -> __IMPOSSIBLE__
          return (gs, ds)

        (FunClause lhs _ _ _)         -> do
          termCheck <- use terminationCheckPragma
          covCheck  <- use coverageCheckPragma
          catchall  <- popCatchallPragma
          xs <- loneFuns <$> use loneSigs
          -- for each type signature 'x' waiting for clauses, we try
          -- if we have some clauses for 'x'
          case [ (x, (x', fits, rest))
               | (x, x') <- xs
               , let (fits, rest) =
                      -- Anonymous declarations only have 1 clause each!
                      if isNoName x then ([d], ds)
                      else span (couldBeFunClauseOf (Map.lookup x fixs) x) (d : ds)
               , not (null fits)
               ] of

            -- case: clauses match none of the sigs
            [] -> case lhs of
              -- Subcase: The lhs is single identifier (potentially anonymous).
              -- Treat it as a function clause without a type signature.
              LHS p [] [] | Just x <- isSingleIdentifierP p -> do
                d  <- mkFunDef (setOrigin Inserted defaultArgInfo) termCheck covCheck x Nothing [d] -- fun def without type signature is relevant
                return (d , ds)
              -- Subcase: The lhs is a proper pattern.
              -- This could be a let-pattern binding. Pass it on.
              -- A missing type signature error might be raise in ConcreteToAbstract
              _ -> do
                return ([NiceFunClause (getRange d) PublicAccess ConcreteDef termCheck covCheck catchall d] , ds)

            -- case: clauses match exactly one of the sigs
            [(x,(x',fits,rest))] -> do
               -- The x'@NoName{} is the unique version of x@NoName{}.
               removeLoneSig x
               ds  <- expandEllipsis fits
               cs  <- mkClauses x' ds False
               return ([FunDef (getRange fits) fits ConcreteDef NotInstanceDef termCheck covCheck x' cs] , rest)

            -- case: clauses match more than one sigs (ambiguity)
            xf:xfs -> declarationException $ AmbiguousFunClauses lhs $ List1.reverse $ fmap fst $ xf :| xfs
                 -- "ambiguous function clause; cannot assign it uniquely to one type signature"

        Field r [] -> justWarning $ EmptyField r
        Field _ fs -> (,ds) <$> niceAxioms FieldBlock fs

        DataSig r erased x tel t -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          _ <- addLoneSig r x $ DataName pc uc
          (,ds) <$> dataOrRec pc uc NiceDataDef
                      (flip NiceDataSig erased) (niceAxioms DataBlock) r
                      x (Just (tel, t)) Nothing

        Data r erased x tel t cs -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (DataName pc uc) x (Just t)
          (,ds) <$> dataOrRec pc uc NiceDataDef
                      (flip NiceDataSig erased) (niceAxioms DataBlock) r
                      x ((tel,) <$> mt) (Just (tel, cs))

        DataDef r x tel cs -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (DataName pc uc) x Nothing
          (,ds) <$> dataOrRec pc uc NiceDataDef
                      (flip NiceDataSig defaultErased)
                      (niceAxioms DataBlock) r x ((tel,) <$> mt)
                      (Just (tel, cs))

        RecordSig r erased x tel t -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          _ <- addLoneSig r x $ RecName pc uc
          return ( [NiceRecSig r erased PublicAccess ConcreteDef pc uc x
                      tel t]
                 , ds
                 )

        Record r erased x dir tel t cs -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (RecName pc uc) x (Just t)
          (,ds) <$> dataOrRec pc uc
                      (\r o a pc uc x tel cs ->
                        NiceRecDef r o a pc uc x dir tel cs)
                      (flip NiceRecSig erased) return r x
                      ((tel,) <$> mt) (Just (tel, cs))

        RecordDef r x dir tel cs   -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (RecName pc uc) x Nothing
          (,ds) <$> dataOrRec pc uc
                      (\r o a pc uc x tel cs ->
                        NiceRecDef r o a pc uc x dir tel cs)
                      (flip NiceRecSig defaultErased) return r x
                      ((tel,) <$> mt) (Just (tel, cs))

        RecordDirective r -> justWarning $ InvalidRecordDirective (getRange r)

        Mutual r ds' -> do
          -- The lone signatures encountered so far are not in scope
          -- for the mutual definition
          breakImplicitMutualBlock r "`mutual` blocks"
          case ds' of
            [] -> justWarning $ EmptyMutual r
            _  -> (,ds) <$> (singleton <$> (mkOldMutual r =<< nice ds'))

        InterleavedMutual r ds' -> do
          -- The lone signatures encountered so far are not in scope
          -- for the mutual definition
          breakImplicitMutualBlock r "`interleaved mutual` blocks"
          case ds' of
            [] -> justWarning $ EmptyMutual r
            _  -> (,ds) <$> (singleton <$> (mkInterleavedMutual r =<< nice ds'))

        LoneConstructor r [] -> justWarning $ EmptyConstructor r
        LoneConstructor r ds' ->
          ((,ds) . singleton . NiceLoneConstructor r) <$> niceAxioms ConstructorBlock ds'


        Abstract r []  -> justWarning $ EmptyAbstract r
        Abstract r ds' ->
          (,ds) <$> (abstractBlock r =<< nice ds')

        Private r UserWritten []  -> justWarning $ EmptyPrivate r
        Private r o ds' ->
          (,ds) <$> (privateBlock r o =<< nice ds')

        InstanceB r []  -> justWarning $ EmptyInstance r
        InstanceB r ds' ->
          (,ds) <$> (instanceBlock r =<< nice ds')

        Macro r []  -> justWarning $ EmptyMacro r
        Macro r ds' ->
          (,ds) <$> (macroBlock r =<< nice ds')

        Postulate r []  -> justWarning $ EmptyPostulate r
        Postulate _ ds' ->
          (,ds) <$> niceAxioms PostulateBlock ds'

        Primitive r []  -> justWarning $ EmptyPrimitive r
        Primitive _ ds' -> (,ds) <$> (map toPrim <$> niceAxioms PrimitiveBlock ds')

        Module r erased x tel ds' -> return $
          ([NiceModule r PublicAccess ConcreteDef erased x tel ds'], ds)

        ModuleMacro r erased x modapp op is -> return $
          ([NiceModuleMacro r PublicAccess erased x modapp op is], ds)

        -- Fixity and syntax declarations and polarity pragmas have
        -- already been processed.
        Infix _ _  -> return ([], ds)
        Syntax _ _ -> return ([], ds)

        PatternSyn r n as p -> do
          return ([NicePatternSyn r PublicAccess n as p] , ds)
        Open r x is         -> return ([NiceOpen r x is] , ds)
        Import r x as op is -> return ([NiceImport r x as op is] , ds)

        UnquoteDecl r xs e -> do
          tc <- use terminationCheckPragma
          cc <- use coverageCheckPragma
          return ([NiceUnquoteDecl r PublicAccess ConcreteDef NotInstanceDef tc cc xs e] , ds)

        UnquoteDef r xs e -> do
          sigs <- map fst . loneFuns <$> use loneSigs
          List1.ifNotNull (filter (`notElem` sigs) xs)
            {-then-} (declarationException . UnquoteDefRequiresSignature)
            {-else-} $ do
              mapM_ removeLoneSig xs
              return ([NiceUnquoteDef r PublicAccess ConcreteDef TerminationCheck YesCoverageCheck xs e] , ds)

        UnquoteData r xs cs e -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          return ([NiceUnquoteData r PublicAccess ConcreteDef pc uc xs cs e], ds)

        Pragma p -> do
          -- Warn about unsafe pragmas unless we are in a builtin module.
          whenM (asks safeButNotBuiltin) $
            whenJust (unsafePragma p) $ \ w ->
              declarationWarning w
          nicePragma p ds

        Opaque r ds' -> do
          breakImplicitMutualBlock r "`opaque` blocks"

          -- Split the enclosed declarations into an initial run of
          -- 'unfolding' statements and the rest of the body.
          let
            (unfoldings, body) = flip spanMaybe ds' $ \case
              Unfolding _ ns -> pure ns
              _ -> Nothing

          -- The body of an 'opaque' definition can have mutual
          -- recursion by interleaving type signatures and definitions,
          -- just like the body of a module.
          decls0 <- nice body
          ps <- use loneSigs
          checkLoneSigs ps
          let decls = replaceSigs ps decls0
          body <- inferMutualBlocks decls
          pure ([NiceOpaque r (concat unfoldings) body], ds)

        Unfolding r _ -> declarationException $ UnfoldingOutsideOpaque r

    nicePragma :: Pragma -> [Declaration] -> Nice ([NiceDeclaration], [Declaration])

    nicePragma (TerminationCheckPragma r (TerminationMeasure _ x)) ds =
      if canHaveTerminationMeasure ds then
        withTerminationCheckPragma (TerminationMeasure r x) $ nice1 ds
      else do
        declarationWarning $ InvalidTerminationCheckPragma r
        nice1 ds

    nicePragma (TerminationCheckPragma r NoTerminationCheck) ds = do
      -- This PRAGMA has been deprecated in favour of (NON_)TERMINATING
      -- We warn the user about it and then assume the function is NON_TERMINATING.
      declarationWarning $ PragmaNoTerminationCheck r
      nicePragma (TerminationCheckPragma r NonTerminating) ds

    nicePragma (TerminationCheckPragma r tc) ds =
      if canHaveTerminationCheckPragma ds then
        withTerminationCheckPragma tc $ nice1 ds
      else do
        declarationWarning $ InvalidTerminationCheckPragma r
        nice1 ds

    nicePragma (NoCoverageCheckPragma r) ds =
      if canHaveCoverageCheckPragma ds then
        withCoverageCheckPragma NoCoverageCheck $ nice1 ds
      else do
        declarationWarning $ InvalidCoverageCheckPragma r
        nice1 ds

    nicePragma (CatchallPragma r) ds =
      if canHaveCatchallPragma ds then
        withCatchallPragma True $ nice1 ds
      else do
        declarationWarning $ InvalidCatchallPragma r
        nice1 ds

    nicePragma (NoPositivityCheckPragma r) ds =
      if canHaveNoPositivityCheckPragma ds then
        withPositivityCheckPragma NoPositivityCheck $ nice1 ds
      else do
        declarationWarning $ InvalidNoPositivityCheckPragma r
        nice1 ds

    nicePragma (NoUniverseCheckPragma r) ds =
      if canHaveNoUniverseCheckPragma ds then
        withUniverseCheckPragma NoUniverseCheck $ nice1 ds
      else do
        declarationWarning $ InvalidNoUniverseCheckPragma r
        nice1 ds

    nicePragma p@CompilePragma{} ds = do
      return ([NicePragma (getRange p) p], ds)

    nicePragma (PolarityPragma{}) ds = return ([], ds)

    nicePragma (BuiltinPragma r str qn@(QName x)) ds = do
      return ([NicePragma r (BuiltinPragma r str qn)], ds)

    nicePragma p@RewritePragma{} ds = return ([NicePragma (getRange p) p], ds)
    nicePragma p ds = return ([NicePragma (getRange p) p], ds)

    canHaveTerminationMeasure :: [Declaration] -> Bool
    canHaveTerminationMeasure [] = False
    canHaveTerminationMeasure (d:ds) = case d of
      TypeSig{} -> True
      (Pragma p) | isAttachedPragma p -> canHaveTerminationMeasure ds
      _         -> False

    canHaveTerminationCheckPragma :: [Declaration] -> Bool
    canHaveTerminationCheckPragma []     = False
    canHaveTerminationCheckPragma (d:ds) = case d of
      Mutual _ ds   -> any (canHaveTerminationCheckPragma . singleton) ds
      TypeSig{}     -> True
      FunClause{}   -> True
      UnquoteDecl{} -> True
      (Pragma p) | isAttachedPragma p -> canHaveTerminationCheckPragma ds
      _             -> False

    canHaveCoverageCheckPragma :: [Declaration] -> Bool
    canHaveCoverageCheckPragma = canHaveTerminationCheckPragma

    canHaveCatchallPragma :: [Declaration] -> Bool
    canHaveCatchallPragma []     = False
    canHaveCatchallPragma (d:ds) = case d of
      FunClause{} -> True
      (Pragma p) | isAttachedPragma p -> canHaveCatchallPragma ds
      _           -> False

    canHaveNoPositivityCheckPragma :: [Declaration] -> Bool
    canHaveNoPositivityCheckPragma []     = False
    canHaveNoPositivityCheckPragma (d:ds) = case d of
      Mutual _ ds                   -> any (canHaveNoPositivityCheckPragma . singleton) ds
      Data{}                        -> True
      DataSig{}                     -> True
      DataDef{}                     -> True
      Record{}                      -> True
      RecordSig{}                   -> True
      RecordDef{}                   -> True
      Pragma p | isAttachedPragma p -> canHaveNoPositivityCheckPragma ds
      _                             -> False

    canHaveNoUniverseCheckPragma :: [Declaration] -> Bool
    canHaveNoUniverseCheckPragma []     = False
    canHaveNoUniverseCheckPragma (d:ds) = case d of
      Data{}                        -> True
      DataSig{}                     -> True
      DataDef{}                     -> True
      Record{}                      -> True
      RecordSig{}                   -> True
      RecordDef{}                   -> True
      Pragma p | isAttachedPragma p -> canHaveNoPositivityCheckPragma ds
      _                             -> False

    -- Pragma that attaches to the following declaration.
    isAttachedPragma :: Pragma -> Bool
    isAttachedPragma = \case
      TerminationCheckPragma{}  -> True
      CatchallPragma{}          -> True
      NoPositivityCheckPragma{} -> True
      NoUniverseCheckPragma{}   -> True
      _                         -> False

    -- We could add a default type signature here, but at the moment we can't
    -- infer the type of a record or datatype, so better to just fail here.
    defaultTypeSig :: DataRecOrFun -> Name -> Maybe Expr -> Nice (Maybe Expr)
    defaultTypeSig k x t@Just{} = return t
    defaultTypeSig k x Nothing  = do
      caseMaybeM (getSig x) (return Nothing) $ \ k' -> do
        unless (sameKind k k') $ declarationException $ WrongDefinition x k' k
        Nothing <$ removeLoneSig x

    dataOrRec
      :: forall a decl
      .  PositivityCheck
      -> UniverseCheck
      -> (Range -> Origin -> IsAbstract -> PositivityCheck -> UniverseCheck -> Name -> [LamBinding] -> [decl] -> NiceDeclaration)
         -- Construct definition.
      -> (Range -> Access -> IsAbstract -> PositivityCheck -> UniverseCheck -> Name -> [LamBinding] -> Expr -> NiceDeclaration)
         -- Construct signature.
      -> ([a] -> Nice [decl])        -- Constructor checking.
      -> Range
      -> Name                        -- Data/record type name.
      -> Maybe ([LamBinding], Expr)  -- Parameters and type.  If not @Nothing@ a signature is created.
      -> Maybe ([LamBinding], [a])   -- Parameters and constructors.  If not @Nothing@, a definition body is created.
      -> Nice [NiceDeclaration]
    dataOrRec pc uc mkDef mkSig niceD r x mt mcs = do
      mds <- Trav.forM mcs $ \ (tel, cs) -> (tel,) <$> niceD cs
      -- We set origin to UserWritten if the user split the data/rec herself,
      -- and to Inserted if the she wrote a single declaration that we're
      -- splitting up here. We distinguish these because the scoping rules for
      -- generalizable variables differ in these cases.
      let o | isJust mt && isJust mcs = Inserted
            | otherwise               = UserWritten
      return $ catMaybes $
        [ mt  <&> \ (tel, t)  -> mkSig (fuseRange x t) PublicAccess ConcreteDef pc uc x tel t
        , mds <&> \ (tel, ds) -> mkDef r o ConcreteDef pc uc x (caseMaybe mt tel $ const $ concatMap dropTypeAndModality tel) ds
          -- If a type is given (mt /= Nothing), we have to delete the types in @tel@
          -- for the data definition, lest we duplicate them. And also drop modalities (#1886).
        ]
    -- Translate axioms
    niceAxioms :: KindOfBlock -> [TypeSignatureOrInstanceBlock] -> Nice [NiceDeclaration]
    niceAxioms b ds = List.concat <$> mapM (niceAxiom b) ds

    niceAxiom :: KindOfBlock -> TypeSignatureOrInstanceBlock -> Nice [NiceDeclaration]
    niceAxiom b = \case
      d@(TypeSig rel _tac x t) -> do
        return [ Axiom (getRange d) PublicAccess ConcreteDef NotInstanceDef rel x t ]
      d@(FieldSig i tac x argt) | b == FieldBlock -> do
        return [ NiceField (getRange d) PublicAccess ConcreteDef i tac x argt ]
      InstanceB r decls -> do
        instanceBlock r =<< niceAxioms InstanceBlock decls
      Private r o decls | PostulateBlock <- b -> do
        privateBlock r o =<< niceAxioms b decls
      Pragma p@(RewritePragma r _ _) -> do
        return [ NicePragma r p ]
      d -> declarationException $ WrongContentBlock b $ getRange d

    toPrim :: NiceDeclaration -> NiceDeclaration
    toPrim (Axiom r p a i rel x t) = PrimitiveFunction r p a x (Arg rel t)
    toPrim _                       = __IMPOSSIBLE__

    -- Create a function definition.
    mkFunDef info termCheck covCheck x mt ds0 = do
      ds <- expandEllipsis ds0
      cs <- mkClauses x ds False
      return [ FunSig (fuseRange x t) PublicAccess ConcreteDef NotInstanceDef NotMacroDef info termCheck covCheck x t
             , FunDef (getRange ds0) ds0 ConcreteDef NotInstanceDef termCheck covCheck x cs ]
        where
          t = fromMaybe (underscore (getRange x)) mt

    underscore r = Underscore r Nothing


    expandEllipsis :: [Declaration] -> Nice [Declaration]
    expandEllipsis [] = return []
    expandEllipsis (d@(FunClause lhs@(LHS p _ _) _ _ _) : ds)
      | hasEllipsis p = (d :) <$> expandEllipsis ds
      | otherwise     = (d :) <$> expand (killRange p) ds
      where
        expand :: Pattern -> [Declaration] -> Nice [Declaration]
        expand _ [] = return []
        expand p (d : ds) = do
          case d of
            Pragma (CatchallPragma _) -> do
                  (d :) <$> expand p ds
            FunClause (LHS p0 eqs es) rhs wh ca -> do
              case hasEllipsis' p0 of
                ManyHoles -> declarationException $ MultipleEllipses p0
                OneHole cxt ~(EllipsisP r Nothing) -> do
                  -- Replace the ellipsis by @p@.
                  let p1 = cxt $ EllipsisP r $ Just $ setRange r p
                  let d' = FunClause (LHS p1 eqs es) rhs wh ca
                  -- If we have with-expressions (es /= []) then the following
                  -- ellipses also get the additional patterns in p0.
                  (d' :) <$> expand (if null es then p else killRange p1) ds
                ZeroHoles _ -> do
                  -- We can have ellipses after a fun clause without.
                  -- They refer to the last clause that introduced new with-expressions.
                  -- Same here: If we have new with-expressions, the next ellipses will
                  -- refer to us.
                  -- Andreas, Jesper, 2017-05-13, issue #2578
                  -- Need to update the range also on the next with-patterns.
                  (d :) <$> expand (if null es then p else killRange p0) ds
            _ -> __IMPOSSIBLE__
    expandEllipsis _ = __IMPOSSIBLE__

    -- Turn function clauses into nice function clauses.
    mkClauses :: Name -> [Declaration] -> Catchall -> Nice [Clause]
    mkClauses _ [] _ = return []
    mkClauses x (Pragma (CatchallPragma r) : cs) True  = do
      declarationWarning $ InvalidCatchallPragma r
      mkClauses x cs True
    mkClauses x (Pragma (CatchallPragma r) : cs) False = do
      when (null cs) $ declarationWarning $ InvalidCatchallPragma r
      mkClauses x cs True

    mkClauses x (FunClause lhs rhs wh ca : cs) catchall
      | null (lhsWithExpr lhs) || hasEllipsis lhs  =
      (Clause x (ca || catchall) lhs rhs wh [] :) <$> mkClauses x cs False   -- Will result in an error later.

    mkClauses x (FunClause lhs rhs wh ca : cs) catchall = do
      when (null withClauses) $ declarationException $ MissingWithClauses x lhs
      wcs <- mkClauses x withClauses False
      (Clause x (ca || catchall) lhs rhs wh wcs :) <$> mkClauses x cs' False
      where
        (withClauses, cs') = subClauses cs

        -- A clause is a subclause if the number of with-patterns is
        -- greater or equal to the current number of with-patterns plus the
        -- number of with arguments.
        numWith = numberOfWithPatterns p + length (filter visible es) where LHS p _ es = lhs

        subClauses :: [Declaration] -> ([Declaration],[Declaration])
        subClauses (c@(FunClause (LHS p0 _ _) _ _ _) : cs)
         | isEllipsis p0 ||
           numberOfWithPatterns p0 >= numWith = mapFst (c:) (subClauses cs)
         | otherwise                           = ([], c:cs)
        subClauses (c@(Pragma (CatchallPragma r)) : cs) = case subClauses cs of
          ([], cs') -> ([], c:cs')
          (cs, cs') -> (c:cs, cs')
        subClauses [] = ([],[])
        subClauses _  = __IMPOSSIBLE__
    mkClauses _ _ _ = __IMPOSSIBLE__

    couldBeCallOf :: Maybe Fixity' -> Name -> Pattern -> Bool
    couldBeCallOf mFixity x p =
      let
      pns        = patternNames p
      xStrings   = nameStringParts x
      patStrings = concatMap nameStringParts pns
      in
--          trace ("x = " ++ prettyShow x) $
--          trace ("pns = " ++ show pns) $
--          trace ("xStrings = " ++ show xStrings) $
--          trace ("patStrings = " ++ show patStrings) $
--          trace ("mFixity = " ++ show mFixity) $
      case (listToMaybe pns, mFixity) of
        -- first identifier in the patterns is the fun.symbol?
        (Just y, _) | x == y -> True -- trace ("couldBe since y = " ++ prettyShow y) $ True
        -- are the parts of x contained in p
        _ | xStrings `isSublistOf` patStrings -> True -- trace ("couldBe since isSublistOf") $ True
        -- looking for a mixfix fun.symb
        (_, Just fix) ->  -- also matches in case of a postfix
           let notStrings = stringParts (theNotation fix)
           in  -- trace ("notStrings = " ++ show notStrings) $
               -- trace ("patStrings = " ++ show patStrings) $
               not (null notStrings) && (notStrings `isSublistOf` patStrings)
        -- not a notation, not first id: give up
        _ -> False -- trace ("couldBe not (case default)") $ False


    -- for finding nice clauses for a type sig in mutual blocks
    couldBeNiceFunClauseOf :: Maybe Fixity' -> Name -> NiceDeclaration
                           -> Maybe (MutualChecks, Declaration)
    couldBeNiceFunClauseOf mf n (NiceFunClause _ _ _ tc cc _ d)
      = (MutualChecks [tc] [cc] [], d) <$ guard (couldBeFunClauseOf mf n d)
    couldBeNiceFunClauseOf _ _ _ = Nothing

    -- for finding clauses for a type sig in mutual blocks
    couldBeFunClauseOf :: Maybe Fixity' -> Name -> Declaration -> Bool
    couldBeFunClauseOf mFixity x (Pragma (CatchallPragma{})) = True
    couldBeFunClauseOf mFixity x (FunClause (LHS p _ _) _ _ _) =
       hasEllipsis p || couldBeCallOf mFixity x p
    couldBeFunClauseOf _ _ _ = False -- trace ("couldBe not (fun default)") $ False

    -- Turn a new style `interleaved mutual' block into a new style mutual block
    -- by grouping the declarations in blocks.
    mkInterleavedMutual
      :: Range                 -- Range of the whole @mutual@ block.
      -> [NiceDeclaration]     -- Declarations inside the block.
      -> Nice NiceDeclaration  -- Returns a 'NiceMutual'.
    mkInterleavedMutual r ds' = do
      (other, (m, checks, _)) <- runStateT (groupByBlocks r ds') (empty, mempty, 0)
      let idecls = other ++ concatMap (uncurry interleavedDecl) (Map.toList m)
      let decls0 = map snd $ List.sortBy (compare `on` fst) idecls
      ps <- use loneSigs
      checkLoneSigs ps
      let decls = replaceSigs ps decls0
      -- process the checks
      tc <- combineTerminationChecks r (mutualTermination checks)
      let cc = combineCoverageChecks   (mutualCoverage checks)
      let pc = combinePositivityChecks (mutualPositivity checks)
      pure $ NiceMutual r tc cc pc decls

      where

        ------------------------------------------------------------------------------
        -- Adding Signatures
        addType :: Name -> (DeclNum -> a) -> MutualChecks
                -> StateT (Map Name a, MutualChecks, DeclNum) Nice ()
        addType n c mc = do
          (m, checks, i) <- get
          when (isJust $ Map.lookup n m) $ lift $ declarationException $ DuplicateDefinition n
          put (Map.insert n (c i) m, mc <> checks, i+1)

        addFunType d@(FunSig _ _ _ _ _ _ tc cc n _) = do
           let checks = MutualChecks [tc] [cc] []
           addType n (\ i -> InterleavedFun i d Nothing) checks
        addFunType _ = __IMPOSSIBLE__

        addDataType d@(NiceDataSig _ _ _ _ pc uc n _ _) = do
          let checks = MutualChecks [] [] [pc]
          addType n (\ i -> InterleavedData i d Nothing) checks
        addDataType _ = __IMPOSSIBLE__

        ------------------------------------------------------------------------------
        -- Adding constructors & clauses

        addDataConstructors :: Maybe Range        -- Range of the `data A where` (if any)
                            -> Maybe Name         -- Data type the constructors belong to
                            -> [NiceConstructor]  -- Constructors to add
                            -> StateT (InterleavedMutual, MutualChecks, DeclNum) Nice ()
        -- if we know the type's name, we can go ahead
        addDataConstructors mr (Just n) ds = do
          (m, checks, i) <- get
          case Map.lookup n m of
            Just (InterleavedData i0 sig cs) -> do
              lift $ removeLoneSig n
              -- add the constructors to the existing ones (if any)
              let (cs', i') = case cs of
                    Nothing        -> ((i , ds :| [] ), i+1)
                    Just (i1, ds1) -> ((i1, ds <| ds1), i)
              put (Map.insert n (InterleavedData i0 sig (Just cs')) m, checks, i')
            _ -> lift $ declarationWarning $ MissingDeclarations $ case mr of
                   Just r -> [(n, r)]
                   Nothing -> flip foldMap ds $ \case
                     Axiom r _ _ _ _ n _ -> [(n, r)]
                     _ -> __IMPOSSIBLE__

        addDataConstructors mr Nothing [] = pure ()

        -- Otherwise we try to guess which datasig the constructor is referring to
        addDataConstructors mr Nothing (d : ds) = do
          -- get the candidate data types that are in this interleaved mutual block
          (m, _, _) <- get
          let sigs = mapMaybe (\ (n, d) -> n <$ isInterleavedData d) $ Map.toList m
          -- check whether this constructor matches any of them
          case isConstructor sigs d of
            Right n -> do
              -- if so grab the whole block that may work and add them
              let (ds0, ds1) = span (isRight . isConstructor [n]) ds
              addDataConstructors Nothing (Just n) (d : ds0)
              -- and then repeat the process for the rest of the block
              addDataConstructors Nothing Nothing ds1
            Left (n, ns) -> lift $ declarationException $ AmbiguousConstructor (getRange d) n ns

        addFunDef :: NiceDeclaration -> StateT (InterleavedMutual, MutualChecks, DeclNum) Nice ()
        addFunDef (FunDef _ ds _ _ tc cc n cs) = do
          let check = MutualChecks [tc] [cc] []
          (m, checks, i) <- get
          case Map.lookup n m of
            Just (InterleavedFun i0 sig cs0) -> do
              let (cs', i') = case cs0 of
                    Nothing        -> ((i,  (ds, cs) :| [] ), i+1)
                    Just (i1, cs1) -> ((i1, (ds, cs) <| cs1), i)
              put (Map.insert n (InterleavedFun i0 sig (Just cs')) m, check <> checks, i')
            _ -> __IMPOSSIBLE__ -- A FunDef always come after an existing FunSig!
        addFunDef _ = __IMPOSSIBLE__

        addFunClauses :: Range -> [NiceDeclaration]
                      -> StateT (InterleavedMutual, MutualChecks, DeclNum) Nice [(DeclNum, NiceDeclaration)]
        addFunClauses r (nd@(NiceFunClause _ _ _ tc cc _ d@(FunClause lhs _ _ _)) : ds) = do
          -- get the candidate functions that are in this interleaved mutual block
          (m, checks, i) <- get
          let sigs = mapMaybe (\ (n, d) -> n <$ isInterleavedFun d) $ Map.toList m
          -- find the funsig candidates for the funclause of interest
          case [ (x, fits, rest)
               | x <- sigs
               , let (fits, rest) = spanJust (couldBeNiceFunClauseOf (Map.lookup x fixs) x) (nd : ds)
               , not (null fits)
               ] of
            -- no candidate: keep the isolated fun clause, we'll complain about it later
            [] -> do
              let check = MutualChecks [tc] [cc] []
              put (m, check <> checks, i+1)
              ((i,nd) :) <$> groupByBlocks r ds
            -- exactly one candidate: attach the funclause to the definition
            [(n, fits0, rest)] -> do
              let (checkss, fits) = unzip fits0
              ds <- lift $ expandEllipsis fits
              cs <- lift $ mkClauses n ds False
              case Map.lookup n m of
                Just (InterleavedFun i0 sig cs0) -> do
                  let (cs', i') = case cs0 of
                        Nothing        -> ((i,  (fits,cs) :| [] ), i+1)
                        Just (i1, cs1) -> ((i1, (fits,cs) <| cs1), i)
                  let checks' = Fold.fold checkss
                  put (Map.insert n (InterleavedFun i0 sig (Just cs')) m, checks' <> checks, i')
                _ -> __IMPOSSIBLE__
              groupByBlocks r rest
            -- more than one candidate: fail, complaining about the ambiguity!
            xf:xfs -> lift $ declarationException
                           $ AmbiguousFunClauses lhs
                           $ List1.reverse $ fmap (\ (a,_,_) -> a) $ xf :| xfs
        addFunClauses _ _ = __IMPOSSIBLE__

        groupByBlocks :: Range -> [NiceDeclaration]
                      -> StateT (InterleavedMutual, MutualChecks, DeclNum) Nice [(DeclNum, NiceDeclaration)]
        groupByBlocks r []       = pure []
        groupByBlocks r (d : ds) = do
          -- for most branches we deal with the one declaration and move on
          let oneOff act = act >>= \ ns -> (ns ++) <$> groupByBlocks r ds
          case d of
            NiceDataSig{}                -> oneOff $ [] <$ addDataType d
            NiceDataDef r _ _ _ _ n _ ds -> oneOff $ [] <$ addDataConstructors (Just r) (Just n) ds
            NiceLoneConstructor r ds     -> oneOff $ [] <$ addDataConstructors Nothing Nothing ds
            FunSig{}                     -> oneOff $ [] <$ addFunType d
            FunDef _ _ _  _ _ _ n cs
                      | not (isNoName n) -> oneOff $ [] <$ addFunDef d
            -- It's a bit different for fun clauses because we may need to grab a lot
            -- of clauses to handle ellipses properly.
            NiceFunClause{}              -> addFunClauses r (d:ds)
            -- We do not need to worry about RecSig vs. RecDef: we know there's exactly one
            -- of each for record definitions and leaving them in place should be enough!
            _ -> oneOff $ do
              (m, c, i) <- get -- TODO: grab checks from c?
              put (m, c, i+1)
              pure [(i,d)]

    -- Extract the name of the return type (if any) of a potential constructor.
    -- In case of failure return the name of the constructor and the list of candidates
    -- for the return type.
    -- A `constructor' block should only contain NiceConstructors so we crash with
    -- an IMPOSSIBLE otherwise
    isConstructor :: [Name] -> NiceDeclaration -> Either (Name, [Name]) Name
    isConstructor ns (Axiom _ _ _ _ _ n e)
       -- extract the return type & see it as an LHS-style pattern
       | Just p <- exprToPatternWithHoles <$> returnExpr e =
         case [ x | x <- ns
                  , couldBeCallOf (Map.lookup x fixs) x p
                  ] of
           [x] -> Right x
           xs  -> Left (n, xs)
       -- which may fail (e.g. if the "return type" is a hole
       | otherwise = Left (n, [])
    isConstructor _ _ = __IMPOSSIBLE__

    -- Turn an old-style mutual block into a new style mutual block
    -- by pushing the definitions to the end.
    mkOldMutual
      :: Range                 -- Range of the whole @mutual@ block.
      -> [NiceDeclaration]     -- Declarations inside the block.
      -> Nice NiceDeclaration  -- Returns a 'NiceMutual'.
    mkOldMutual r ds' = do
        -- Postulate the missing definitions
        let ps = loneSigsFromLoneNames loneNames
        checkLoneSigs ps
        let ds = replaceSigs ps ds'

        -- -- Remove the declarations that aren't allowed in old style mutual blocks
        -- ds <- fmap catMaybes $ forM ds $ \ d -> let success = pure (Just d) in case d of
        --   -- Andreas, 2013-11-23 allow postulates in mutual blocks
        --   Axiom{}          -> success
        --   -- Andreas, 2017-10-09, issue #2576, raise error about missing type signature
        --   -- in ConcreteToAbstract rather than here.
        --   NiceFunClause{}  -> success
        --   -- Andreas, 2018-05-11, issue #3052, allow pat.syn.s in mutual blocks
        --   NicePatternSyn{} -> success
        --   -- Otherwise, only categorized signatures and definitions are allowed:
        --   -- Data, Record, Fun
        --   _ -> if (declKind d /= OtherDecl) then success
        --        else Nothing <$ declarationWarning (NotAllowedInMutual (getRange d) $ declName d)
        -- Sort the declarations in the mutual block.
        -- Declarations of names go to the top.  (Includes module definitions.)
        -- Definitions of names go to the bottom.
        -- Some declarations are forbidden, as their positioning could confuse
        -- the user.
        (top, bottom, invalid) <- forEither3M ds $ \ d -> do
          let top       = return (In1 d)
              bottom    = return (In2 d)
              invalid s = In3 d <$ do declarationWarning $ NotAllowedInMutual (getRange d) s
          case d of
            -- Andreas, 2013-11-23 allow postulates in mutual blocks
            Axiom{}             -> top
            NiceField{}         -> top
            PrimitiveFunction{} -> top
            -- Andreas, 2019-07-23 issue #3932:
            -- Nested mutual blocks are not supported.
            NiceMutual{}        -> invalid "mutual blocks"
            -- Andreas, 2018-10-29, issue #3246
            -- We could allow modules (top), but this is potentially confusing.
            NiceModule{}        -> invalid "Module definitions"
            -- Lone constructors are only allowed in new-style mutual blocks
            NiceLoneConstructor{} -> invalid "Lone constructors"
            NiceModuleMacro{}   -> top
            NiceOpen{}          -> top
            NiceImport{}        -> top
            NiceRecSig{}        -> top
            NiceDataSig{}       -> top
            -- Andreas, 2017-10-09, issue #2576, raise error about missing type signature
            -- in ConcreteToAbstract rather than here.
            NiceFunClause{}     -> bottom
            FunSig{}            -> top
            FunDef{}            -> bottom
            NiceDataDef{}       -> bottom
            NiceRecDef{}        -> bottom
            -- Andreas, 2018-05-11, issue #3051, allow pat.syn.s in mutual blocks
            -- Andreas, 2018-10-29: We shift pattern synonyms to the bottom
            -- since they might refer to constructors defined in a data types
            -- just above them.
            NicePatternSyn{}    -> bottom
            NiceGeneralize{}    -> top
            NiceUnquoteDecl{}   -> top
            NiceUnquoteDef{}    -> bottom
            NiceUnquoteData{}   -> top

            -- Opaque blocks can not participate in old-style mutual
            -- recursion. If some of the definitions are opaque then
            -- they all need to be.
            NiceOpaque{}        ->
              In3 d <$ do declarationException $ OpaqueInMutual (getRange d)
            NicePragma r pragma -> case pragma of

              OptionsPragma{}           -> top     -- error thrown in the type checker

              -- Some builtins require a definition, and they affect type checking
              -- Thus, we do not handle BUILTINs in mutual blocks (at least for now).
              BuiltinPragma{}           -> invalid "BUILTIN pragmas"

              -- The REWRITE pragma behaves differently before or after the def.
              -- and affects type checking.  Thus, we refuse it here.
              RewritePragma{}           -> invalid "REWRITE pragmas"

              -- Compiler pragmas are not needed for type checking, thus,
              -- can go to the bottom.
              ForeignPragma{}           -> bottom
              CompilePragma{}           -> bottom

              StaticPragma{}            -> bottom
              InlinePragma{}            -> bottom
              NotProjectionLikePragma{} -> bottom

              ImpossiblePragma{}        -> top     -- error thrown in scope checker
              EtaPragma{}               -> bottom  -- needs record definition
              WarningOnUsage{}          -> top
              WarningOnImport{}         -> top
              InjectivePragma{}         -> top     -- only needs name, not definition
              DisplayPragma{}           -> top     -- only for printing

              -- The attached pragmas have already been handled at this point.
              CatchallPragma{}          -> __IMPOSSIBLE__
              TerminationCheckPragma{}  -> __IMPOSSIBLE__
              NoPositivityCheckPragma{} -> __IMPOSSIBLE__
              PolarityPragma{}          -> __IMPOSSIBLE__
              NoUniverseCheckPragma{}   -> __IMPOSSIBLE__
              NoCoverageCheckPragma{}   -> __IMPOSSIBLE__


        -- -- Pull type signatures to the top
        -- let (sigs, other) = List.partition isTypeSig ds

        -- -- Push definitions to the bottom
        -- let (other, defs) = flip List.partition ds $ \case
        --       FunDef{}         -> False
        --       NiceDataDef{}    -> False
        --       NiceRecDef{}         -> False
        --       NiceFunClause{}  -> False
        --       NicePatternSyn{} -> False
        --       NiceUnquoteDef{} -> False
        --       _ -> True

        -- Compute termination checking flag for mutual block
        tc0 <- use terminationCheckPragma
        let tcs = map termCheck ds
        tc <- combineTerminationChecks r (tc0:tcs)

        -- Compute coverage checking flag for mutual block
        cc0 <- use coverageCheckPragma
        let ccs = map covCheck ds
        let cc = combineCoverageChecks (cc0:ccs)

        -- Compute positivity checking flag for mutual block
        pc0 <- use positivityCheckPragma
        let pcs = map positivityCheckOldMutual ds
        let pc = combinePositivityChecks (pc0:pcs)

        return $ NiceMutual r tc cc pc $ top ++ bottom
        -- return $ NiceMutual r tc pc $ other ++ defs
        -- return $ NiceMutual r tc pc $ sigs ++ other
      where

        -- isTypeSig Axiom{}                     = True
        -- isTypeSig d | LoneSig{} <- declKind d = True
        -- isTypeSig _                           = False

        sigNames  = [ (r, x, k) | LoneSigDecl r k x <- map declKind ds' ]
        defNames  = [ (x, k) | LoneDefs k xs <- map declKind ds', x <- xs ]
        -- compute the set difference with equality just on names
        loneNames = [ (r, x, k) | (r, x, k) <- sigNames, List.all ((x /=) . fst) defNames ]

        termCheck :: NiceDeclaration -> TerminationCheck
        -- Andreas, 2013-02-28 (issue 804):
        -- do not termination check a mutual block if any of its
        -- inner declarations comes with a {-# NO_TERMINATION_CHECK #-}
        termCheck (FunSig _ _ _ _ _ _ tc _ _ _)      = tc
        termCheck (FunDef _ _ _ _ tc _ _ _)          = tc
        -- ASR (28 December 2015): Is this equation necessary?
        termCheck (NiceMutual _ tc _ _ _)            = tc
        termCheck (NiceUnquoteDecl _ _ _ _ tc _ _ _) = tc
        termCheck (NiceUnquoteDef _ _ _ tc _ _ _)    = tc
        termCheck Axiom{}               = TerminationCheck
        termCheck NiceField{}           = TerminationCheck
        termCheck PrimitiveFunction{}   = TerminationCheck
        termCheck NiceModule{}          = TerminationCheck
        termCheck NiceModuleMacro{}     = TerminationCheck
        termCheck NiceOpen{}            = TerminationCheck
        termCheck NiceImport{}          = TerminationCheck
        termCheck NicePragma{}          = TerminationCheck
        termCheck NiceRecSig{}          = TerminationCheck
        termCheck NiceDataSig{}         = TerminationCheck
        termCheck NiceFunClause{}       = TerminationCheck
        termCheck NiceDataDef{}         = TerminationCheck
        termCheck NiceRecDef{}          = TerminationCheck
        termCheck NicePatternSyn{}      = TerminationCheck
        termCheck NiceGeneralize{}      = TerminationCheck
        termCheck NiceLoneConstructor{} = TerminationCheck
        termCheck NiceUnquoteData{}     = TerminationCheck
        termCheck NiceOpaque{}          = TerminationCheck

        covCheck :: NiceDeclaration -> CoverageCheck
        covCheck (FunSig _ _ _ _ _ _ _ cc _ _)      = cc
        covCheck (FunDef _ _ _ _ _ cc _ _)          = cc
        -- ASR (28 December 2015): Is this equation necessary?
        covCheck (NiceMutual _ _ cc _ _)            = cc
        covCheck (NiceUnquoteDecl _ _ _ _ _ cc _ _) = cc
        covCheck (NiceUnquoteDef _ _ _ _ cc _ _)    = cc
        covCheck Axiom{}               = YesCoverageCheck
        covCheck NiceField{}           = YesCoverageCheck
        covCheck PrimitiveFunction{}   = YesCoverageCheck
        covCheck NiceModule{}          = YesCoverageCheck
        covCheck NiceModuleMacro{}     = YesCoverageCheck
        covCheck NiceOpen{}            = YesCoverageCheck
        covCheck NiceImport{}          = YesCoverageCheck
        covCheck NicePragma{}          = YesCoverageCheck
        covCheck NiceRecSig{}          = YesCoverageCheck
        covCheck NiceDataSig{}         = YesCoverageCheck
        covCheck NiceFunClause{}       = YesCoverageCheck
        covCheck NiceDataDef{}         = YesCoverageCheck
        covCheck NiceRecDef{}          = YesCoverageCheck
        covCheck NicePatternSyn{}      = YesCoverageCheck
        covCheck NiceGeneralize{}      = YesCoverageCheck
        covCheck NiceLoneConstructor{} = YesCoverageCheck
        covCheck NiceUnquoteData{}     = YesCoverageCheck
        covCheck NiceOpaque{}          = YesCoverageCheck

        -- ASR (26 December 2015): Do not positivity check a mutual
        -- block if any of its inner declarations comes with a
        -- NO_POSITIVITY_CHECK pragma. See Issue 1614.
        positivityCheckOldMutual :: NiceDeclaration -> PositivityCheck
        positivityCheckOldMutual (NiceDataDef _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (NiceDataSig _ _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (NiceMutual _ _ _ pc _)        = pc
        positivityCheckOldMutual (NiceRecSig _ _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (NiceRecDef _ _ _ pc _ _ _ _ _) = pc
        positivityCheckOldMutual _                              = YesPositivityCheck

        -- A mutual block cannot have a measure,
        -- but it can skip termination check.

    abstractBlock _ [] = return []
    abstractBlock r ds = do
      (ds', anyChange) <- runChangeT $ mkAbstract ds
      let inherited = r == noRange
      if anyChange then return ds' else do
        -- hack to avoid failing on inherited abstract blocks in where clauses
        unless inherited $ declarationWarning $ UselessAbstract r
        return ds -- no change!

    privateBlock _ _ [] = return []
    privateBlock r o ds = do
      (ds', anyChange) <- runChangeT $ mkPrivate o ds
      if anyChange then return ds' else do
        when (o == UserWritten) $ declarationWarning $ UselessPrivate r
        return ds -- no change!

    instanceBlock
      :: Range  -- Range of @instance@ keyword.
      -> [NiceDeclaration]
      -> Nice [NiceDeclaration]
    instanceBlock _ [] = return []
    instanceBlock r ds = do
      let (ds', anyChange) = runChange $ mapM (mkInstance r) ds
      if anyChange then return ds' else do
        declarationWarning $ UselessInstance r
        return ds -- no change!

    -- Make a declaration eligible for instance search.
    mkInstance
      :: Range  -- Range of @instance@ keyword.
      -> Updater NiceDeclaration
    mkInstance r0 = \case
        Axiom r p a i rel x e          -> (\ i -> Axiom r p a i rel x e) <$> setInstance r0 i
        FunSig r p a i m rel tc cc x e -> (\ i -> FunSig r p a i m rel tc cc x e) <$> setInstance r0 i
        NiceUnquoteDecl r p a i tc cc x e -> (\ i -> NiceUnquoteDecl r p a i tc cc x e) <$> setInstance r0 i
        NiceMutual r tc cc pc ds       -> NiceMutual r tc cc pc <$> mapM (mkInstance r0) ds
        NiceLoneConstructor r ds       -> NiceLoneConstructor r <$> mapM (mkInstance r0) ds
        d@NiceFunClause{}              -> return d
        FunDef r ds a i tc cc x cs     -> (\ i -> FunDef r ds a i tc cc x cs) <$> setInstance r0 i
        NiceOpaque r ns i              -> (\ i -> NiceOpaque r ns i) <$> traverse (mkInstance r0) i
        d@NiceField{}                  -> return d  -- Field instance are handled by the parser
        d@PrimitiveFunction{}          -> return d
        d@NiceUnquoteDef{}             -> return d
        d@NiceRecSig{}                 -> return d
        d@NiceDataSig{}                -> return d
        d@NiceModuleMacro{}            -> return d
        d@NiceModule{}                 -> return d
        d@NicePragma{}                 -> return d
        d@NiceOpen{}                   -> return d
        d@NiceImport{}                 -> return d
        d@NiceDataDef{}                -> return d
        d@NiceRecDef{}                 -> return d
        d@NicePatternSyn{}             -> return d
        d@NiceGeneralize{}             -> return d
        d@NiceUnquoteData{}            -> return d

    setInstance
      :: Range  -- Range of @instance@ keyword.
      -> Updater IsInstance
    setInstance r0 = \case
      i@InstanceDef{} -> return i
      _               -> dirty $ InstanceDef r0

    macroBlock r ds = mapM mkMacro ds

    mkMacro :: NiceDeclaration -> Nice NiceDeclaration
    mkMacro = \case
        FunSig r p a i _ rel tc cc x e -> return $ FunSig r p a i MacroDef rel tc cc x e
        d@FunDef{}                     -> return d
        d                              -> declarationException (BadMacroDef d)

-- | Make a declaration abstract.
--
-- Mark computation as 'dirty' if there was a declaration that could be made abstract.
-- If no abstraction is taking place, we want to complain about 'UselessAbstract'.
--
-- Alternatively, we could only flag 'dirty' if a non-abstract thing was abstracted.
-- Then, nested @abstract@s would sometimes also be complained about.

class MakeAbstract a where
  mkAbstract :: UpdaterT Nice a

  default mkAbstract :: (Traversable f, MakeAbstract a', a ~ f a') => UpdaterT Nice a
  mkAbstract = traverse mkAbstract

instance MakeAbstract a => MakeAbstract [a]

-- Leads to overlap with 'WhereClause':
-- instance (Traversable f, MakeAbstract a) => MakeAbstract (f a) where
--   mkAbstract = traverse mkAbstract

instance MakeAbstract IsAbstract where
  mkAbstract = \case
    a@AbstractDef -> return a
    ConcreteDef -> dirty $ AbstractDef

instance MakeAbstract NiceDeclaration where
  mkAbstract = \case
      NiceMutual r termCheck cc pc ds  -> NiceMutual r termCheck cc pc <$> mkAbstract ds
      NiceLoneConstructor r ds         -> NiceLoneConstructor r <$> mkAbstract ds
      FunDef r ds a i tc cc x cs       -> (\ a -> FunDef r ds a i tc cc x) <$> mkAbstract a <*> mkAbstract cs
      NiceDataDef r o a pc uc x ps cs  -> (\ a -> NiceDataDef r o a pc uc x ps) <$> mkAbstract a <*> mkAbstract cs
      NiceRecDef r o a pc uc x dir ps cs -> (\ a -> NiceRecDef r o a pc uc x dir ps cs) <$> mkAbstract a
      NiceFunClause r p a tc cc catchall d  -> (\ a -> NiceFunClause r p a tc cc catchall d) <$> mkAbstract a
      -- The following declarations have an @InAbstract@ field
      -- but are not really definitions, so we do count them into
      -- the declarations which can be made abstract
      -- (thus, do not notify progress with @dirty@).
      Axiom r p a i rel x e          -> return $ Axiom             r p AbstractDef i rel x e
      FunSig r p a i m rel tc cc x e -> return $ FunSig            r p AbstractDef i m rel tc cc x e
      NiceRecSig  r er p a pc uc x ls t -> return $ NiceRecSig  r er p AbstractDef pc uc x ls t
      NiceDataSig r er p a pc uc x ls t -> return $ NiceDataSig r er p AbstractDef pc uc x ls t
      NiceField r p _ i tac x e      -> return $ NiceField         r p AbstractDef i tac x e
      PrimitiveFunction r p _ x e    -> return $ PrimitiveFunction r p AbstractDef x e
      -- Andreas, 2016-07-17 it does have effect on unquoted defs.
      -- Need to set updater state to dirty!
      NiceUnquoteDecl r p _ i tc cc x e -> tellDirty $> NiceUnquoteDecl r p AbstractDef i tc cc x e
      NiceUnquoteDef r p _ tc cc x e    -> tellDirty $> NiceUnquoteDef r p AbstractDef tc cc x e
      NiceUnquoteData r p _ tc cc x xs e -> tellDirty $> NiceUnquoteData r p AbstractDef tc cc x xs e
      d@NiceModule{}                 -> return d
      d@NiceModuleMacro{}            -> return d
      d@NicePragma{}                 -> return d
      d@(NiceOpen _ _ directives)              -> do
        whenJust (publicOpen directives) $ lift . declarationWarning . OpenPublicAbstract
        return d
      d@NiceImport{}                 -> return d
      d@NicePatternSyn{}             -> return d
      d@NiceGeneralize{}             -> return d
      NiceOpaque r ns ds             -> NiceOpaque r ns <$> mkAbstract ds

instance MakeAbstract Clause where
  mkAbstract (Clause x catchall lhs rhs wh with) = do
    Clause x catchall lhs rhs <$> mkAbstract wh <*> mkAbstract with

-- | Contents of a @where@ clause are abstract if the parent is.
instance MakeAbstract WhereClause where
  mkAbstract  NoWhere               = return $ NoWhere
  mkAbstract (AnyWhere r ds)        = dirty $ AnyWhere r
                                                [Abstract noRange ds]
  mkAbstract (SomeWhere r e m a ds) = dirty $ SomeWhere r e m a
                                                [Abstract noRange ds]

-- | Make a declaration private.
--
-- Andreas, 2012-11-17:
-- Mark computation as 'dirty' if there was a declaration that could be privatized.
-- If no privatization is taking place, we want to complain about 'UselessPrivate'.
--
-- Alternatively, we could only flag 'dirty' if a non-private thing was privatized.
-- Then, nested @private@s would sometimes also be complained about.

class MakePrivate a where
  mkPrivate :: Origin -> UpdaterT Nice a

  default mkPrivate :: (Traversable f, MakePrivate a', a ~ f a') => Origin -> UpdaterT Nice a
  mkPrivate o = traverse $ mkPrivate o

instance MakePrivate a => MakePrivate [a]

-- Leads to overlap with 'WhereClause':
-- instance (Traversable f, MakePrivate a) => MakePrivate (f a) where
--   mkPrivate = traverse mkPrivate

instance MakePrivate Access where
  mkPrivate o = \case
    p@PrivateAccess{} -> return p  -- OR? return $ PrivateAccess o
    _                 -> dirty $ PrivateAccess o

instance MakePrivate NiceDeclaration where
  mkPrivate o = \case
      Axiom r p a i rel x e                    -> (\ p -> Axiom r p a i rel x e)                <$> mkPrivate o p
      NiceField r p a i tac x e                -> (\ p -> NiceField r p a i tac x e)            <$> mkPrivate o p
      PrimitiveFunction r p a x e              -> (\ p -> PrimitiveFunction r p a x e)          <$> mkPrivate o p
      NiceMutual r tc cc pc ds                 -> (\ ds-> NiceMutual r tc cc pc ds)             <$> mkPrivate o ds
      NiceLoneConstructor r ds                 -> NiceLoneConstructor r                         <$> mkPrivate o ds
      NiceModule r p a e x tel ds              -> (\ p -> NiceModule r p a e x tel ds)          <$> mkPrivate o p
      NiceModuleMacro r p e x ma op is         -> (\ p -> NiceModuleMacro r p e x ma op is)     <$> mkPrivate o p
      FunSig r p a i m rel tc cc x e           -> (\ p -> FunSig r p a i m rel tc cc x e)       <$> mkPrivate o p
      NiceRecSig r er p a pc uc x ls t         -> (\ p -> NiceRecSig r er p a pc uc x ls t)     <$> mkPrivate o p
      NiceDataSig r er p a pc uc x ls t        -> (\ p -> NiceDataSig r er p a pc uc x ls t)    <$> mkPrivate o p
      NiceFunClause r p a tc cc catchall d     -> (\ p -> NiceFunClause r p a tc cc catchall d) <$> mkPrivate o p
      NiceUnquoteDecl r p a i tc cc x e        -> (\ p -> NiceUnquoteDecl r p a i tc cc x e)    <$> mkPrivate o p
      NiceUnquoteDef r p a tc cc x e           -> (\ p -> NiceUnquoteDef r p a tc cc x e)       <$> mkPrivate o p
      NicePatternSyn r p x xs p'               -> (\ p -> NicePatternSyn r p x xs p')           <$> mkPrivate o p
      NiceGeneralize r p i tac x t             -> (\ p -> NiceGeneralize r p i tac x t)         <$> mkPrivate o p
      NiceOpaque r ns ds                       -> (\ p -> NiceOpaque r ns p)                    <$> mkPrivate o ds
      d@NicePragma{}                           -> return d
      d@(NiceOpen _ _ directives)              -> do
        whenJust (publicOpen directives) $ lift . declarationWarning . OpenPublicPrivate
        return d
      d@NiceImport{}                           -> return d
      -- Andreas, 2016-07-08, issue #2089
      -- we need to propagate 'private' to the named where modules
      FunDef r ds a i tc cc x cls              -> FunDef r ds a i tc cc x <$> mkPrivate o cls
      d@NiceDataDef{}                          -> return d
      d@NiceRecDef{}                           -> return d
      d@NiceUnquoteData{}                      -> return d

instance MakePrivate Clause where
  mkPrivate o (Clause x catchall lhs rhs wh with) = do
    Clause x catchall lhs rhs <$> mkPrivate o wh <*> mkPrivate o with

instance MakePrivate WhereClause where
  mkPrivate o = \case
    d@NoWhere    -> return d
    -- @where@-declarations are protected behind an anonymous module,
    -- thus, they are effectively private by default.
    d@AnyWhere{} -> return d
    -- Andreas, 2016-07-08
    -- A @where@-module is private if the parent function is private.
    -- The contents of this module are not private, unless declared so!
    -- Thus, we do not recurse into the @ds@ (could not anyway).
    SomeWhere r e m a ds ->
      mkPrivate o a <&> \a' -> SomeWhere r e m a' ds

-- The following function is (at the time of writing) only used three
-- times: for building Lets, and for printing error messages.

-- | (Approximately) convert a 'NiceDeclaration' back to a list of
-- 'Declaration's.
notSoNiceDeclarations :: NiceDeclaration -> [Declaration]
notSoNiceDeclarations = \case
    Axiom _ _ _ i rel x e          -> inst i [TypeSig rel Nothing x e]
    NiceField _ _ _ i tac x argt   -> [FieldSig i tac x argt]
    PrimitiveFunction r _ _ x e    -> [Primitive r [TypeSig (argInfo e) Nothing x (unArg e)]]
    NiceMutual r _ _ _ ds          -> [Mutual r $ concatMap notSoNiceDeclarations ds]
    NiceLoneConstructor r ds       -> [LoneConstructor r $ concatMap notSoNiceDeclarations ds]
    NiceModule r _ _ e x tel ds    -> [Module r e x tel ds]
    NiceModuleMacro r _ e x ma o dir
                                   -> [ModuleMacro r e x ma o dir]
    NiceOpen r x dir               -> [Open r x dir]
    NiceImport r x as o dir        -> [Import r x as o dir]
    NicePragma _ p                 -> [Pragma p]
    NiceRecSig r er _ _ _ _ x bs e -> [RecordSig r er x bs e]
    NiceDataSig r er _ _ _ _ x bs e -> [DataSig r er x bs e]
    NiceFunClause _ _ _ _ _ _ d    -> [d]
    FunSig _ _ _ i _ rel _ _ x e   -> inst i [TypeSig rel Nothing x e]
    FunDef _ ds _ _ _ _ _ _        -> ds
    NiceDataDef r _ _ _ _ x bs cs  -> [DataDef r x bs $ concatMap notSoNiceDeclarations cs]
    NiceRecDef r _ _ _ _ x dir bs ds -> [RecordDef r x dir bs ds]
    NicePatternSyn r _ n as p      -> [PatternSyn r n as p]
    NiceGeneralize r _ i tac n e   -> [Generalize r [TypeSig i tac n e]]
    NiceUnquoteDecl r _ _ i _ _ x e -> inst i [UnquoteDecl r x e]
    NiceUnquoteDef r _ _ _ _ x e    -> [UnquoteDef r x e]
    NiceUnquoteData r _ _ _ _ x xs e  -> [UnquoteData r x xs e]
    NiceOpaque r ns ds                -> [Opaque r (Unfolding r ns:concatMap notSoNiceDeclarations ds)]
  where
    inst (InstanceDef r) ds = [InstanceB r ds]
    inst NotInstanceDef  ds = ds

-- | Has the 'NiceDeclaration' a field of type 'IsAbstract'?
niceHasAbstract :: NiceDeclaration -> Maybe IsAbstract
niceHasAbstract = \case
    Axiom{}                       -> Nothing
    NiceField _ _ a _ _ _ _       -> Just a
    PrimitiveFunction _ _ a _ _   -> Just a
    NiceMutual{}                  -> Nothing
    NiceLoneConstructor{}         -> Nothing
    NiceModule _ _ a _ _ _ _      -> Just a
    NiceModuleMacro{}             -> Nothing
    NiceOpen{}                    -> Nothing
    NiceImport{}                  -> Nothing
    NicePragma{}                  -> Nothing
    NiceRecSig{}                  -> Nothing
    NiceDataSig{}                 -> Nothing
    NiceFunClause _ _ a _ _ _ _   -> Just a
    FunSig{}                      -> Nothing
    FunDef _ _ a _ _ _ _ _        -> Just a
    NiceDataDef _ _ a _ _ _ _ _   -> Just a
    NiceRecDef _ _ a _ _ _ _ _ _ -> Just a
    NicePatternSyn{}              -> Nothing
    NiceGeneralize{}              -> Nothing
    NiceUnquoteDecl _ _ a _ _ _ _ _ -> Just a
    NiceUnquoteDef _ _ a _ _ _ _    -> Just a
    NiceUnquoteData _ _ a _ _ _ _ _ -> Just a
    NiceOpaque{}                    -> Nothing
