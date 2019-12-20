{-# LANGUAGE NondecreasingIndentation #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Errors
  ( prettyError
  , prettyWarning
  , tcErrString
  , prettyTCWarnings'
  , prettyTCWarnings
  , tcWarningsToError
  , applyFlagsToTCWarnings'
  , applyFlagsToTCWarnings
  , dropTopLevelModule
  , topLevelModuleDropper
  , stringTCErr
  ) where

import Prelude hiding ( null )

import Data.Function
import Data.List (sortBy, isInfixOf, dropWhileEnd)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Char (toLower)
import qualified Data.Set as Set
import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Pretty (prettyHiding, prettyRelevance)
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Scope.Monad (isDatatypeModule)
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.SizedTypes ( sizeType )
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Call
import Agda.TypeChecking.Pretty.Warning
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope ( ifPiType )
import Agda.TypeChecking.Reduce (instantiate)

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.FileName
import Agda.Utils.Float  ( toStringWithoutDotZero )
import Agda.Utils.Function
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Top level function
---------------------------------------------------------------------------

{-# SPECIALIZE prettyError :: TCErr -> TCM String #-}
prettyError :: MonadTCM tcm => TCErr -> tcm String
prettyError err = liftTCM $ show <$> prettyError' err []
  where
  prettyError' :: TCErr -> [TCErr] -> TCM Doc
  prettyError' err errs
    | length errs > 3 = fsep (
        pwords "total panic: error when printing error from printing error from printing error." ++
        pwords "I give up! Approximations of errors (original error last):" )
        $$ vcat (map (text . tcErrString) errs)
    | otherwise = applyUnless (null errs) ("panic: error when printing error!" $$) $ do
        (prettyTCM err $$ vcat (map (text . ("when printing error " ++) . tcErrString) errs))
        `catchError` \ err' -> prettyError' err' (err:errs)

---------------------------------------------------------------------------
-- * Helpers
---------------------------------------------------------------------------

panic :: Monad m => String -> m Doc
panic s = fwords $ "Panic: " ++ s

nameWithBinding :: MonadPretty m => QName -> m Doc
nameWithBinding q =
  (prettyTCM q <+> "bound at") <?> prettyTCM r
  where
    r = nameBindingSite $ qnameName q

tcErrString :: TCErr -> String
tcErrString err = show (getRange err) ++ " " ++ case err of
  TypeError _ cl    -> errorString $ clValue cl
  Exception r s     -> show r ++ " " ++ show s
  IOException _ r e -> show r ++ " " ++ show e
  PatternErr{}      -> "PatternErr"

stringTCErr :: String -> TCErr
stringTCErr = Exception noRange . P.text

errorString :: TypeError -> String
errorString err = case err of
  AmbiguousModule{}                        -> "AmbiguousModule"
  AmbiguousName{}                          -> "AmbiguousName"
  AmbiguousParseForApplication{}           -> "AmbiguousParseForApplication"
  AmbiguousParseForLHS{}                   -> "AmbiguousParseForLHS"
--  AmbiguousParseForPatternSynonym{}        -> "AmbiguousParseForPatternSynonym"
  AmbiguousTopLevelModuleName {}           -> "AmbiguousTopLevelModuleName"
  BadArgumentsToPatternSynonym{}           -> "BadArgumentsToPatternSynonym"
  TooFewArgumentsToPatternSynonym{}        -> "TooFewArgumentsToPatternSynonym"
  CannotResolveAmbiguousPatternSynonym{}   -> "CannotResolveAmbiguousPatternSynonym"
  BothWithAndRHS                           -> "BothWithAndRHS"
  BuiltinInParameterisedModule{}           -> "BuiltinInParameterisedModule"
  BuiltinMustBeConstructor{}               -> "BuiltinMustBeConstructor"
  ClashingDefinition{}                     -> "ClashingDefinition"
  ClashingFileNamesFor{}                   -> "ClashingFileNamesFor"
  ClashingImport{}                         -> "ClashingImport"
  ClashingModule{}                         -> "ClashingModule"
  ClashingModuleImport{}                   -> "ClashingModuleImport"
  CompilationError{}                       -> "CompilationError"
  ConstructorPatternInWrongDatatype{}      -> "ConstructorPatternInWrongDatatype"
  CyclicModuleDependency{}                 -> "CyclicModuleDependency"
  DataMustEndInSort{}                      -> "DataMustEndInSort"
-- UNUSED:    DataTooManyParameters{}                  -> "DataTooManyParameters"
  CantResolveOverloadedConstructorsTargetingSameDatatype{} -> "CantResolveOverloadedConstructorsTargetingSameDatatype"
  DoesNotConstructAnElementOf{}            -> "DoesNotConstructAnElementOf"
  DuplicateBuiltinBinding{}                -> "DuplicateBuiltinBinding"
  DuplicateConstructors{}                  -> "DuplicateConstructors"
  DuplicateFields{}                        -> "DuplicateFields"
  DuplicateImports{}                       -> "DuplicateImports"
  FieldOutsideRecord                       -> "FieldOutsideRecord"
  FileNotFound{}                           -> "FileNotFound"
  GenericError{}                           -> "GenericError"
  GenericDocError{}                        -> "GenericDocError"
  InstanceNoCandidate{}                    -> "InstanceNoCandidate"
  IlltypedPattern{}                        -> "IlltypedPattern"
  IllformedProjectionPattern{}             -> "IllformedProjectionPattern"
  CannotEliminateWithPattern{}             -> "CannotEliminateWithPattern"
  IllegalLetInTelescope{}                  -> "IllegalLetInTelescope"
  IllegalPatternInTelescope{}              -> "IllegalPatternInTelescope"
-- UNUSED:  IncompletePatternMatching{}              -> "IncompletePatternMatching"
  InternalError{}                          -> "InternalError"
  InvalidPattern{}                         -> "InvalidPattern"
  LocalVsImportedModuleClash{}             -> "LocalVsImportedModuleClash"
  MetaCannotDependOn{}                     -> "MetaCannotDependOn"
  MetaOccursInItself{}                     -> "MetaOccursInItself"
  MetaIrrelevantSolution{}                 -> "MetaIrrelevantSolution"
  MetaErasedSolution{}                     -> "MetaErasedSolution"
  ModuleArityMismatch{}                    -> "ModuleArityMismatch"
  ModuleDefinedInOtherFile {}              -> "ModuleDefinedInOtherFile"
  ModuleNameUnexpected{}                   -> "ModuleNameUnexpected"
  ModuleNameDoesntMatchFileName {}         -> "ModuleNameDoesntMatchFileName"
  NeedOptionCopatterns{}                   -> "NeedOptionCopatterns"
  NeedOptionRewriting{}                    -> "NeedOptionRewriting"
  NeedOptionProp{}                         -> "NeedOptionProp"
  GeneralizeNotSupportedHere{}             -> "GeneralizeNotSupportedHere"
  GeneralizeCyclicDependency{}             -> "GeneralizeCyclicDependency"
  GeneralizeUnsolvedMeta{}                 -> "GeneralizeUnsolvedMeta"
  MultipleFixityDecls{}                    -> "MultipleFixityDecls"
  MultiplePolarityPragmas{}                -> "MultiplePolarityPragmas"
  NoBindingForBuiltin{}                    -> "NoBindingForBuiltin"
  NoParseForApplication{}                  -> "NoParseForApplication"
  NoParseForLHS{}                          -> "NoParseForLHS"
--  NoParseForPatternSynonym{}               -> "NoParseForPatternSynonym"
  NoRHSRequiresAbsurdPattern{}             -> "NoRHSRequiresAbsurdPattern"
  NoSuchBuiltinName{}                      -> "NoSuchBuiltinName"
  NoSuchModule{}                           -> "NoSuchModule"
  DuplicatePrimitiveBinding{}              -> "DuplicatePrimitiveBinding"
  NoSuchPrimitiveFunction{}                -> "NoSuchPrimitiveFunction"
  NotAModuleExpr{}                         -> "NotAModuleExpr"
  NotAProperTerm                           -> "NotAProperTerm"
  InvalidType{}                            -> "InvalidType"
  InvalidTypeSort{}                        -> "InvalidTypeSort"
  FunctionTypeInSizeUniv{}                 -> "FunctionTypeInSizeUniv"
  NotAValidLetBinding{}                    -> "NotAValidLetBinding"
  NotValidBeforeField{}                    -> "NotValidBeforeField"
  NotAnExpression{}                        -> "NotAnExpression"
  NotImplemented{}                         -> "NotImplemented"
  NotSupported{}                           -> "NotSupported"
  AbstractConstructorNotInScope{}          -> "AbstractConstructorNotInScope"
  NotInScope{}                             -> "NotInScope"
  NotLeqSort{}                             -> "NotLeqSort"
  NothingAppliedToHiddenArg{}              -> "NothingAppliedToHiddenArg"
  NothingAppliedToInstanceArg{}            -> "NothingAppliedToInstanceArg"
  OverlappingProjects {}                   -> "OverlappingProjects"
  OperatorInformation {}                   -> "OperatorInformation"
  PatternShadowsConstructor {}             -> "PatternShadowsConstructor"
  PropMustBeSingleton                      -> "PropMustBeSingleton"
  RepeatedVariablesInPattern{}             -> "RepeatedVariablesInPattern"
  ShadowedModule{}                         -> "ShadowedModule"
  ShouldBeASort{}                          -> "ShouldBeASort"
  ShouldBeApplicationOf{}                  -> "ShouldBeApplicationOf"
  ShouldBeAppliedToTheDatatypeParameters{} -> "ShouldBeAppliedToTheDatatypeParameters"
  ShouldBeEmpty{}                          -> "ShouldBeEmpty"
  ShouldBePi{}                             -> "ShouldBePi"
  ShouldBePath{}                           -> "ShouldBePath"
  ShouldBeRecordType{}                     -> "ShouldBeRecordType"
  ShouldBeRecordPattern{}                  -> "ShouldBeRecordPattern"
  NotAProjectionPattern{}                  -> "NotAProjectionPattern"
  ShouldEndInApplicationOfTheDatatype{}    -> "ShouldEndInApplicationOfTheDatatype"
  SplitError{}                             -> "SplitError"
  ImpossibleConstructor{}                  -> "ImpossibleConstructor"
  TooManyFields{}                          -> "TooManyFields"
  TooManyPolarities{}                      -> "TooManyPolarities"
  SplitOnIrrelevant{}                      -> "SplitOnIrrelevant"
  SplitOnUnusableCohesion{}                -> "SplitOnUnusableCohesion"
  -- UNUSED: -- SplitOnErased{}                          -> "SplitOnErased"
  SplitOnNonVariable{}                     -> "SplitOnNonVariable"
  DefinitionIsIrrelevant{}                 -> "DefinitionIsIrrelevant"
  DefinitionIsErased{}                     -> "DefinitionIsErased"
  VariableIsIrrelevant{}                   -> "VariableIsIrrelevant"
  VariableIsErased{}                       -> "VariableIsErased"
  VariableIsOfUnusableCohesion{}           -> "VariableIsOfUnusableCohesion"
  UnequalBecauseOfUniverseConflict{}       -> "UnequalBecauseOfUniverseConflict"
  UnequalRelevance{}                       -> "UnequalRelevance"
  UnequalQuantity{}                        -> "UnequalQuantity"
  UnequalHiding{}                          -> "UnequalHiding"
  UnequalLevel{}                           -> "UnequalLevel"
  UnequalSorts{}                           -> "UnequalSorts"
  UnequalTerms{}                           -> "UnequalTerms"
  UnequalTypes{}                           -> "UnequalTypes"
--  UnequalTelescopes{}                      -> "UnequalTelescopes" -- UNUSED
  WithOnFreeVariable{}                     -> "WithOnFreeVariable"
  UnexpectedWithPatterns{}                 -> "UnexpectedWithPatterns"
  UninstantiatedDotPattern{}               -> "UninstantiatedDotPattern"
  ForcedConstructorNotInstantiated{}       -> "ForcedConstructorNotInstantiated"
  SolvedButOpenHoles{}                     -> "SolvedButOpenHoles"
  UnusedVariableInPatternSynonym           -> "UnusedVariableInPatternSynonym"
  UnquoteFailed{}                          -> "UnquoteFailed"
  DeBruijnIndexOutOfScope{}                -> "DeBruijnIndexOutOfScope"
  WithClausePatternMismatch{}              -> "WithClausePatternMismatch"
  WrongHidingInApplication{}               -> "WrongHidingInApplication"
  WrongHidingInLHS{}                       -> "WrongHidingInLHS"
  WrongHidingInLambda{}                    -> "WrongHidingInLambda"
  WrongIrrelevanceInLambda{}               -> "WrongIrrelevanceInLambda"
  WrongQuantityInLambda{}                  -> "WrongQuantityInLambda"
  WrongCohesionInLambda{}                  -> "WrongCohesionInLambda"
  WrongNamedArgument{}                     -> "WrongNamedArgument"
  WrongNumberOfConstructorArguments{}      -> "WrongNumberOfConstructorArguments"
  QuantityMismatch{}                       -> "QuantityMismatch"
  HidingMismatch{}                         -> "HidingMismatch"
  RelevanceMismatch{}                      -> "RelevanceMismatch"
  NonFatalErrors{}                         -> "NonFatalErrors"
  InstanceSearchDepthExhausted{}           -> "InstanceSearchDepthExhausted"
  TriedToCopyConstrainedPrim{}             -> "TriedToCopyConstrainedPrim"

instance PrettyTCM TCErr where
  prettyTCM err = case err of
    -- Gallais, 2016-05-14
    -- Given where `NonFatalErrors` are created, we know for a
    -- fact that ̀ws` is non-empty.
    TypeError _ Closure{ clValue = NonFatalErrors ws } -> foldr1 ($$) $ fmap prettyTCM ws
    -- Andreas, 2014-03-23
    -- This use of withTCState seems ok since we do not collect
    -- Benchmark info during printing errors.
    TypeError s e -> withTCState (const s) $
      sayWhen (envRange $ clEnv e) (envCall $ clEnv e) $ prettyTCM e
    Exception r s     -> sayWhere r $ return s
    IOException _ r e -> sayWhere r $ fwords $ show e
    PatternErr{}      -> sayWhere err $ panic "uncaught pattern violation"

-- | Drops given amount of leading components of the qualified name.
dropTopLevelModule' :: Int -> QName -> QName
dropTopLevelModule' k (QName (MName ns) n) = QName (MName (drop k ns)) n

-- | Drops the filename component of the qualified name.
dropTopLevelModule :: QName -> TCM QName
dropTopLevelModule q = ($ q) <$> topLevelModuleDropper

-- | Produces a function which drops the filename component of the qualified name.
topLevelModuleDropper :: (MonadTCEnv m, ReadTCState m) => m (QName -> QName)
topLevelModuleDropper = do
  caseMaybeM (asksTC envCurrentPath) (return id) $ \ f -> do
  m <- fromMaybe __IMPOSSIBLE__ <$> lookupModuleFromSource f
  return $ dropTopLevelModule' $ size m

instance PrettyTCM TypeError where
  prettyTCM err = case err of
    InternalError s -> panic s

    NotImplemented s -> fwords $ "Not implemented: " ++ s

    NotSupported s -> fwords $ "Not supported: " ++ s

    CompilationError s -> sep [fwords "Compilation error:", text s]

    GenericError s -> fwords s

    GenericDocError d -> return d

    PropMustBeSingleton -> fwords
      "Datatypes in Prop must have at most one constructor when proof irrelevance is enabled"

    DataMustEndInSort t -> fsep $
      pwords "The type of a datatype must end in a sort."
      ++ [prettyTCM t] ++ pwords "isn't a sort."

{- UNUSED:
    DataTooManyParameters -> fsep $ pwords "Too many parameters given to data type."
-}

    ShouldEndInApplicationOfTheDatatype t -> fsep $
      pwords "The target of a constructor must be the datatype applied to its parameters,"
      ++ [prettyTCM t] ++ pwords "isn't"

    ShouldBeAppliedToTheDatatypeParameters s t -> fsep $
      pwords "The target of the constructor should be" ++ [prettyTCM s] ++
      pwords "instead of" ++ [prettyTCM t]

    ShouldBeApplicationOf t q -> fsep $
      pwords "The pattern constructs an element of" ++ [prettyTCM q] ++
      pwords "which is not the right datatype"

    ShouldBeRecordType t -> fsep $
      pwords "Expected non-abstract record type, found " ++ [prettyTCM t]

    ShouldBeRecordPattern p -> fsep $
      pwords "Expected record pattern" -- ", found " ++ [prettyTCM p]

    NotAProjectionPattern p -> fsep $
      pwords "Not a valid projection for a copattern: " ++ [ prettyA p ]

    WrongHidingInLHS -> fwords "Unexpected implicit argument"

    WrongHidingInLambda t ->
      fwords "Found an implicit lambda where an explicit lambda was expected"

    WrongIrrelevanceInLambda ->
      fwords "Found a non-strict lambda where a irrelevant lambda was expected"

    WrongQuantityInLambda ->
      fwords "Incorrect quantity annotation in lambda"

    WrongCohesionInLambda ->
      fwords "Incorrect cohesion annotation in lambda"

    WrongNamedArgument a xs0 -> fsep $
      pwords "Function does not accept argument "
      ++ [prettyTCM a] -- ++ pwords " (wrong argument name)"
      ++ if null xs then [] else
         [parens $ fsep $ text "possible arguments:" : map pretty xs]
      where
      xs = filter (not . isNoName) xs0

    WrongHidingInApplication t ->
      fwords "Found an implicit application where an explicit application was expected"

    HidingMismatch h h' -> fwords $
      "Expected " ++ verbalize (Indefinite h') ++ " argument, but found " ++
      verbalize (Indefinite h) ++ " argument"

    RelevanceMismatch r r' -> fwords $
      "Expected " ++ verbalize (Indefinite r') ++ " argument, but found " ++
      verbalize (Indefinite r) ++ " argument"

    QuantityMismatch q q' -> fwords $
      "Expected " ++ verbalize (Indefinite q') ++ " argument, but found " ++
      verbalize (Indefinite q) ++ " argument"

    UninstantiatedDotPattern e -> fsep $
      pwords "Failed to infer the value of dotted pattern"

    ForcedConstructorNotInstantiated p -> fsep $
      pwords "Failed to infer that constructor pattern "
      ++ [prettyA p] ++ pwords " is forced"

    IlltypedPattern p a -> do
      let ho _ _ = fsep $ pwords "Cannot pattern match on functions"
      ifPiType a ho $ {- else -} \ _ -> do
        fsep $ pwords "Type mismatch"

    IllformedProjectionPattern p -> fsep $
      pwords "Ill-formed projection pattern " ++ [prettyA p]

    CannotEliminateWithPattern p a -> do
      let isProj = isJust (isProjP p)
      fsep $
        pwords "Cannot eliminate type" ++ prettyTCM a : if
         | isProj -> pwords "with projection pattern" ++ [prettyA p]
         | A.ProjP _ _ f <- namedArg p -> pwords "with pattern" ++ [prettyA p] ++
             pwords "(suggestion: write" ++ [".(" <> prettyA (A.Proj ProjPrefix f) <> ")"] ++ pwords "for a dot pattern," ++
             pwords "or remove the braces for a postfix projection)"
         | otherwise ->
             "with" : text (kindOfPattern (namedArg p)) : "pattern" : prettyA p :
             pwords "(did you supply too many arguments?)"
      where
      kindOfPattern = \case
        A.VarP{}    -> "variable"
        A.ConP{}    -> "constructor"
        A.ProjP{}   -> __IMPOSSIBLE__
        A.DefP{}    -> __IMPOSSIBLE__
        A.WildP{}   -> "wildcard"
        A.DotP{}    -> "dot"
        A.AbsurdP{} -> "absurd"
        A.LitP{}    -> "literal"
        A.RecP{}    -> "record"
        A.WithP{}   -> "with"
        A.EqualP{}  -> "equality"
        A.AsP _ _ p -> kindOfPattern p
        A.PatternSynP{} -> __IMPOSSIBLE__

    WrongNumberOfConstructorArguments c expect given -> fsep $
      pwords "The constructor" ++ [prettyTCM c] ++
      pwords "expects" ++ [prettyTCM expect] ++
      pwords "arguments (including hidden ones), but has been given"
      ++ [prettyTCM given] ++ pwords "(including hidden ones)"

    CantResolveOverloadedConstructorsTargetingSameDatatype d cs -> fsep $
      pwords "Can't resolve overloaded constructors targeting the same datatype"
      ++ [(parens $ prettyTCM (qnameToConcrete d)) <> colon]
      ++ map pretty cs

    DoesNotConstructAnElementOf c t -> fsep $
      pwords "The constructor" ++ [prettyTCM c] ++
      pwords "does not construct an element of" ++ [prettyTCM t]

    ConstructorPatternInWrongDatatype c d -> fsep $
      [prettyTCM c] ++ pwords "is not a constructor of the datatype"
      ++ [prettyTCM d]

    ShadowedModule x [] -> __IMPOSSIBLE__

    ShadowedModule x ms@(m0 : _) -> do
      -- Clash! Concrete module name x already points to the abstract names ms.
      (r, m) <- do
        -- Andreas, 2017-07-28, issue #719.
        -- First, we try to find whether one of the abstract names @ms@ points back to @x@
        scope <- getScope
        -- Get all pairs (y,m) such that y points to some m ∈ ms.
        let xms0 = ms >>= \ m -> map (,m) $ inverseScopeLookupModule m scope
        reportSLn "scope.clash.error" 30 $ "candidates = " ++ prettyShow xms0

        -- Try to find x (which will have a different Range, if it has one (#2649)).
        let xms = filter ((\ y -> not (null $ getRange y) && y == C.QName x) . fst) xms0
        reportSLn "scope.class.error" 30 $ "filtered candidates = " ++ prettyShow xms

        -- If we found a copy of x with non-empty range, great!
        ifJust (listToMaybe xms) (\ (x', m) -> return (getRange x', m)) $ {-else-} do

        -- If that failed, we pick the first m from ms which has a nameBindingSite.
        let rms = ms >>= \ m -> map (,m) $
              filter (noRange /=) $ map nameBindingSite $ reverse $ mnameToList m
              -- Andreas, 2017-07-25, issue #2649
              -- Take the first nameBindingSite we can get hold of.
        reportSLn "scope.class.error" 30 $ "rangeful clashing modules = " ++ prettyShow rms

        -- If even this fails, we pick the first m and give no range.
        return $ fromMaybe (noRange, m0) $ listToMaybe rms

      fsep $
        pwords "Duplicate definition of module" ++ [prettyTCM x <> "."] ++
        pwords "Previous definition of" ++ [help m] ++ pwords "module" ++ [prettyTCM x] ++
        pwords "at" ++ [prettyTCM r]
      where
        help m = caseMaybeM (isDatatypeModule m) empty $ \case
          IsData   -> "(datatype)"
          IsRecord -> "(record)"

    ModuleArityMismatch m EmptyTel args -> fsep $
      pwords "The module" ++ [prettyTCM m] ++
      pwords "is not parameterized, but is being applied to arguments"

    ModuleArityMismatch m tel@(ExtendTel _ _) args -> fsep $
      pwords "The arguments to " ++ [prettyTCM m] ++ pwords "do not fit the telescope" ++
      [prettyTCM tel]

    ShouldBeEmpty t [] -> fsep $
       [prettyTCM t] ++ pwords "should be empty, but that's not obvious to me"

    ShouldBeEmpty t ps -> fsep (
      [prettyTCM t] ++
      pwords "should be empty, but the following constructor patterns are valid:"
      ) $$ nest 2 (vcat $ map (prettyPat 0) ps)

    ShouldBeASort t -> fsep $
      [prettyTCM t] ++ pwords "should be a sort, but it isn't"

    ShouldBePi t -> fsep $
      [prettyTCM t] ++ pwords "should be a function type, but it isn't"

    ShouldBePath t -> fsep $
      [prettyTCM t] ++ pwords "should be a Path or PathP type, but it isn't"

    NotAProperTerm -> fwords "Found a malformed term"

    InvalidTypeSort s -> fsep $ [prettyTCM s] ++ pwords "is not a valid type"
    InvalidType v -> fsep $ [prettyTCM v] ++ pwords "is not a valid type"

    FunctionTypeInSizeUniv v -> fsep $
      pwords "Functions may not return sizes, thus, function type " ++
      [ prettyTCM v ] ++ pwords " is illegal"

    SplitOnIrrelevant t -> fsep $
      pwords "Cannot pattern match against" ++ [text $ verbalize $ getRelevance t] ++
      pwords "argument of type" ++ [prettyTCM $ unDom t]

    SplitOnUnusableCohesion t -> fsep $
      pwords "Cannot pattern match against" ++ [text $ verbalize $ getCohesion t] ++
      pwords "argument of type" ++ [prettyTCM $ unDom t]

    -- UNUSED:
    -- SplitOnErased t -> fsep $
    --   pwords "Cannot pattern match against" ++ [text $ verbalize $ getQuantity t] ++
    --   pwords "argument of type" ++ [prettyTCM $ unDom t]

    SplitOnNonVariable v t -> fsep $
      pwords "Cannot pattern match because the (refined) argument " ++
      [ prettyTCM v ] ++ pwords " is not a variable."

    DefinitionIsIrrelevant x -> fsep $
      "Identifier" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"

    DefinitionIsErased x -> fsep $
      "Identifier" : prettyTCM x : pwords "is declared erased, so it cannot be used here"

    VariableIsIrrelevant x -> fsep $
      "Variable" : prettyTCM (nameConcrete x) : pwords "is declared irrelevant, so it cannot be used here"

    VariableIsErased x -> fsep $
      "Variable" : prettyTCM (nameConcrete x) : pwords "is declared erased, so it cannot be used here"

    VariableIsOfUnusableCohesion x c -> fsep
      ["Variable", prettyTCM (nameConcrete x), "is declared", text (show c), "so it cannot be used here"]

    UnequalBecauseOfUniverseConflict cmp s t -> fsep $
      [prettyTCM s, notCmp cmp, prettyTCM t, "because this would result in an invalid use of Setω" ]

    UnequalTerms cmp s t a -> case (s,t) of
      (Sort s1      , Sort s2      )
        | CmpEq  <- cmp              -> prettyTCM $ UnequalSorts s1 s2
        | CmpLeq <- cmp              -> prettyTCM $ NotLeqSort s1 s2
      (Sort MetaS{} , t            ) -> prettyTCM $ ShouldBeASort $ El Inf t
      (s            , Sort MetaS{} ) -> prettyTCM $ ShouldBeASort $ El Inf s
      (Sort DefS{}  , t            ) -> prettyTCM $ ShouldBeASort $ El Inf t
      (s            , Sort DefS{}  ) -> prettyTCM $ ShouldBeASort $ El Inf s
      (_            , _            ) -> do
        (d1, d2, d) <- prettyInEqual s t
        fsep $ concat $
          [ [return d1, notCmp cmp, return d2]
          , case a of
                AsTermsOf t -> pwords "of type" ++ [prettyTCM t]
                AsSizes     -> pwords "of type" ++ [prettyTCM =<< sizeType]
                AsTypes     -> []
          , [return d]
          ]

    UnequalLevel cmp s t -> fsep $
      [prettyTCM s, notCmp cmp, prettyTCM t]

-- UnequalTelescopes is UNUSED
--   UnequalTelescopes cmp a b -> fsep $
--     [prettyTCM a, notCmp cmp, prettyTCM b]

    UnequalTypes cmp a b -> prettyUnequal a (notCmp cmp) b
--              fsep $ [prettyTCM a, notCmp cmp, prettyTCM b]

    UnequalRelevance cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because one is a relevant function type and the other is an irrelevant function type"

    UnequalQuantity cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because one is a non-erased function type and the other is an erased function type"

    UnequalHiding a b -> fsep $
      [prettyTCM a, "!=", prettyTCM b] ++
      pwords "because one is an implicit function type and the other is an explicit function type"

    UnequalSorts s1 s2 -> fsep $
      [prettyTCM s1, "!=", prettyTCM s2]

    NotLeqSort s1 s2 -> fsep $
      [prettyTCM s1] ++ pwords "is not less or equal than" ++ [prettyTCM s2]

    TooManyFields r missing xs -> fsep $
      pwords "The record type" ++ [prettyTCM r] ++
      pwords "does not have the fields" ++ punctuate comma (map pretty xs) ++
      if null missing then [] else
        pwords "but it would have the fields"  ++ punctuate comma (map pretty missing)

    DuplicateConstructors xs -> fsep $
      pwords "Duplicate constructors" ++ punctuate comma (map pretty xs) ++
      pwords "in datatype"

    DuplicateFields xs -> fsep $
      pwords "Duplicate fields" ++ punctuate comma (map pretty xs) ++
      pwords "in record"

    WithOnFreeVariable e v -> do
      de <- prettyA e
      dv <- prettyTCM v
      if show de == show dv
        then fsep $
          pwords "Cannot `with` on variable" ++ [return dv] ++
          pwords " bound in a module telescope (or patterns of a parent clause)"
        else fsep $
          pwords "Cannot `with` on expression" ++ [return de] ++ pwords "which reduces to variable" ++ [return dv] ++
          pwords " bound in a module telescope (or patterns of a parent clause)"

    UnexpectedWithPatterns ps -> fsep $
      pwords "Unexpected with patterns" ++ (punctuate " |" $ map prettyA ps)

    WithClausePatternMismatch p q -> fsep $
      pwords "With clause pattern " ++ [prettyA p] ++
      pwords " is not an instance of its parent pattern " ++ [P.fsep <$> prettyTCMPatterns [q]]

    -- The following error is caught and reraised as GenericDocError in Occurs.hs
    MetaCannotDependOn m {- ps -} i -> fsep $
      pwords "The metavariable" ++ [prettyTCM $ MetaV m []] ++
      pwords "cannot depend on" ++ [pvar i] ++
      [] -- pwords "because it" ++ deps
        where
          pvar = prettyTCM . I.var
          -- deps = case map pvar ps of
          --   []  -> pwords "does not depend on any variables"
          --   [x] -> pwords "only depends on the variable" ++ [x]
          --   xs  -> pwords "only depends on the variables" ++ punctuate comma xs

    -- The following error is caught and reraised as GenericDocError in Occurs.hs
    MetaOccursInItself m -> fsep $
      pwords "Cannot construct infinite solution of metavariable" ++ [prettyTCM $ MetaV m []]

    -- The following error is caught and reraised as GenericDocError in Occurs.hs
    MetaIrrelevantSolution m _ -> fsep $
      pwords "Cannot instantiate the metavariable because (part of) the" ++
      pwords "solution was created in an irrelevant context."

    -- The following error is caught and reraised as GenericDocError in Occurs.hs
    MetaErasedSolution m _ -> fsep $
      pwords "Cannot instantiate the metavariable because (part of) the" ++
      pwords "solution was created in an erased context."

    BuiltinMustBeConstructor s e -> fsep $
      [prettyA e] ++ pwords "must be a constructor in the binding to builtin" ++ [text s]

    NoSuchBuiltinName s -> fsep $
      pwords "There is no built-in thing called" ++ [text s]

    DuplicateBuiltinBinding b x y -> fsep $
      pwords "Duplicate binding for built-in thing" ++ [text b <> comma] ++
      pwords "previous binding to" ++ [prettyTCM x]

    NoBindingForBuiltin x
      | x `elem` [builtinZero, builtinSuc] -> fsep $
        pwords "No binding for builtin " ++ [text x <> comma] ++
        pwords ("use {-# BUILTIN " ++ builtinNat ++ " name #-} to bind builtin natural " ++
                "numbers to the type 'name'")
      | otherwise -> fsep $
        pwords "No binding for builtin thing" ++ [text x <> comma] ++
        pwords ("use {-# BUILTIN " ++ x ++ " name #-} to bind it to 'name'")

    DuplicatePrimitiveBinding b x y -> fsep $
      pwords "Duplicate binding for primitive thing" ++ [text b <> comma] ++
      pwords "previous binding to" ++ [prettyTCM x]

    NoSuchPrimitiveFunction x -> fsep $
      pwords "There is no primitive function called" ++ [text x]

    BuiltinInParameterisedModule x -> fwords $
      "The BUILTIN pragma cannot appear inside a bound context " ++
      "(for instance, in a parameterised module or as a local declaration)"

    IllegalLetInTelescope tb -> fsep $
      -- pwords "The binding" ++
      [pretty tb] ++
      pwords " is not allowed in a telescope here."

    IllegalPatternInTelescope bd -> fsep $
      [pretty bd] ++
      pwords " is not allowed in a telescope here."

    NoRHSRequiresAbsurdPattern ps -> fwords $
      "The right-hand side can only be omitted if there " ++
      "is an absurd pattern, () or {}, in the left-hand side."

    LocalVsImportedModuleClash m -> fsep $
      pwords "The module" ++ [prettyTCM m] ++
      pwords "can refer to either a local module or an imported module"

    SolvedButOpenHoles -> fsep $
      pwords "Module cannot be imported since it has open interaction points" ++
      pwords "(consider adding {-# OPTIONS --allow-unsolved-metas #-} to this module)"

    CyclicModuleDependency ms ->
      fsep (pwords "cyclic module dependency:")
      $$ nest 2 (vcat $ map pretty ms)

    FileNotFound x files ->
      fsep ( pwords "Failed to find source of module" ++ [pretty x] ++
             pwords "in any of the following locations:"
           ) $$ nest 2 (vcat $ map (text . filePath) files)

    OverlappingProjects f m1 m2 ->
      fsep ( pwords "The file" ++ [text (filePath f)] ++
             pwords "can be accessed via several project roots. Both" ++
             [pretty m1] ++ pwords "and" ++ [pretty m2] ++
             pwords "point to this file."
           )

    AmbiguousTopLevelModuleName x files ->
      fsep ( pwords "Ambiguous module name. The module name" ++
             [pretty x] ++
             pwords "could refer to any of the following files:"
           ) $$ nest 2 (vcat $ map (text . filePath) files)

    ClashingFileNamesFor x files ->
      fsep ( pwords "Multiple possible sources for module"
             ++ [prettyTCM x] ++ pwords "found:"
           ) $$ nest 2 (vcat $ map (text . filePath) files)

    ModuleDefinedInOtherFile mod file file' -> fsep $
      pwords "You tried to load" ++ [text (filePath file)] ++
      pwords "which defines the module" ++ [pretty mod <> "."] ++
      pwords "However, according to the include path this module should" ++
      pwords "be defined in" ++ [text (filePath file') <> "."]

    ModuleNameUnexpected given expected -> fsep $
      pwords "The name of the top level module does not match the file name. The module" ++
      [ pretty given ] ++
      pwords "should probably be named" ++
      [ pretty expected ]

    ModuleNameDoesntMatchFileName given files ->
      fsep (pwords "The name of the top level module does not match the file name. The module" ++
           [ pretty given ] ++ pwords "should be defined in one of the following files:")
      $$ nest 2 (vcat $ map (text . filePath) files)

    BothWithAndRHS -> fsep $ pwords "Unexpected right hand side"

    AbstractConstructorNotInScope q -> fsep $
      [ "Constructor"
      , prettyTCM q
      ] ++ pwords "is abstract, thus, not in scope here"

    NotInScope xs ->
      -- using the warning version to avoid code duplication
      prettyTCM (NotInScopeW xs)

    NoSuchModule x -> fsep $ pwords "No module" ++ [pretty x] ++ pwords "in scope"

    AmbiguousName x ys -> vcat
      [ fsep $ pwords "Ambiguous name" ++ [pretty x <> "."] ++
               pwords "It could refer to any one of"
      , nest 2 $ vcat $ map nameWithBinding (NonEmpty.toList ys)
      , fwords "(hint: Use C-c C-w (in Emacs) if you want to know why)"
      ]

    AmbiguousModule x ys -> vcat
      [ fsep $ pwords "Ambiguous module name" ++ [pretty x <> "."] ++
               pwords "It could refer to any one of"
      , nest 2 $ vcat $ map help (NonEmpty.toList ys)
      , fwords "(hint: Use C-c C-w (in Emacs) if you want to know why)"
      ]
      where
        help :: MonadPretty m => ModuleName -> m Doc
        help m = do
          anno <- caseMaybeM (isDatatypeModule m) (return empty) $ \case
            IsData   -> return $ "(datatype module)"
            IsRecord -> return $ "(record module)"
          sep [prettyTCM m, anno ]

    ClashingDefinition x y -> fsep $
      pwords "Multiple definitions of" ++ [pretty x <> "."] ++
      pwords "Previous definition at"
      ++ [prettyTCM $ nameBindingSite $ qnameName y]

    ClashingModule m1 m2 -> fsep $
      pwords "The modules" ++ [prettyTCM m1, "and", prettyTCM m2]
      ++ pwords "clash."

    ClashingImport x y -> fsep $
      pwords "Import clash between" ++ [pretty x, "and", prettyTCM y]

    ClashingModuleImport x y -> fsep $
      pwords "Module import clash between" ++ [pretty x, "and", prettyTCM y]

    PatternShadowsConstructor x c -> fsep $
      pwords "The pattern variable" ++ [prettyTCM x] ++
      pwords "has the same name as the constructor" ++ [prettyTCM c]

    DuplicateImports m xs -> fsep $
      pwords "Ambiguous imports from module" ++ [pretty m] ++ pwords "for" ++
      punctuate comma (map pretty xs)

    NotAModuleExpr e -> fsep $
      pwords "The right-hand side of a module definition must have the form 'M e1 .. en'" ++
      pwords "where M is a module name. The expression"
      ++ [pretty e, "doesn't."]

    FieldOutsideRecord -> fsep $
      pwords "Field appearing outside record declaration."

    InvalidPattern p -> fsep $
      pretty p : pwords "is not a valid pattern"

    RepeatedVariablesInPattern xs -> fsep $
      pwords "Repeated variables in pattern:" ++ map pretty xs

    NotAnExpression e -> fsep $
      [pretty e] ++ pwords "is not a valid expression."

    NotAValidLetBinding nd -> fwords $
      "Not a valid let-declaration"

    NotValidBeforeField nd -> fwords $
      "This declaration is illegal in a record before the last field"

    NothingAppliedToHiddenArg e -> fsep $
      [pretty e] ++ pwords "cannot appear by itself. It needs to be the argument to" ++
      pwords "a function expecting an implicit argument."

    NothingAppliedToInstanceArg e -> fsep $
      [pretty e] ++ pwords "cannot appear by itself. It needs to be the argument to" ++
      pwords "a function expecting an instance argument."

    NoParseForApplication es -> fsep (
      pwords "Could not parse the application" ++ [pretty $ C.RawApp noRange es])

    AmbiguousParseForApplication es es' -> fsep (
      pwords "Don't know how to parse" ++ [pretty_es <> "."] ++
      pwords "Could mean any one of:"
      ) $$ nest 2 (vcat $ map pretty' es')
      where
        pretty_es :: MonadPretty m => m Doc
        pretty_es = pretty $ C.RawApp noRange es

        pretty' :: MonadPretty m => C.Expr -> m Doc
        pretty' e = do
          p1 <- pretty_es
          p2 <- pretty e
          if show p1 == show p2 then unambiguous e else pretty e

        unambiguous :: MonadPretty m => C.Expr -> m Doc
        unambiguous e@(C.OpApp r op _ xs)
          | all (isOrdinary . namedArg) xs =
            pretty $
              foldl (C.App r) (C.Ident op) $
                (map . fmap . fmap) fromOrdinary xs
          | any (isPlaceholder . namedArg) xs =
              pretty e <+> "(section)"
        unambiguous e = pretty e

        isOrdinary :: MaybePlaceholder (C.OpApp e) -> Bool
        isOrdinary (NoPlaceholder _ (C.Ordinary _)) = True
        isOrdinary _                                = False

        fromOrdinary :: MaybePlaceholder (C.OpApp e) -> e
        fromOrdinary (NoPlaceholder _ (C.Ordinary e)) = e
        fromOrdinary _                                = __IMPOSSIBLE__

        isPlaceholder :: MaybePlaceholder a -> Bool
        isPlaceholder Placeholder{}   = True
        isPlaceholder NoPlaceholder{} = False

    BadArgumentsToPatternSynonym x -> fsep $
      pwords "Bad arguments to pattern synonym " ++ [prettyTCM $ headAmbQ x]

    TooFewArgumentsToPatternSynonym x -> fsep $
      pwords "Too few arguments to pattern synonym " ++ [prettyTCM $ headAmbQ x]

    CannotResolveAmbiguousPatternSynonym defs -> vcat
      [ fsep $ pwords "Cannot resolve overloaded pattern synonym" ++ [prettyTCM x <> comma] ++
               pwords "since candidates have different shapes:"
      , nest 2 $ vcat $ map prDef (NonEmpty.toList defs)
      , fsep $ pwords "(hint: overloaded pattern synonyms must be equal up to variable and constructor names)"
      ]
      where
        (x, _) = NonEmpty.head defs
        prDef (x, (xs, p)) = prettyA (A.PatternSynDef x xs p) <?> ("at" <+> pretty r)
          where r = nameBindingSite $ qnameName x

    UnusedVariableInPatternSynonym -> fsep $
      pwords "Unused variable in pattern synonym."

    NoParseForLHS IsLHS p -> fsep (
      pwords "Could not parse the left-hand side" ++ [pretty p])

    NoParseForLHS IsPatSyn p -> fsep (
      pwords "Could not parse the pattern synonym" ++ [pretty p])

{- UNUSED
    NoParseForPatternSynonym p -> fsep $
      pwords "Could not parse the pattern synonym" ++ [pretty p]
-}

    AmbiguousParseForLHS lhsOrPatSyn p ps -> fsep (
      pwords "Don't know how to parse" ++ [pretty_p <> "."] ++
      pwords "Could mean any one of:"
      ) $$ nest 2 (vcat $ map pretty' ps)
      where
        pretty_p :: MonadPretty m => m Doc
        pretty_p = pretty p

        pretty' :: MonadPretty m => C.Pattern -> m Doc
        pretty' p' = do
          p1 <- pretty_p
          p2 <- pretty p'
          pretty $ if show p1 == show p2 then unambiguousP p' else p'

        -- the entire pattern is shown, not just the ambiguous part,
        -- so we need to dig in order to find the OpAppP's.
        unambiguousP :: C.Pattern -> C.Pattern
        unambiguousP (C.AppP x y)         = C.AppP (unambiguousP x) $ (fmap.fmap) unambiguousP y
        unambiguousP (C.HiddenP r x)      = C.HiddenP r $ fmap unambiguousP x
        unambiguousP (C.InstanceP r x)    = C.InstanceP r $ fmap unambiguousP x
        unambiguousP (C.ParenP r x)       = C.ParenP r $ unambiguousP x
        unambiguousP (C.AsP r n x)        = C.AsP r n $ unambiguousP x
        unambiguousP (C.OpAppP r op _ xs) = foldl C.AppP (C.IdentP op) xs
        unambiguousP e                    = e

    OperatorInformation sects err ->
      prettyTCM err
        $+$
      fsep (pwords "Operators used in the grammar:")
        $$
      nest 2
        (if null sects then "None" else
         vcat (map text $
               lines $
               Boxes.render $
               (\(col1, col2, col3) ->
                   Boxes.hsep 1 Boxes.top $
                   map (Boxes.vcat Boxes.left) [col1, col2, col3]) $
               unzip3 $
               map prettySect $
               sortBy (compare `on` show . notaName . sectNotation) $
               filter (not . closedWithoutHoles) sects))
      where
      trimLeft  = dropWhile isNormalHole
      trimRight = dropWhileEnd isNormalHole

      closedWithoutHoles sect =
        sectKind sect == NonfixNotation
          &&
        null [ () | NormalHole {} <- trimLeft $ trimRight $
                                       notation (sectNotation sect) ]

      prettyName n = Boxes.text $
        P.render (P.pretty n) ++
        " (" ++ P.render (P.pretty (nameBindingSite n)) ++ ")"

      prettySect sect =
        ( Boxes.text (P.render (P.pretty section))
            Boxes.//
          strut
        , Boxes.text
            ("(" ++
             kind ++ " " ++
             (if notaIsOperator nota
              then "operator"
              else "notation") ++
             (if sectIsSection sect
              then " section"
              else "") ++
             (case sectLevel sect of
                Nothing          -> ""
                Just Unrelated   -> ", unrelated"
                Just (Related l) -> ", level " ++ toStringWithoutDotZero l) ++
             ")")
            Boxes.//
          strut
        , "["
            Boxes.<>
          Boxes.vcat Boxes.left
            (map (\n -> prettyName n Boxes.<> ",") names ++
             [prettyName name Boxes.<> "]"])
        )
        where
        nota    = sectNotation sect
        section = qualifyFirstIdPart
                    (foldr (\x s -> C.nameToRawName x ++ "." ++ s)
                           ""
                           (init (C.qnameParts (notaName nota))))
                    (trim (notation nota))

        qualifyFirstIdPart _ []              = []
        qualifyFirstIdPart q (IdPart x : ps) = IdPart (fmap (q ++) x) : ps
        qualifyFirstIdPart q (p : ps)        = p : qualifyFirstIdPart q ps

        trim = case sectKind sect of
          InfixNotation   -> trimLeft . trimRight
          PrefixNotation  -> trimRight
          PostfixNotation -> trimLeft
          NonfixNotation  -> id
          NoNotation      -> __IMPOSSIBLE__

        (names, name) = case Set.toList $ notaNames nota of
          [] -> __IMPOSSIBLE__
          ns -> (init ns, last ns)

        strut = Boxes.emptyBox (length names) 0

        kind = case sectKind sect of
          PrefixNotation  -> "prefix"
          PostfixNotation -> "postfix"
          NonfixNotation  -> "closed"
          NoNotation      -> __IMPOSSIBLE__
          InfixNotation   ->
            case fixityAssoc $ notaFixity nota of
              NonAssoc   -> "infix"
              LeftAssoc  -> "infixl"
              RightAssoc -> "infixr"

{- UNUSED
    AmbiguousParseForPatternSynonym p ps -> fsep (
      pwords "Don't know how to parse" ++ [pretty p <> "."] ++
      pwords "Could mean any one of:"
      ) $$ nest 2 (vcat $ map pretty ps)
-}

{- UNUSED
    IncompletePatternMatching v args -> fsep $
      pwords "Incomplete pattern matching for" ++ [prettyTCM v <> "."] ++
      pwords "No match for" ++ map prettyTCM args
-}

    SplitError e -> prettyTCM e

    ImpossibleConstructor c neg -> fsep $
      pwords "The case for the constructor " ++ [prettyTCM c] ++
      pwords " is impossible" ++ [prettyTCM neg] ++
      pwords "Possible solution: remove the clause, or use an absurd pattern ()."

    TooManyPolarities x n -> fsep $
      pwords "Too many polarities given in the POLARITY pragma for" ++
      [prettyTCM x] ++
      pwords "(at most" ++ [text (show n)] ++ pwords "allowed)."

    InstanceNoCandidate t errs -> vcat $
      [ fsep $ pwords "No instance of type" ++ [prettyTCM t] ++ pwords "was found in scope."
      , vcat $ map prCand errs ]
      where
        prCand (term, err) =
          text "-" <+>
            vcat [ prettyTCM term <?> text "was ruled out because"
                 , prettyTCM err ]

    UnquoteFailed e -> case e of
      BadVisibility msg arg -> fsep $
        pwords $ "Unable to unquote the argument. It should be `" ++ msg ++ "'."

      ConInsteadOfDef x def con -> fsep $
        pwords ("Use " ++ con ++ " instead of " ++ def ++ " for constructor") ++
        [prettyTCM x]

      DefInsteadOfCon x def con -> fsep $
        pwords ("Use " ++ def ++ " instead of " ++ con ++ " for non-constructor")
        ++ [prettyTCM x]

      NonCanonical kind t ->
        fwords ("Cannot unquote non-canonical " ++ kind)
        $$ nest 2 (prettyTCM t)

      BlockedOnMeta _ m -> fsep $
        pwords $ "Unquote failed because of unsolved meta variables."

      UnquotePanic err -> __IMPOSSIBLE__

    DeBruijnIndexOutOfScope i EmptyTel [] -> fsep $
        pwords $ "de Bruijn index " ++ show i ++ " is not in scope in the empty context"
    DeBruijnIndexOutOfScope i cxt names ->
        sep [ text ("de Bruijn index " ++ show i ++ " is not in scope in the context")
            , inTopContext $ addContext ("_" :: String) $ prettyTCM cxt' ]
      where
        cxt' = cxt `abstract` raise (size cxt) (nameCxt names)
        nameCxt :: [Name] -> I.Telescope
        nameCxt [] = EmptyTel
        nameCxt (x : xs) = ExtendTel (defaultDom (El __DUMMY_SORT__ $ I.var 0)) $
          NoAbs (P.prettyShow x) $ nameCxt xs

    NeedOptionCopatterns -> fsep $
      pwords "Option --copatterns needed to enable destructor patterns"

    NeedOptionRewriting  -> fsep $
      pwords "Option --rewriting needed to add and use rewrite rules"

    NeedOptionProp       -> fsep $
      pwords "Universe Prop is disabled (use options --prop and --no-prop to enable/disable Prop)"

    GeneralizeNotSupportedHere x -> fsep $
      pwords $ "Generalizable variable " ++ show x ++ " is not supported here"

    GeneralizeCyclicDependency -> fsep $
      pwords "Cyclic dependency between generalized variables"

    GeneralizeUnsolvedMeta -> fsep $
      pwords "Unsolved meta not generalized"

    MultipleFixityDecls xs ->
      sep [ fsep $ pwords "Multiple fixity or syntax declarations for"
          , vcat $ map f xs
          ]
      where
        f (x, fs) = (pretty x <> ": ") <+> fsep (map pretty fs)

    MultiplePolarityPragmas xs -> fsep $
      pwords "Multiple polarity pragmas for" ++ map pretty xs

    NonFatalErrors ws -> foldr1 ($$) $ fmap prettyTCM ws

    InstanceSearchDepthExhausted c a d -> fsep $
      pwords ("Instance search depth exhausted (max depth: " ++ show d ++ ") for candidate") ++
      [hang (prettyTCM c <+> ":") 2 (prettyTCM a)]

    TriedToCopyConstrainedPrim q -> fsep $
      pwords "Cannot create a module containing a copy of" ++ [prettyTCM q]

    where
    mpar n args
      | n > 0 && not (null args) = parens
      | otherwise                = id

    prettyArg :: MonadPretty m => Arg (I.Pattern' a) -> m Doc
    prettyArg (Arg info x) = case getHiding info of
      Hidden     -> braces $ prettyPat 0 x
      Instance{} -> dbraces $ prettyPat 0 x
      NotHidden  -> prettyPat 1 x

    prettyPat :: MonadPretty m => Integer -> (I.Pattern' a) -> m Doc
    prettyPat _ (I.VarP _ _) = "_"
    prettyPat _ (I.DotP _ _) = "._"
    prettyPat n (I.ConP c _ args) =
      mpar n args $
        prettyTCM c <+> fsep (map (prettyArg . fmap namedThing) args)
    prettyPat n (I.DefP o q args) =
      mpar n args $
        prettyTCM q <+> fsep (map (prettyArg . fmap namedThing) args)
    prettyPat _ (I.LitP _ l) = prettyTCM l
    prettyPat _ (I.ProjP _ p) = "." <> prettyTCM p
    prettyPat _ (I.IApplyP _ _ _ _) = "_"

notCmp :: MonadPretty m => Comparison -> m Doc
notCmp cmp = "!" <> prettyTCM cmp

-- | Print two terms that are supposedly unequal.
--   If they print to the same identifier, add some explanation
--   why they are different nevertheless.
prettyInEqual :: MonadPretty m => Term -> Term -> m (Doc, Doc, Doc)
prettyInEqual t1 t2 = do
  d1 <- prettyTCM t1
  d2 <- prettyTCM t2
  (d1, d2,) <$> do
     -- if printed differently, no extra explanation needed
    if P.render d1 /= P.render d2 then empty else do
      (v1, v2) <- instantiate (t1, t2)
      case (v1, v2) of
        (I.Var i1 _, I.Var i2 _)
          | i1 == i2  -> generic -- possible, see issue 1826
          | otherwise -> varVar i1 i2
        (I.Def{}, I.Con{}) -> __IMPOSSIBLE__  -- ambiguous identifiers
        (I.Con{}, I.Def{}) -> __IMPOSSIBLE__
        (I.Var{}, I.Def{}) -> varDef
        (I.Def{}, I.Var{}) -> varDef
        (I.Var{}, I.Con{}) -> varCon
        (I.Con{}, I.Var{}) -> varCon
        _                  -> empty
  where
    varDef, varCon, generic :: MonadPretty m => m Doc
    varDef = parens $ fwords "because one is a variable and one a defined identifier"
    varCon = parens $ fwords "because one is a variable and one a constructor"
    generic = parens $ fwords $ "although these terms are looking the same, " ++
      "they contain different but identically rendered identifiers somewhere"
    varVar :: MonadPretty m => Int -> Int -> m Doc
    varVar i j = parens $ fwords $
                   "because one has de Bruijn index " ++ show i
                   ++ " and the other " ++ show j

class PrettyUnequal a where
  prettyUnequal :: MonadPretty m => a -> m Doc -> a -> m Doc

instance PrettyUnequal Term where
  prettyUnequal t1 ncmp t2 = do
    (d1, d2, d) <- prettyInEqual t1 t2
    fsep $ return d1 : ncmp : return d2 : return d : []

instance PrettyUnequal Type where
  prettyUnequal t1 ncmp t2 = prettyUnequal (unEl t1) ncmp (unEl t2)

instance PrettyTCM SplitError where
  prettyTCM err = case err of
    NotADatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot split on argument of non-datatype" ++ [prettyTCM t]

    IrrelevantDatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot split on argument of irrelevant datatype" ++ [prettyTCM t]

    ErasedDatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot branch on erased argument of datatype" ++ [prettyTCM t]

    CoinductiveDatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot pattern match on the coinductive type" ++ [prettyTCM t]

{- UNUSED
    NoRecordConstructor t -> fsep $
      pwords "Cannot pattern match on record" ++ [prettyTCM t] ++
      pwords "because it has no constructor"
 -}

    UnificationStuck c tel cIxs gIxs errs
      | length cIxs /= length gIxs -> __IMPOSSIBLE__
      | otherwise                  -> vcat . concat $
        [ [ fsep . concat $
            [ pwords "I'm not sure if there should be a case for the constructor"
            , [prettyTCM c <> ","]
            , pwords "because I get stuck when trying to solve the following"
            , pwords "unification problems (inferred index ≟ expected index):"
            ]
          ]
        , zipWith prEq cIxs gIxs
        , if null errs then [] else
            [ fsep $ pwords "Possible" ++ pwords (P.singPlural errs "reason" "reasons") ++
                     pwords "why unification failed:" ] ++
            map (nest 2 . prettyTCM) errs
        ]
      where
        -- Andreas, 2019-08-08, issue #3943
        -- To not print hidden indices just as {_}, we strip the Arg and print
        -- the hiding information manually.
        prEq cIx gIx = addContext tel $ nest 2 $ hsep [ pr cIx , "≟" , pr gIx ]
        pr arg = prettyRelevance arg . prettyHiding arg id <$> prettyTCM (unArg arg)

    CosplitCatchall -> fsep $
      pwords "Cannot split into projections because not all clauses have a projection copattern"

    CosplitNoTarget -> fsep $
      pwords "Cannot split into projections because target type is unknown"

    CosplitNoRecordType t -> enterClosure t $ \t -> fsep $
      pwords "Cannot split into projections because the target type "
      ++ [prettyTCM t] ++ pwords " is not a record type"

    CannotCreateMissingClause f cl msg t -> fsep (
      pwords "Cannot generate inferred clause for" ++ [prettyTCM f <> "."] ++
      pwords "Case to handle:") $$ nest 2 (vcat $ [display cl])
                                $$ ((pure msg <+> enterClosure t displayAbs) <> ".")
        where
        displayAbs (Abs x t) = addContext x $ prettyTCM t
        displayAbs (NoAbs x t) = prettyTCM t
        display (tel, ps) = prettyTCM $ NamedClause f True $
          empty { clauseTel = tel, namedClausePats = ps }


    GenericSplitError s -> fsep $ pwords "Split failed:" ++ pwords s

instance PrettyTCM NegativeUnification where
  prettyTCM err = case err of
    UnifyConflict tel u v -> addContext tel $ vcat $
      [ fsep $ pwords "because unification ended with a conflicting equation "
      , nest 2 $ prettyTCM u <+> "≟" <+> prettyTCM v
      ]

    UnifyCycle tel i u -> addContext tel $ vcat $
      [ fsep $ pwords "because unification ended with a cyclic equation "
      , nest 2 $ prettyTCM (var i) <+> "≟" <+> prettyTCM u
      ]

instance PrettyTCM UnificationFailure where
  prettyTCM err = case err of
    UnifyIndicesNotVars tel a u v ixs -> addContext tel $ fsep $
      pwords "Cannot apply injectivity to the equation" ++ [prettyTCM u] ++
      pwords "=" ++ [prettyTCM v] ++ pwords "of type" ++ [prettyTCM a] ++
      pwords "because I cannot generalize over the indices" ++
      [prettyList (map prettyTCM ixs) <> "."]

    UnifyRecursiveEq tel a i u -> addContext tel $ fsep $
      pwords "Cannot solve variable " ++ [prettyTCM (var i)] ++
      pwords " of type " ++ [prettyTCM a] ++
      pwords " with solution " ++ [prettyTCM u] ++
      pwords " because the variable occurs in the solution," ++
      pwords " or in the type of one of the variables in the solution."

    UnifyReflexiveEq tel a u -> addContext tel $ fsep $
      pwords "Cannot eliminate reflexive equation" ++ [prettyTCM u] ++
      pwords "=" ++ [prettyTCM u] ++ pwords "of type" ++ [prettyTCM a] ++
      pwords "because K has been disabled."

    UnifyUnusableModality tel a i u mod -> addContext tel $ fsep $
      pwords "Cannot solve variable " ++ [prettyTCM (var i)] ++
      pwords "of type " ++ [prettyTCM a] ++
      pwords "with solution " ++ [prettyTCM u] ++
      pwords "because the solution cannot be used at" ++
             [ text (verbalize $ getRelevance mod) <> ","
             , text $ verbalize $ getQuantity mod ] ++
      pwords "modality"


---------------------------------------------------------------------------
-- * Natural language
---------------------------------------------------------------------------

class Verbalize a where
  verbalize :: a -> String

instance Verbalize Hiding where
  verbalize h =
    case h of
      Hidden     -> "hidden"
      NotHidden  -> "visible"
      Instance{} -> "instance"

instance Verbalize Relevance where
  verbalize r =
    case r of
      Relevant   -> "relevant"
      Irrelevant -> "irrelevant"
      NonStrict  -> "shape-irrelevant"

instance Verbalize Quantity where
  verbalize = \case
    Quantity0{} -> "erased"
    Quantity1{} -> "linear"
    Quantityω{} -> "unrestricted"

instance Verbalize Cohesion where
  verbalize r =
    case r of
      Flat       -> "flat"
      Continuous -> "continuous"
      Squash     -> "squashed"

-- | Indefinite article.
data Indefinite a = Indefinite a

instance Verbalize a => Verbalize (Indefinite a) where
  verbalize (Indefinite a) =
    case verbalize a of
      "" -> ""
      w@(c:cs) | c `elem` ['a','e','i','o'] -> "an " ++ w
               | otherwise                  -> "a " ++ w
      -- Aarne Ranta would whip me if he saw this.
