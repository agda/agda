{-# LANGUAGE NondecreasingIndentation #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.TypeChecking.Errors
  ( renderError
  , prettyError
  , tcErrString
  , prettyTCWarnings'
  , prettyTCWarnings
  , tcWarningsToError
  , applyFlagsToTCWarningsPreserving
  , applyFlagsToTCWarnings
  , getAllUnsolvedWarnings
  , getAllWarningsPreserving
  , getAllWarnings
  , getAllWarningsOfTCErr
  , dropTopLevelModule
  , topLevelModuleDropper
  , explainWhyInScope
  , Verbalize(verbalize)
  ) where

import Prelude hiding ( null, foldl )

import qualified Control.Exception as E
import Control.Monad ((>=>), (<=<))
import Control.Monad.Except

import qualified Data.CaseInsensitive as CaseInsens
import Data.Foldable (foldl)
import Data.Function (on)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortBy, dropWhileEnd, intercalate)
import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import System.FilePath
import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Interaction.Options
import Agda.Interaction.Options.Errors

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( prettyShow, render )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Concrete.Definitions (notSoNiceDeclarations)
import Agda.Syntax.Concrete.Definitions.Errors (declarationExceptionString)
import Agda.Syntax.Concrete.Pretty (attributesForModality, prettyHiding, prettyRelevance)
import Agda.Syntax.Notation
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Scope.Monad (isDatatypeModule)
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Errors.Names (typeErrorString)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Call
import Agda.TypeChecking.Pretty.Warning
import Agda.TypeChecking.SizedTypes.Pretty ()
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce (instantiate)

import Agda.Interaction.Library.Base (formatLibErrors, libFile)

import Agda.Utils.FileName
import Agda.Utils.Float  ( toStringWithoutDotZero )
import Agda.Utils.Function
import Agda.Utils.Functor( for )
import Agda.Utils.IO     ( showIOException )
import Agda.Utils.Lens
import Agda.Utils.List   ( initLast, lastMaybe )
import Agda.Utils.List1  ( List1, pattern (:|) )
import Agda.Utils.List2  ( pattern List2 )
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.Singleton
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Top level function
---------------------------------------------------------------------------

{-# SPECIALIZE renderError :: TCErr -> TCM String #-}
renderError :: MonadTCM tcm => TCErr -> tcm String
renderError = fmap show . prettyError

{-# SPECIALIZE prettyError :: TCErr -> TCM Doc #-}
prettyError :: MonadTCM tcm => TCErr -> tcm Doc
prettyError = liftTCM . flip renderError' [] where
  renderError' :: TCErr -> [TCErr] -> TCM Doc
  renderError' err errs
    | length errs > 3 = fsep (
        pwords "total panic: error when printing error from printing error from printing error." ++
        pwords "I give up! Approximations of errors (original error last):" )
        $$ vcat (map (text . tcErrString) errs)
    | otherwise = applyUnless (null errs) ("panic: error when printing error!" $$) $ do
        (prettyTCM err $$ vcat (map (text . ("when printing error " ++) . tcErrString) errs))
        `catchError` \ err' -> renderError' err' (err:errs)

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
tcErrString err =
  unwords . filter (not . null) . (prettyShow (getRange err) :) $
    case err of
      TypeError _ _ cl     -> [ typeErrorString $ clValue cl ]
      ParserError e        -> [ "ParserError" ]
      GenericException msg -> [ msg ]
      IOException _ r e    -> [ prettyShow r, showIOException e ]
      PatternErr{}         -> [ "PatternErr" ]

instance PrettyTCM TCErr where
  prettyTCM err = case err of
    -- Gallais, 2016-05-14
    -- Given where `NonFatalErrors` are created, we know for a
    -- fact that  ̀ws` is non-empty.
    TypeError loc _ Closure{ clValue = NonFatalErrors ws } -> do
      reportSLn "error" 2 $ "Error raised at " ++ prettyShow loc
      vsep $ fmap prettyTCM $ Set1.toAscList ws
    -- Andreas, 2014-03-23
    -- This use of withTCState seems ok since we do not collect
    -- Benchmark info during printing errors.
    TypeError loc s e -> withTCState (const s) $ do
      reportSLn "error" 2 $ "Error raised at " ++ prettyShow loc
      let r = envRange $ clEnv e
      vcat
        [ hsep
          [ if null r then empty else prettyTCM r <> ":"
          , "error:"
          , brackets (text $ typeErrorString $ clValue e)
          ]
        , prettyTCM e
        , prettyTCM (envCall $ clEnv e)
        ]
    ParserError err   -> pretty err
    GenericException msg -> fwords msg
    IOException _ r e -> sayWhere r $ fwords $ showIOException e
    PatternErr{}      -> sayWhere err $ panic "uncaught pattern violation"

-- | Drops given amount of leading components of the qualified name.
dropTopLevelModule' :: Int -> QName -> QName
dropTopLevelModule' k (QName (MName ns) n) = QName (MName (drop k ns)) n

-- | Drops the filename component of the qualified name.
dropTopLevelModule :: MonadPretty m => QName -> m QName
dropTopLevelModule q = ($ q) <$> topLevelModuleDropper

-- | Produces a function which drops the filename component of the qualified name.
topLevelModuleDropper :: (MonadDebug m, MonadTCEnv m, ReadTCState m) => m (QName -> QName)
topLevelModuleDropper =
  caseMaybeM currentTopLevelModule
    (return id)
    (return . dropTopLevelModule' . size)

prettyDisamb :: MonadPretty m => (QName -> Maybe (Range' SrcFile)) -> QName -> m Doc
prettyDisamb f x = do
  let d  = pretty =<< dropTopLevelModule x
  caseMaybe (f x) d $ \ r -> d <+> ("(introduced at " <> prettyTCM r <> ")")

-- | Print the last range in 'qnameModule'.
prettyDisambProj :: MonadPretty m => QName -> m Doc
prettyDisambProj = prettyDisamb $ lastMaybe . filter (noRange /=) . map nameBindingSite . mnameToList . qnameModule

--   Print the range in 'qnameName'. This fixes the bad error message in #4130.
prettyDisambCons :: MonadPretty m => QName -> m Doc
prettyDisambCons = prettyDisamb $ Just . nameBindingSite . qnameName

instance PrettyTCM TypeError where
  prettyTCM :: forall m. MonadPretty m => TypeError -> m Doc
  prettyTCM err = case err of
    InternalError s -> panic s

    NotImplemented s -> fwords $ "Not implemented: " ++ s

    NotSupported s -> fwords $ "Not supported: " ++ s

    CompilationError s -> sep [fwords "Compilation error:", text s]

    GenericError s -> fwords s

    GenericDocError d -> return d

    ExecError err -> prettyTCM err

    NicifierError err -> pretty err

    OptionError s -> fwords s

    SyntaxError s -> fwords $ "Syntax error: "  ++ s

    DoNotationError err -> fwords err

    IdiomBracketError err -> fwords err

    InvalidDottedExpression -> fwords "Invalid dotted expression"

    NoKnownRecordWithSuchFields fields -> fsep $
      case fields of
        []  -> pwords "There are no records in scope"
        [f] -> pwords "There is no known record with the field" ++ [ pretty f ]
        _   -> pwords "There is no known record with the fields" ++ map pretty fields

    ShouldEndInApplicationOfTheDatatype t -> fsep $
      pwords "The target of a constructor must be the datatype applied to its parameters,"
      ++ [prettyTCM t] ++ pwords "isn't"

    ShouldBeRecordType t -> fsep $
      pwords "Expected non-abstract record type, found " ++ [prettyTCM t]

    ShouldBeRecordPattern p -> fsep $
      pwords "Expected record pattern" -- ", found " ++ [prettyTCM p]

    WrongHidingInLHS -> fwords "Unexpected implicit argument"

    WrongHidingInLambda t ->
      fwords "Found an implicit lambda where an explicit lambda was expected"

    WrongHidingInProjection d ->
      sep [ "Wrong hiding used for projection " , prettyTCM d ]

    IllegalHidingInPostfixProjection arg -> fsep $
      pwords "Illegal hiding in postfix projection " ++
      [pretty arg]

    WrongAnnotationInLambda ->
      fwords "Wrong annotation in lambda"

    WrongIrrelevanceInLambda ->
      fwords "Found a non-strict lambda where a irrelevant lambda was expected"

    WrongQuantityInLambda ->
      fwords "Incorrect quantity annotation in lambda"

    WrongCohesionInLambda ->
      fwords "Incorrect cohesion annotation in lambda"

    WrongPolarityInLambda ->
      fwords "Incorrect polarity annotation in lambda"

    WrongNamedArgument a xs0 -> fsep $
      pwords "Function does not accept argument "
      ++ [prettyTCM a] -- ++ pwords " (wrong argument name)"
      ++ [parens $ fsep $ text "possible arguments:" : map pretty xs | not (null xs)]
      where
      xs = List1.filter (not . isNoName) xs0

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

    ForcedConstructorNotInstantiated p -> fsep $
      pwords "Failed to infer that constructor pattern "
      ++ [prettyA p] ++ pwords " is forced"

    IllformedProjectionPatternAbstract p -> fsep $
      pwords "Ill-formed projection pattern " ++ [prettyA p]

    IllformedProjectionPatternConcrete p -> fsep $
      pwords "Ill-formed projection pattern" ++ [pretty p]

    LiteralTooBig -> fsep $ concat
      [ pwords "Matching on natural number literals is done by expanding"
      , pwords "the literal to the corresponding constructor pattern,"
      , pwords "so you probably don't want to do it this way"
      ]

    NegativeLiteralInPattern -> fsep $
      pwords "Negative literals are not supported in patterns"

    CannotEliminateWithPattern b p a -> do
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

    CannotEliminateWithProjection ty isAmbiguous projection -> sep
        [ "Cannot eliminate type "
        , prettyTCM (unArg ty)
        , " with projection "
        , if isAmbiguous then
            text $ prettyShow projection
          else
            prettyTCM projection
        ]

    WrongNumberOfConstructorArguments c expect given -> fsep $
      pwords "The constructor" ++ [prettyTCM c] ++
      pwords "expects" ++ [prettyTCM expect] ++
      pwords "arguments (including hidden ones), but has been given"
      ++ [prettyTCM given] ++ pwords "(including hidden ones)"

    CantResolveOverloadedConstructorsTargetingSameDatatype d cs -> fsep $
      pwords "Can't resolve overloaded constructors targeting the same datatype"
      ++ [parens (prettyTCM (qnameToConcrete d)) <> colon]
      ++ map pretty (List1.toList cs)

    ConstructorDoesNotTargetGivenType c t -> fsep $
      pwords "The constructor" ++ [prettyTCM c] ++
      pwords "does not construct an element of" ++ [prettyTCM t]

    ConstructorPatternInWrongDatatype c d -> fsep $
      [prettyTCM c] ++ pwords "is not a constructor of the datatype"
      ++ [prettyTCM d]

    ShadowedModule x ms@(m0 :| _) -> do
      -- Clash! Concrete module name x already points to the abstract names ms.
      (r, m) <- do
        -- Andreas, 2017-07-28, issue #719.
        -- First, we try to find whether one of the abstract names @ms@ points back to @x@
        scope <- getScope
        -- Get all pairs (y,m) such that y points to some m ∈ ms.
        let xms0 = concat $ ms <&> \ m -> map (,m) $ inverseScopeLookupModule m scope
        reportSLn "scope.clash.error" 30 $ "candidates = " ++ prettyShow xms0

        -- Try to find x (which will have a different Range, if it has one (#2649)).
        let xms = filter ((\ y -> not (null $ getRange y) && y == C.QName x) . fst) xms0
        reportSLn "scope.class.error" 30 $ "filtered candidates = " ++ prettyShow xms

        -- If we found a copy of x with non-empty range, great!
        ifJust (listToMaybe xms) (\ (x', m) -> return (getRange x', m)) $ {-else-} do

        -- If that failed, we pick the first m from ms which has a nameBindingSite.
        let rms = concat $ ms <&> \ m -> map (,m) $
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
        help :: MonadPretty m => ModuleName -> m Doc
        help m = caseMaybeM (isDatatypeModule m) empty $ \case
          IsDataModule   -> "(datatype)"
          IsRecordModule -> "(record)"

    ModuleArityMismatch m EmptyTel args -> fsep $
      pwords "The module" ++ [prettyTCM m] ++
      pwords "is not parameterized, but is being applied to arguments"

    ModuleArityMismatch m tel@(ExtendTel _ _) args -> fsep $
      pwords "The arguments to " ++ [prettyTCM m] ++ pwords "do not fit the telescope" ++
      [prettyTCM tel]

    ShouldBeEmpty t [] -> fsep $
       prettyTCM t : pwords "should be empty, but that's not obvious to me"

    ShouldBeEmpty t ps -> fsep (
      prettyTCM t :
      pwords "should be empty, but the following constructor patterns are valid:"
      ) $$ nest 2 (vcat $ map (prettyPat 0) ps)

    ShouldBeASort t -> fsep $
      prettyTCM t : pwords "should be a sort, but it isn't"

    ShouldBePi t -> fsep $
      prettyTCM t : pwords "should be a function type, but it isn't"

    ShouldBePath t -> fsep $
      prettyTCM t : pwords "should be a Path or PathP type, but it isn't"

    InvalidTypeSort s -> fsep $ prettyTCM s : pwords "is not a valid sort"

    CannotSolveSizeConstraints ccs reason -> do
      -- Print the HypSizeConstraints (snd)
      vcat $ concat
        [ [ text $ "Cannot solve size constraints" ]
        , List1.toList $ fmap (prettyTCM . snd) ccs
        , [ "Reason:" <+> pure reason | not (null reason) ]
        ]

    ContradictorySizeConstraint cc@(_,c0) -> fsep $
      pwords "Contradictory size constraint" ++ [prettyTCM c0]

    EmptyTypeOfSizes t -> fsep $ pwords "Possibly empty type of sizes:" ++ [prettyTCM t]

    FunctionTypeInSizeUniv v -> fsep $
      pwords "Functions may not return sizes, thus, function type " ++
      [ prettyTCM v ] ++ pwords " is illegal"

    SplitOnCoinductive -> fsep $ pwords "Pattern matching on coinductive types is not allowed"

    SplitOnIrrelevant t -> fsep $
      pwords "Cannot pattern match against" ++ [text $ verbalize $ getRelevance t] ++
      pwords "argument of type" ++ [prettyTCM $ unDom t]

    SplitOnUnusableCohesion t -> fsep $
      pwords "Cannot pattern match against" ++ [text $ verbalize $ getCohesion t] ++
      pwords "argument of type" ++ [prettyTCM $ unDom t]

    SplitOnUnusablePolarity t -> fsep $
      pwords "Cannot pattern match against" ++ [text $ verbalize $ getModalPolarity t] ++
      pwords "argument of type" ++ [prettyTCM $ unDom t]

    -- UNUSED:
    -- SplitOnErased t -> fsep $
    --   pwords "Cannot pattern match against" ++ [text $ verbalize $ getQuantity t] ++
    --   pwords "argument of type" ++ [prettyTCM $ unDom t]

    SplitOnNonVariable v t -> fsep $
      pwords "Cannot pattern match because the (refined) argument " ++
      [ prettyTCM v ] ++ pwords " is not a variable."

    SplitOnNonEtaRecord q -> fsep $ concat
      [ pwords "Pattern matching on no-eta record type"
      , [ prettyTCM q, parens ("defined at" <+> prettyTCM r) ]
      , pwords "is not allowed"
      , [ parens "to activate, add declaration `pattern` to record definition" ]
      ]
      where r = nameBindingSite $ qnameName q

    SplitOnAbstract d ->
      "Cannot split on abstract data type" <+> prettyTCM d

    SplitOnUnchecked d ->
      "Cannot split on data type" <+> prettyTCM d <+> "whose definition has not yet been checked"

    SplitOnPartial dom -> vcat
      [ "Splitting on partial elements is only allowed at the type Partial, but the domain here is", nest 2 $ prettyTCM $ unDom dom ]

    SplitInProp dr -> fsep
      [ text "Cannot split on"
      , text $ kindOfData dr
      , text "in Prop unless target is in Prop"
      ]
      where
        kindOfData :: DataOrRecordE -> String
        kindOfData IsData                                                          = "datatype"
        kindOfData (IsRecord InductionAndEta {recordInduction=Nothing})            = "record type"
        kindOfData (IsRecord InductionAndEta {recordInduction=(Just Inductive)})   =  "inductive record type"
        kindOfData (IsRecord InductionAndEta {recordInduction=(Just CoInductive)}) = "coinductive record type"


    DefinitionIsIrrelevant x -> fsep $
      "Identifier" : prettyTCM x : pwords "is declared irrelevant, so it cannot be used here"

    DefinitionIsErased x -> fsep $
      "Identifier" : prettyTCM x : pwords "is declared erased, so it cannot be used here"

    ProjectionIsIrrelevant x -> vcat
      [ fsep [ "Projection " , prettyTCM x, " is irrelevant." ]
      , "Turn on option --irrelevant-projections to use it (unsafe)"
      ]

    VariableIsIrrelevant x -> fsep $
      "Variable" : prettyTCM (nameConcrete x) : pwords "is declared irrelevant, so it cannot be used here"

    VariableIsErased x -> fsep $
      "Variable" : prettyTCM (nameConcrete x) : pwords "is declared erased, so it cannot be used here"

    VariableIsOfUnusableCohesion x c -> fsep
      ["Variable", prettyTCM (nameConcrete x), "is declared", text (show c), "so it cannot be used here"]

    InvalidModalTelescopeUse t used avail def -> fsep
      [ "Telescope variable" <+> prettyTCM t
      , "is indirectly being used in the" <+> text (verbalize (getModality used)) <+> "modality"
      , "but only available in the" <+> text (verbalize (getModality avail)) <+> "modality"
      , "when inserting into the telescope of definition"
      , pretty (defName def) <+> ":" <+> prettyTCM (defType def)
      ]

    VariableIsOfUnusablePolarity x c -> fsep $
      ["Variable", prettyTCM (nameConcrete x), "is bound with", text (verbalize p)] ++  pwords "polarity, so it cannot be used here at" ++
      [text (verbalize (Indefinite l)), "position"]
      where
        PolarityModality _ p l = c

    UnequalTerms cmp s t a -> case (s,t) of
      (Sort s1      , Sort s2      )
        | CmpEq  <- cmp              -> prettyTCM $ UnequalSorts s1 s2
        | CmpLeq <- cmp              -> prettyTCM $ NotLeqSort s1 s2
      (Sort MetaS{} , t            ) -> prettyTCM $ ShouldBeASort $ El __IMPOSSIBLE__ t
      (s            , Sort MetaS{} ) -> prettyTCM $ ShouldBeASort $ El __IMPOSSIBLE__ s
      (Sort DefS{}  , t            ) -> prettyTCM $ ShouldBeASort $ El __IMPOSSIBLE__ t
      (s            , Sort DefS{}  ) -> prettyTCM $ ShouldBeASort $ El __IMPOSSIBLE__ s
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

    UnequalRelevance cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because one is a relevant function type and the other is an irrelevant function type"

    UnequalQuantity cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because one is a non-erased function type and the other is an erased function type"

    UnequalCohesion cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because one is a non-flat function type and the other is a flat function type"
      -- FUTURE Cohesion: update message if/when introducing sharp.

    UnequalPolarity cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because they do not have the same polarity annotations"

    UnequalFiniteness cmp a b -> fsep $
      [prettyTCM a, notCmp cmp, prettyTCM b] ++
      pwords "because one is a type of partial elements and the other is a function type"
      -- FUTURE Cohesion: update message if/when introducing sharp.

    UnequalHiding a b -> fsep $
      [prettyTCM a, "!=", prettyTCM b] ++
      pwords "because one is an implicit function type and the other is an explicit function type"

    UnequalSorts s1 s2 -> fsep $
      [prettyTCM s1, "!=", prettyTCM s2]

    NotLeqSort s1 s2 -> fsep $
      [prettyTCM s1] ++ pwords "is not less or equal than" ++ [prettyTCM s2]

    TooManyFields r missing xs -> prettyTooManyFields r missing xs

    DuplicateConstructors xs -> fsep $ concat
      [ [ "Duplicate" ]
      , [ pluralS xs "constructor" ]
      , punctuate comma $ fmap pretty xs
      , pwords "in datatype"
      ]

    DuplicateFields xs -> prettyDuplicateFields xs

    DuplicateOverlapPragma q old new -> fsep $
      pwords "The instance" ++ [prettyTCM q] ++
      pwords "was already marked" ++ [pretty old <> "."] ++
      pwords "This" ++ [pretty new] ++
      pwords "pragma can not be applied to it."

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
      pwords "Unexpected with patterns" ++ punctuate " |" (fmap prettyA ps)

    TooFewPatternsInWithClause -> fsep $ pwords "Too few arguments given in with-clause"
    TooManyPatternsInWithClause -> fsep $ pwords "Too many arguments given in with-clause"

    WithClausePatternMismatch p q -> fsep $
      pwords "With clause pattern " ++ [prettyA p] ++
      pwords " is not an instance of its parent pattern " ++ [P.fsep <$> prettyTCMPatterns [q]]

    MetaCannotDependOn m v i ->
      ifM (isSortMeta m `and2M` (not <$> hasUniversePolymorphism))
      ( {- then -}
        fsep [ text "Cannot instantiate the metavariable"
             , prettyTCM m
             , "to"
             , prettyTCM v
             , "since universe polymorphism is disabled"
             ]
      ) {- else -}
      ( fsep [ text "Cannot instantiate the metavariable"
             , prettyTCM m
             , "to solution"
             , prettyTCM v
             , "since it contains the variable"
             , prettyTCM (I.Var i [])
             , "which is not in scope of the metavariable"
             ]
        )
    MetaIrrelevantSolution m v ->
      fsep [ text "Cannot instantiate the metavariable"
           , prettyTCM m
           , "to solution"
           , prettyTCM v
           , "since (part of) the solution was created in an irrelevant context"
           ]

    MetaErasedSolution m v  ->
      fsep [ text "Cannot instantiate the metavariable"
           , prettyTCM m
           , "to solution"
           , prettyTCM v
           , "since (part of) the solution was created in an erased context"
           ]

    BuiltinMustBeConstructor s e -> fsep $
      [prettyA e] ++ pwords "must be a constructor in the binding to builtin" ++ [pretty s]

    NoSuchBuiltinName s -> fsep $
      pwords "There is no built-in thing called" ++ [pretty s]

    DuplicateBuiltinBinding b x y -> fsep $
      pwords "Duplicate binding for built-in thing" ++ [pretty b <> comma] ++
      pwords "previous binding to" ++ [prettyTCM x]

    NoBindingForBuiltin x
      | x `elem` [builtinZero, builtinSuc] -> fsep $
        pwords "No binding for builtin " ++ [pretty x <> comma] ++
        pwords ("use {-# BUILTIN " ++ getBuiltinId builtinNat ++ " name #-} to bind builtin natural " ++
                "numbers to the type 'name'")
      | otherwise -> fsep $
        pwords "No binding for builtin thing" ++ [pretty x <> comma] ++
        pwords ("use {-# BUILTIN " ++ getBuiltinId x ++ " name #-} to bind it to 'name'")

    NoBindingForPrimitive x -> fsep $
      pwords "Missing binding for" ++
      [pretty x] ++
      pwords "primitive."

    DuplicatePrimitiveBinding b x y -> fsep $
      pwords "Duplicate binding for primitive thing" ++ [pretty b <> comma] ++
      pwords "previous binding to" ++ [prettyTCM x]

    NoSuchPrimitiveFunction x -> fsep $
      pwords "There is no primitive function called" ++ [text x]

    WrongArgInfoForPrimitive x got expect ->
      vcat [ fsep $ pwords "Wrong definition properties for primitive" ++ [pretty x]
           , nest 2 $ text $ "Got:      " ++ intercalate ", " gs
           , nest 2 $ text $ "Expected: " ++ intercalate ", " es ]
      where
        (gs, es) = unzip [ p | p@(g, e) <- zip (things got) (things expect), g /= e ]
        things i = [verbalize $ getHiding i,
                    "at modality " ++ verbalize (getModality i)]

    BuiltinInParameterisedModule x -> fwords $
      "The BUILTIN pragma cannot appear inside a bound context " ++
      "(for instance, in a parameterised module or as a local declaration)"

    IllegalDeclarationInDataDefinition ds -> vcat
      [ "Illegal declaration in data type definition"
      , nest 2 $ vcat $ fmap pretty ds
      ]

    IllegalLetInTelescope tb -> fsep $
      -- pwords "The binding" ++
      pretty tb :
      pwords " is not allowed in a telescope here."

    IllegalPatternInTelescope bd -> fsep $
      pretty bd :
      pwords " is not allowed in a telescope here."

    AbsentRHSRequiresAbsurdPattern -> fwords $
      "The right-hand side can only be omitted if there " ++
      "is an absurd pattern, () or {}, in the left-hand side."

    LibraryError err -> return $ formatLibErrors err

    LibTooFarDown m lib -> vcat
      [ text "A .agda-lib file for" <+> pretty m
      , text "must not be located in the directory" <+> text (takeDirectory (lib ^. libFile))
      ]

    SolvedButOpenHoles -> fsep $
      pwords "Module cannot be imported since it has open interaction points" ++
      pwords "(consider adding {-# OPTIONS --allow-unsolved-metas #-} to this module)"

    CyclicModuleDependency (List2 m0 m1 ms) ->
      fsep (pwords "cyclic module dependency:")
      $$ nest 2 (vcat $ (pretty m0 :) $ map (("importing" <+>) . pretty) (m1 : ms))

    FileNotFound x files ->
      fsep ( pwords "Failed to find source of module" ++ [pretty x] ++
             pwords "in any of the following locations:"
           ) $$ nest 2 (vcat $ map (text . filePath) files)

    OverlappingProjects f m1 m2
      | canon d1 == canon d2 -> fsep $ concat
          [ pwords "Case mismatch when accessing file"
          , [ text $ filePath f ]
          , pwords "through module name"
          , [ pure d2 ]
          ]
      | otherwise -> fsep
           ( pwords "The file" ++ [text (filePath f)] ++
             pwords "can be accessed via several project roots. Both" ++
             [ pure d1 ] ++ pwords "and" ++ [ pure d2 ] ++
             pwords "point to this file."
           )
      where
      canon = CaseInsens.mk . P.render
      d1 = P.pretty m1
      d2 = P.pretty m2

    AmbiguousTopLevelModuleName x files ->
      fsep ( pwords "Ambiguous module name. The module name" ++
             [pretty x] ++
             pwords "could refer to any of the following files:"
           ) $$ nest 2 (vcat $ fmap (text . filePath) files)

    AmbiguousProjection d disambs -> vcat
      [ "Ambiguous projection " <> prettyTCM d <> "."
      , "It could refer to any of"
      , nest 2 $ vcat $ fmap prettyDisambProj $ List2.cons d disambs
      ]

    AmbiguousOverloadedProjection ds reason -> do
      let nameRaw = pretty $ A.nameConcrete $ A.qnameName $ List1.head ds
      vcat
        [ fsep
          [ text "Cannot resolve overloaded projection"
          , nameRaw
          , text "because"
          , pure reason
          ]
        , nest 2 $ text "candidates in scope:"
        , vcat $ for ds $ \ d -> do
            t <- typeOfConst d
            text "-" <+> nest 2 (nameRaw <+> text ":" <+> prettyTCM t)
        ]

    AmbiguousConstructor c disambs -> vcat
      [ "Ambiguous constructor " <> pretty (qnameName c) <> "."
      , "It could refer to any of"
      , nest 2 $ vcat $ fmap prettyDisambCons disambs
      ]

    InvalidFileName file reason -> fsep $
      pwords "The file name" ++ [pretty file] ++ pwords "is invalid because" ++
      case reason of
        DoesNotCorrespondToValidModuleName ->
          pwords "it does not correspond to a valid module name."
        RootNameModuleNotAQualifiedModuleName defaultName ->
          pretty defaultName : pwords "is not an unqualified module name."

    ModuleDefinedInOtherFile mod file file' -> fsep $
      pwords "You tried to load" ++ [text (filePath file)] ++
      pwords "which defines the module" ++ [pretty mod <> "."] ++
      pwords "However, according to the include path this module should" ++
      pwords "be defined in" ++ [text (filePath file') <> "."]

    ModuleNameUnexpected given expected
      | canon dGiven == canon dExpected -> fsep $ concat
          [ pwords "Case mismatch between the actual module name"
          , [ pure dGiven ]
          , pwords "and the expected module name"
          , [ pure dExpected ]
          ]
      | otherwise -> fsep $ concat
          [ pwords "The name of the top level module does not match the file name. The module"
          , [ pure dGiven ]
          , pwords "should probably be named"
          , [ pure dExpected ]
          ]
      where
      canon = CaseInsens.mk . P.render
      dGiven    = P.pretty given
      dExpected = P.pretty expected


    ModuleNameDoesntMatchFileName given files ->
      fsep (pwords "The name of the top level module does not match the file name. The module" ++
           [ pretty given ] ++ pwords "should be defined in one of the following files:")
      $$ nest 2 (vcat $ map (text . filePath) files)

    AbstractConstructorNotInScope q -> fsep $
      [ "Constructor"
      , prettyTCM q
      ] ++ pwords "is abstract, thus, not in scope here"

    CopatternHeadNotProjection x -> fsep $ concat
      [ pwords "Head of copattern needs to be a projection, but"
      , [ prettyTCM x ]
      , pwords "isn't one"
      ]

    NotAllowedInDotPatterns what -> fsep $ verb what ++ pwords "are not allowed in dot patterns"
      where
      verb = \case
        LetExpressions -> pwords "Let expressions"
        PatternLambdas -> pwords "Pattern lambdas"

    NotInScope x ->
      -- using the warning version to avoid code duplication
      prettyWarning $ NotInScopeW x

    NoSuchModule x -> fsep $ pwords "No module" ++ [pretty x] ++ pwords "in scope"

    AmbiguousName x reason -> vcat
      [ fsep $ pwords "Ambiguous name" ++ [pretty x <> "."] ++
               pwords "It could refer to any one of"
      , nest 2 $ vcat $ fmap nameWithBinding $ ambiguousNamesInReason reason
      , explainWhyInScope $ whyInScopeDataFromAmbiguousNameReason x reason
      ]

    AmbiguousModule x ys -> vcat
      [ fsep $ pwords "Ambiguous module name" ++ [pretty x <> "."] ++
               pwords "It could refer to any one of"
      , nest 2 $ vcat $ fmap help ys
      , fwords "(hint: Use C-c C-w (in Emacs) if you want to know why)"
      ]
      where
        help :: MonadPretty m => ModuleName -> m Doc
        help m = do
          anno <- caseMaybeM (isDatatypeModule m) (return empty) $ \case
            IsDataModule   -> return $ "(datatype module)"
            IsRecordModule -> return $ "(record module)"
          sep [prettyTCM m, anno ]

    AmbiguousField field modules -> vcat $
      hsep [ "Ambiguity: the field", prettyTCM field, "appears in the following modules:" ]
      : map prettyTCM (List2.toList modules)

    ClashingDefinition x y suggestion -> fsep $
      pwords "Multiple definitions of" ++ [pretty x <> "."] ++
      pwords "Previous definition at"
      ++ [prettyTCM $ nameBindingSite $ qnameName y] ++
      caseMaybe suggestion [] (\d ->
        [  "Perhaps you meant to write "
        $$ nest 2 ("'" <> pretty (notSoNiceDeclarations d) <> "'")
        $$ ("at" <+> (pretty . envRange =<< askTC)) <> "?"
        $$ "In data definitions separate from data declaration, the ':' and type must be omitted."
        ])

    ClashingModule m1 m2 -> fsep $
      pwords "The modules" ++ [prettyTCM m1, "and", prettyTCM m2]
      ++ pwords "clash."

    DuplicateImports m xs -> fsep $
      pwords "Ambiguous imports from module" ++ [pretty m] ++ pwords "for" ++
      punctuate comma (fmap pretty xs)

    DefinitionInDifferentModule _x -> fsep $
      pwords "Definition in different module than its type signature"

    FieldOutsideRecord -> fsep $
      pwords "Field appearing outside record declaration."

    PrivateRecordField -> fwords "Record fields cannot be private"

    InvalidPattern p -> fsep $
      pretty p : pwords "is not a valid pattern"

    InvalidPun kind x -> fsep $ concat
      [ pwords "A pun must not use the"
      , [ pure $ P.pretty kind ]
      , [ prettyTCM x ]
      ]

    RepeatedVariablesInPattern xs -> fsep $
      pwords "Repeated variables in pattern:" ++ map pretty (List1.toList xs)

    RepeatedNamesInImportDirective yss -> fsep
      [ fsep $ concat
         [ [ "Repeated" , pluralS yss "name" ]
         , pwords "in import directive:"
         ]
      , fsep $ punctuate comma $ fmap (prettyTCM . List2.head) yss
      ]

    DeclarationsAfterTopLevelModule -> fwords $ "No declarations allowed after top-level module."

    IllegalDeclarationBeforeTopLevelModule -> fwords $ "Illegal declaration(s) before top-level module"

    MissingTypeSignature info -> fwords "Missing type signature for" <+> prettyTCM info

    NotAnExpression e -> fsep $
      pretty e : pwords "is not a valid expression."

    NotAValidLetBinding Nothing -> fwords $ "Not a valid let binding"
    NotAValidLetBinding (Just err) -> fwords $ verbalizeNotAValidLetBinding err

    NotAValidLetExpression err -> fwords $ verbalizeNotAValidLetExpression err

    NotValidBeforeField nd -> fwords $
      "This declaration is illegal in a record before the last field"

    NoParseForApplication es -> fsep (
      pwords "Could not parse the application" ++ [pretty $ C.RawApp noRange es])

    AmbiguousParseForApplication es es' -> fsep (
      pwords "Don't know how to parse" ++ [pretty_es <> "."] ++
      pwords "Could mean any one of:"
      ) $$ nest 2 (vcat $ fmap pretty' es')
      where
        pretty_es :: MonadPretty m => m Doc
        pretty_es = pretty $ C.RawApp noRange es

        pretty' :: MonadPretty m => C.Expr -> m Doc
        pretty' e = do
          p1 <- pretty_es
          p2 <- pretty e
          if render p1 == render p2 then unambiguous e else return p2

        unambiguous :: MonadPretty m => C.Expr -> m Doc
        unambiguous e@(C.OpApp r op _ xs)
          | all (isOrdinary . namedArg) xs =
            pretty $
              foldl (C.App r) (C.Ident op) $
                (fmap . fmap . fmap) fromOrdinary xs
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

    AsPatternInPatternSynonym -> fsep $ pwords "@-patterns are not allowed in pattern synonyms"

    DotPatternInPatternSynonym -> fsep $ pwords
      "Dot or equality patterns are not allowed in pattern synonyms. Maybe use '_' instead."

    BadArgumentsToPatternSynonym x -> fsep $
      pwords "Bad arguments to pattern synonym " ++ [prettyTCM $ headAmbQ x]

    TooFewArgumentsToPatternSynonym x -> fsep $
      pwords "Too few arguments to pattern synonym " ++ [prettyTCM $ headAmbQ x]

    CannotResolveAmbiguousPatternSynonym defs -> vcat
      [ fsep $ pwords "Cannot resolve overloaded pattern synonym" ++ [prettyTCM x <> comma] ++
               pwords "since candidates have different shapes:"
      , nest 2 $ vcat $ fmap prDef defs
      , fsep $ pwords "(hint: overloaded pattern synonyms must be equal up to variable and constructor names)"
      ]
      where
        (x, _) = List1.head defs
        prDef (x, (xs, p)) = prettyA (A.PatternSynDef x (map (fmap BindName) xs) p) <?> ("at" <+> pretty r)
          where r = nameBindingSite $ qnameName x

    IllegalInstanceVariableInPatternSynonym x -> fsep $ concat
      [ pwords "Variable is bound as instance in pattern synonym,"
      , pwords "but does not resolve as instance in pattern: "
      , [pretty x]
      ]

    PatternSynonymArgumentShadows kind x (y :| _ys) -> vcat
      [ fsep $ concat
        [ pwords "Pattern synonym variable"
        , [ pretty x ]
        , [ "shadows" ]
        , [ pretty kind ]
        , pwords "defined at:"
        ]
      , pretty $ nameBindingSite $ qnameName $ anameName y
      ]

    UnusedVariableInPatternSynonym x -> fsep $
      pwords "Unused variable in pattern synonym: " ++ [pretty x]

    UnboundVariablesInPatternSynonym xs -> fsep $
      pwords "Unbound variables in pattern synonym: " ++
      [sep (fmap prettyA xs)]

    NoParseForLHS lhsOrPatSyn errs p -> vcat
      [ fsep $ pwords "Could not parse the" ++ prettyLhsOrPatSyn ++ [pretty p]
      , prettyErrs
      ]
      where
      prettyLhsOrPatSyn = pwords $ case lhsOrPatSyn of
        IsLHS    -> "left-hand side"
        IsPatSyn -> "pattern synonym right-hand side"
      prettyErrs = case errs of
        []     -> empty
        p0 : _ -> fsep $ pwords "Problematic expression:" ++ [pretty p0]

    AmbiguousParseForLHS lhsOrPatSyn p ps -> do
      d <- pretty p
      vcat $
        [ fsep $
            pwords "Don't know how to parse" ++ [pure d <> "."] ++
            pwords "Could mean any one of:"
        ]
          ++
        map (nest 2 . pretty' d) (List2.toList ps)
      where
        pretty' :: MonadPretty m => Doc -> C.Pattern -> m Doc
        pretty' d1 p' = do
          d2 <- pretty p'
          if render d1 == render d2 then pretty $ unambiguousP p' else return d2

        -- the entire pattern is shown, not just the ambiguous part,
        -- so we need to dig in order to find the OpAppP's.
        unambiguousP :: C.Pattern -> C.Pattern
        unambiguousP (C.AppP x y)         = C.AppP (unambiguousP x) $ (fmap.fmap) unambiguousP y
        unambiguousP (C.HiddenP r x)      = C.HiddenP r $ fmap unambiguousP x
        unambiguousP (C.InstanceP r x)    = C.InstanceP r $ fmap unambiguousP x
        unambiguousP (C.ParenP r x)       = C.ParenP r $ unambiguousP x
        unambiguousP (C.AsP r n x)        = C.AsP r n $ unambiguousP x
        unambiguousP (C.OpAppP r op _ xs) = foldl C.AppP (C.IdentP True op) xs
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
               sortBy (compare `on` prettyShow . notaName . sectNotation) $
               filter (not . closedWithoutHoles) sects))
      where
      trimLeft  = dropWhile isAHole
      trimRight = dropWhileEnd isAHole

      closedWithoutHoles sect =
        sectKind sect == NonfixNotation
          &&
        null [ () | HolePart{} <- trimLeft $ trimRight $
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
                           (List1.init (C.qnameParts (notaName nota))))
                    (spacesBetweenAdjacentIds $
                     trim (notation nota))

        qualifyFirstIdPart _ []              = []
        qualifyFirstIdPart q (IdPart x : ps) = IdPart (fmap (q ++) x) : ps
        qualifyFirstIdPart q (p : ps)        = p : qualifyFirstIdPart q ps

        spacesBetweenAdjacentIds (IdPart x : ps@(IdPart _ : _)) =
          IdPart x : IdPart (unranged " ") : spacesBetweenAdjacentIds ps
        spacesBetweenAdjacentIds (p : ps) =
          p : spacesBetweenAdjacentIds ps
        spacesBetweenAdjacentIds [] = []

        trim = case sectKind sect of
          InfixNotation   -> trimLeft . trimRight
          PrefixNotation  -> trimRight
          PostfixNotation -> trimLeft
          NonfixNotation  -> id
          NoNotation      -> __IMPOSSIBLE__

        (names, name) = List1.initLast $ Set1.toList $ notaNames nota

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

    RecursiveRecordNeedsInductivity q -> fsep $ concat
      [ pwords "Recursive record"
      , [ prettyTCM q ]
      , pwords "needs to be declared as either inductive or coinductive"
      ]

    InstanceNoCandidate t errs -> vcat $
      [ fsep $ pwords "No instance of type" ++ [prettyTCM t] ++ pwords "was found in scope."
      , vcat $ map prCand errs ]
      where
        prCand (term, err) =
          text "-" <+>
            vcat [ prettyTCM term <?> text "was ruled out because"
                 , prettyTCM err ]

    UnquoteFailed e -> prettyTCM e

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

    NeedOptionAllowExec -> fsep $
      pwords "Option --allow-exec needed to call external commands from macros"

    NeedOptionCopatterns -> fsep $
      pwords "Option --copatterns needed to enable destructor patterns"

    NeedOptionCubical cubical reason -> fsep $ concat
        [ [ "Option" ], opt, [ "required" ]
        , pwords reason
        ]
      where
      opt = case cubical of
        CFull   -> [ "--cubical" ]
        CErased -> pwords $ "--cubical or --erased-cubical"

    NeedOptionPatternMatching -> fsep $
      pwords "Pattern matching is disabled (use option --pattern-matching to enable it)"

    NeedOptionProp       -> fsep $
      pwords "Universe Prop is disabled (use options --prop and --no-prop to enable/disable Prop)"

    NeedOptionRewriting  -> fsep $
      pwords "Option --rewriting needed to add and use rewrite rules"

    NeedOptionSizedTypes reason -> fsep $
      pwords "Option --sized-types needed" ++ pwords reason

    NeedOptionTwoLevel   -> fsep $
      pwords "Universe SSet is disabled (use option --two-level to enable SSet)"

    NeedOptionUniversePolymorphism -> fsep $
      pwords "Universe polymorphism is disabled (use option --universe-polymorphism to allow level arguments to sorts)"

    GeneralizeNotSupportedHere x -> fsep $
      pwords $ "Generalizable variable " ++ prettyShow x ++ " is not supported here"

    GeneralizeCyclicDependency -> fsep $
      pwords "Cyclic dependency between generalized variables"

    GeneralizedVarInLetOpenedModule x -> fsep $
      pwords "Cannot use generalized variable from let-opened module: " ++
      [prettyTCM x]

    MultipleFixityDecls xs ->
      sep [ fsep $ pwords "Multiple fixity or syntax declarations for"
          , vcat $ fmap f xs
          ]
      where
        f (x, fs) = (pretty x <> ": ") <+> fsep (fmap pretty fs)

    MultiplePolarityPragmas xs -> fsep $
      pwords "Multiple polarity pragmas for" ++ map pretty (List1.toList xs)

    CannotQuote what -> do
      fwords "`quote' expects an unambiguous defined name," $$ do
      fsep $ pwords "but here the argument is" ++
        case what of
          CannotQuoteNothing ->
            pwords "missing"
          CannotQuoteHidden ->
            pwords "implicit"
          CannotQuoteAmbiguous (List2 x y zs) ->
            pwords "ambiguous:" ++ [ pretty $ AmbQ $ x :| y : zs ]
          CannotQuoteExpression e -> case e of
            -- These expression can be quoted:
            A.Def' _ NoSuffix -> __IMPOSSIBLE__
              -- Andreas, 2024-09-27, issue #7514:
              -- Why only quote suffix-free universes?
            A.Macro        {} -> __IMPOSSIBLE__
            A.Proj         {} -> __IMPOSSIBLE__
            A.Con          {} -> __IMPOSSIBLE__
            A.DontCare     {} -> __IMPOSSIBLE__
            A.ScopedExpr   {} -> __IMPOSSIBLE__
            -- These cannot:
            A.PatternSyn   {} -> other "a pattern synonym:"
            A.Var          {} -> other "a variable:"
            A.Lit          {} -> other "a literal:"
            A.QuestionMark {} -> pwords "a metavariable"
            A.Underscore   {} -> pwords "a metavariable"
            _ ->
              pwords "a compound expression"
            where
              other s = pwords s ++ [ prettyTCM e]
          CannotQuotePattern p -> case namedArg p of
            C.IdentP    {} -> __IMPOSSIBLE__
            C.HiddenP   {} -> __IMPOSSIBLE__
            C.InstanceP {} -> __IMPOSSIBLE__
            C.RawAppP   {} -> __IMPOSSIBLE__
            C.AbsurdP   {} -> pwords "an absurd pattern"
            C.LitP      {} -> pwords "a literal pattern"
            C.WildP     {} -> pwords "a wildcard pattern"
            _ ->
              pwords "a compound pattern"

    CannotQuoteTerm what -> do
      fwords "`quoteTerm' expects a single visible argument," $$ do
      fsep $ pwords "but has been given" ++
        case what of
          CannotQuoteTermNothing ->
            pwords "none"
          CannotQuoteTermHidden ->
            pwords "an implicit one"


    ConstructorNameOfNonRecord res -> case res of
      UnknownName -> __IMPOSSIBLE__ -- Turned into NotInScope when the name is resolved
      name ->
        let
          qn :: m Doc
          (qn, whatis) = case name of
            DefinedName _ nm _ -> (prettyTCM nm,) case anameKind nm of
              RecName                  -> __IMPOSSIBLE__
              ConName                  -> __IMPOSSIBLE__
              CoConName                -> __IMPOSSIBLE__
              FldName                  -> __IMPOSSIBLE__
              PatternSynName           -> __IMPOSSIBLE__

              GeneralizeName           -> "a generalized variable"
              DisallowedGeneralizeName -> "a generalized variable"
              MacroName                -> "a macro"
              QuotableName             -> "a quotable name"

              DataName                 -> "a data type"
              FunName                  -> "a function"
              AxiomName                -> "a postulate"
              PrimName                 -> "a primitive"
              OtherDefName             -> "a defined symbol"
            VarName a _ -> (prettyTCM a, "a local variable")
            FieldName (a :| _) -> (prettyTCM a, "a projection")
            ConstructorName _ (a :| _) -> (prettyTCM a, "a constructor")
            PatternSynResName (a :| _) -> (prettyTCM a, "a pattern synonym")
        in fsep $ pwords "Only record types have constructor names, but" ++ [qn, "is"] ++ pwords (whatis <> ".")

    NonFatalErrors ws -> vsep $ fmap prettyTCM $ Set1.toAscList ws

    ExplicitPolarityVsPragma p -> fsep $
      pwords "Polarity pragma used for " ++ [ prettyTCM p ] ++ pwords " but its type is already annotated with polarities."

    InstanceSearchDepthExhausted c a d -> fsep $
      pwords ("Instance search depth exhausted (max depth: " ++ show d ++ ") for candidate") ++
      [hang (prettyTCM c <+> ":") 2 (prettyTCM a)]

    TriedToCopyConstrainedPrim q -> fsep $
      pwords "Cannot create a module containing a copy of" ++ [prettyTCM q]

    InvalidInstanceHeadType _ why -> fsep $ case why of
      ImproperInstHead -> pwords "Instance search can only be used to find elements in a named type"
      ImproperInstTele -> pwords "Instance search cannot be used to find elements in an explicit function type"

    SortOfSplitVarError _ doc -> return doc

    ReferencesFutureVariables term (disallowed :| _) lock leftmost
      | disallowed == leftmost
      -> fsep $ pwords "The lock variable"
             ++ pure (prettyTCM =<< nameOfBV disallowed)
             ++ pwords "can not appear simultaneously in the \"later\" term"
             ++ pure (prettyTCM term)
             ++ pwords "and in the lock term"
             ++ pure (prettyTCM lock <> ".")

    ReferencesFutureVariables term (disallowed :| rest) lock leftmost -> do
      explain <- (/=) <$> prettyTCM lock <*> (prettyTCM =<< nameOfBV leftmost)
      let
        name = prettyTCM =<< nameOfBV leftmost
        mod = case getLock lock of
          IsLock LockOLock -> "@lock"
          IsLock LockOTick -> "@tick"
          _ -> __IMPOSSIBLE__
      vcat $ concat
        [ pure . fsep $ concat
          [ pwords "The variable", pure (prettyTCM =<< nameOfBV disallowed), pwords "can not be mentioned here,"
          , pwords "since it was not introduced before the variable", pure (name <> ".")
          ]
        , [ fsep ( pwords "Variables introduced after"
                ++ pure name
                ++ pwords "can not be used, since that is the leftmost" ++ pure mod ++ pwords "variable in the locking term"
                ++ pure (prettyTCM lock <> "."))
          | explain
          ]
        , [ fsep ( pwords "The following"
                  ++ P.singPlural rest (pwords "variable is") (pwords "variables are")
                  ++ pwords "not allowed here, either:"
                  ++ punctuate comma (map (prettyTCM <=< nameOfBV) rest))
          | not (null rest)
          ]
        ]

    DoesNotMentionTicks term ty lock ->
      let
        mod = case getLock lock of
          IsLock LockOLock -> "@lock"
          IsLock LockOTick -> "@tick"
          _ -> __IMPOSSIBLE__
      in
        vcat
        [ fsep $
            pwords "The term"
            ++ [prettyTCM lock <> ","]
            ++ pwords "given as an argument to the guarded value"
        , nest 2 (prettyTCM term <+> ":" <+> prettyTCM ty)
        , fsep (pwords ("can not be used as a " ++ mod ++ " argument, since it does not mention any " ++ mod ++ " variables."))
        ]

    MismatchedProjectionsError left right -> fsep $
      pwords "The projections" ++ [prettyTCM left] ++
      pwords "and" ++ [prettyTCM right] ++
      pwords "do not match"

    AttributeKindNotEnabled kind opt s -> fsep $
      [text kind] ++
      pwords "attributes have not been enabled (use" ++
      [text opt] ++
      pwords "to enable them):" ++
      [text s]

    InvalidProjectionParameter arg -> fsep $
      pwords "Invalid projection parameter " ++
      [prettyA arg]

    TacticAttributeNotAllowed -> fsep $
      pwords "The @tactic attribute is not allowed here"

    CannotRewriteByNonEquation t ->
      "Cannot rewrite by equation of type" <+> prettyTCM t

    MacroResultTypeMismatch expectedType ->
      sep [ "Result type of a macro must be", nest 2 $ prettyTCM expectedType ]

    NamedWhereModuleInRefinedContext args names -> do
      let pr x v = text (x ++ " =") <+> prettyTCM v
      vcat
        [ fsep (pwords $ "Named where-modules are not allowed when module parameters have been refined by pattern matching. " ++
                          "See https://github.com/agda/agda/issues/2897.")
        , text $ "In this case the module parameter" ++
                  (if not (null args) then "s have" else " has") ++
                  " been refined to"
        , nest 2 $ vcat (zipWith pr names args) ]

    CannotGenerateHCompClause ty -> fsep $ concat
        [ pwords "Cannot generate hcomp clause at type"
        , [ prettyTCM ty ]
        ]

    CannotGenerateTransportClause f clos ->
      enterClosure clos \ failed_t -> addContext ("i" :: String, __DUMMY_DOM__) $ vcat
        [ "Could not generate a transport clause for" <+> prettyTCM f
        , "because a term of type" <+> prettyTCM (unAbs failed_t)
        , "lives in the sort" <+> prettyTCM (getSort (unAbs failed_t))
        , "and thus can not be transported"
        ]

    CubicalPrimitiveNotFullyApplied c ->
      prettyTCM c <+> "must be fully applied"

    ExpectedIntervalLiteral e -> do
      i0 <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIZero
      i1 <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIOne
      fsep $ concat
        [ pwords "Expected an interval literal"
        , [ parens $ fsep [ prettyTCM i0, "or", prettyTCM i1 ] ]
        , pwords "but found:"
        , [ prettyTCM e ]
        ]

    PatternInPathLambda ->
      fwords $ "Patterns are not allowed in Path-lambdas"

    PatternInSystem ->
      fwords $ "Pattern matching or path copatterns not allowed in systems"

    IllTypedPatternAfterWithAbstraction p -> vcat
      [ "Ill-typed pattern after with abstraction: " <+> prettyA p
      , "(perhaps you can replace it by `_`?)"
      ]

    ComatchingDisabledForRecord recName ->
      "Copattern matching is disabled for record" <+> prettyTCM recName

    IncorrectTypeForRewriteRelation v reason -> case reason of
      ShouldAcceptAtLeastTwoArguments -> sep
        [ prettyTCM v <+> " does not have the right type for a rewriting relation"
        , "because it should accept at least two arguments"
        ]
      FinalTwoArgumentsNotVisible -> sep
        [ prettyTCM v <+> " does not have the right type for a rewriting relation"
        , "because its two final arguments are not both visible."
        ]
      TypeDoesNotEndInSort core tel -> sep
        [ prettyTCM v <+> " does not have the right type for a rewriting relation"
        , "because its type does not end in a sort, but in "
          <+> do inTopContext $ addContext tel $ prettyTCM core
        ]

    UnexpectedParameter par -> do
      text "Unexpected parameter" <+> prettyA par

    NoParameterOfName x -> do
      text ("No parameter of name " ++ x)

    UnexpectedModalityAnnotationInParameter par -> do
      text "Unexpected modality/relevance annotation in" <+> prettyA par

    SortDoesNotAdmitDataDefinitions name s ->fsep
      [ "The universe"
      , prettyTCM s
      , "of"
      , prettyTCM name
      , "does not admit data or record declarations"
      ]

    SortCannotDependOnItsIndex name t -> fsep
      [ "The sort of" <+> prettyTCM name
      , "cannot depend on its indices in the type"
      , prettyTCM t
      ]

    ExpectedBindingForParameter a b -> sep
      [ "Expected binding for parameter"
      , text (absName b) <+> text ":" <+> prettyTCM (unDom a)
      ]

    UnexpectedTypeSignatureForParameter xs -> do
      fsep (pwords "Unexpected type signature for" ++ [ pluralS xs "parameter" ]) <+> sep (fmap prettyA xs)

    UnusableAtModality why mod t -> do
      compatible <- cubicalCompatibleOption
      cubical <- isJust <$> cubicalOption
      let
        context
          | cubical    = "in Cubical Agda,"
          | compatible = "to maintain compatibility with Cubical Agda,"
          | otherwise  = "when --without-K is enabled,"

        explanation what
          | cubical || compatible =
            [ ""
            , fsep ( "Note:":pwords context
                  ++ pwords what ++ pwords "must be usable at the modality"
                  ++ pwords "in which the function was defined, since it will be"
                  ++ pwords "used for computing transports"
                  )
            , ""
            ]
          | otherwise = []
      case why of
        IndexedClause ->
          vcat $
            ( fsep ( pwords "This clause has target type"
                  ++ [prettyTCM t]
                  ++ pwords "which is not usable at the required modality"
                  ++ [pure (attributesForModality mod) <> "."]
                   )
            : explanation "the target type")

        -- Arguments sometimes need to be transported too:
        IndexedClauseArg forced the_arg ->
          vcat $
            ( fsep (pwords "The argument" ++ [prettyTCM the_arg] ++ pwords "has type")
            : nest 2 (prettyTCM t)
            : fsep ( pwords "which is not usable at the required modality"
                  ++ [pure (attributesForModality mod) <> "."] )
            : explanation "this argument's type")

        -- Note: if a generated clause is modality-incorrect, that's a
        -- bug in the LHS modality check
        GeneratedClause ->
          __IMPOSSIBLE_VERBOSE__ . show =<<
                   prettyTCM t
              <+> "is not usable at the required modality"
              <+> pure (attributesForModality mod)
        _ -> prettyTCM t <+> "is not usable at the required modality"
         <+> pure (attributesForModality mod)

    CubicalCompilationNotSupported cubical -> fsep $ concat
      [ pwords $ "Compilation of code that uses"
      , [ text $ cubicalOptionString cubical ]
      , pwords $ "is not supported."
      ]

    OpenEverythingInRecordWhere -> fsep $
      pwords "'open' in 'record where' expressions must provide a 'using' clause"

    QualifiedLocalModule -> fwords "Local modules cannot have qualified names"

    BackendDoesNotSupportOnlyScopeChecking backend -> fsep $ concat
      [ pwords "The backend"
      , [ prettyTCM backend ]
      , pwords "does not support --only-scope-checking."
      ]

    UnknownBackend backend backends -> pure $ P.vcat $ concat
      [ [ P.hcat [ "No backend called '", P.pretty backend, "' " ] ]
      , [ "Installed backend(s):" ]
      , map (("-" P.<+>) . P.pretty) $ Set.toAscList backends
      ]

    CustomBackendError backend err -> (pretty backend <> ":") <?> pure err

    GHCBackendError err -> prettyTCM err

    JSBackendError err -> prettyTCM err

    InteractionError err -> prettyTCM err

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


instance PrettyTCM ExecError where
  prettyTCM = \case

    ExeNotTrusted exe exes -> vcat $
      (fsep $ concat
         [ pwords "Could not find"
         , q exe
         , pwords "in list of trusted executables:"
         ]) :
      [ text $ "  - " ++ Text.unpack exe | exe <- Map.keys exes ]

    ExeNotFound exe fp -> fsep $ concat
      [ pwords "Could not find file"
      , q fp
      , pwords "for trusted executable"
      , q fp
      ]

    ExeNotExecutable exe fp -> fsep $ concat
      [ [ "File" ]
      , q fp
      , pwords "for trusted executable"
      , q exe
      , pwords "does not have permission to execute"
      ]

    where
      q :: (MonadPretty m, P.Pretty a) => a -> [m Doc]
      q = singleton . quotes . pretty



instance PrettyTCM GHCBackendError where
  prettyTCM = \case

    ConstructorCountMismatch d cs hsCons -> fsep $ concat
      [ [ prettyTCM d, "has", text (show n), "constructors,", "but" ]
      , [ "only" | hn > 0, hn < n ]
      , pwords n_forms_are
      , pwords $ "given [" ++ unwords hsCons ++ "]"
      ]
      where
        n  = length cs
        hn = length hsCons
        n_forms_are = case hn of
          1 -> "1 Haskell constructor is"
          _ -> show hn ++ " Haskell constructors are"

    NotAHaskellType top offender -> vcat
      [ fsep $ concat
        [ pwords "The type", [ prettyTCM top ]
        , pwords "cannot be translated to a corresponding Haskell type, because it contains"
        , reason offender
        ]
      , possibleFix offender
      ]
      where
      reason (BadLambda        v) = pwords "the lambda term" ++ [prettyTCM v <> "."]
      reason (BadMeta          v) = pwords "a meta variable" ++ [prettyTCM v <> "."]
      reason (BadDontCare      v) = pwords "an erased term" ++ [prettyTCM v <> "."]
      reason (NotCompiled      x) = pwords "a name that is not compiled"
                                    ++ [parens (prettyTCM x) <> "."]
      reason (NoPragmaFor      x) = prettyTCM x : pwords "which does not have a COMPILE pragma."
      reason (WrongPragmaFor _ x) = prettyTCM x : pwords "which has the wrong kind of COMPILE pragma."

      possibleFix BadLambda{}     = empty
      possibleFix BadMeta{}       = empty
      possibleFix BadDontCare{}   = empty
      possibleFix NotCompiled{}   = empty
      possibleFix (NoPragmaFor d) = suggestPragma d $ "add a pragma"
      possibleFix (WrongPragmaFor r d) = suggestPragma d $
        sep [ "replace the value-level pragma at", nest 2 $ pretty r, "by" ]

      suggestPragma d action = do
        def    <- theDef <$> getConstInfo d
        let dataPragma n = ("data type HsD", "data HsD (" ++ intercalate " | " [ "C" ++ show i | i <- [1..n] ] ++ ")")
            (hsThing, pragma) =
              case def of
                Datatype{ dataCons = cs } -> dataPragma (length cs)
                Record{}                  -> dataPragma 1
                _                         -> ("type HsT", "type HsT")
        vcat [ sep ["Possible fix:", action]
             , nest 2 $ hsep [ "{-# COMPILE GHC", prettyTCM d, "=", text pragma, "#-}" ]
             , text ("for a suitable Haskell " ++ hsThing ++ ".")
             ]

    WrongTypeOfMain io ty -> fsep $ concat
      [ pwords "The type of main should be", [ prettyTCM io ], pwords "A, for some A."
      , pwords "The given type is:", [ prettyTCM ty ]
      ]

instance PrettyTCM JSBackendError where
  prettyTCM = \case
    BadCompilePragma -> sep
      [ "Badly formed COMPILE JS pragma. Expected"
      , "{-# COMPILE JS <name> = <js> #-}"
      ]

instance PrettyTCM InteractionError where
  prettyTCM = \case
    CannotRefine s     -> fsep $ pwords "Cannot refine" ++ pwords s

    CaseSplitError doc -> return doc

    ExpectedIdentifier e -> fsep $ concat
      [ pwords "Expected identifier, but found:"
      , pure $ pretty e
      ]

    ExpectedApplication -> fwords "Expected an argument of the form f e1 e2 .. en"

    NoActionForInteractionPoint ii -> vcat
      [ fwords $ "No type nor action available for hole " ++ prettyShow ii ++ "."
      , fwords $ "Possible cause: the hole has not been reached during type checking (do you see yellow?)"
      ]

    NoSuchInteractionPoint ii ->
      fsep [ "Unknown", "interaction", "point", prettyTCM ii ]

    UnexpectedWhere -> fwords "`where' clauses are not supported in holes"

instance PrettyTCM UnquoteError where
  prettyTCM = \case

    CannotDeclareHiddenFunction f -> fsep $
      pwords "Cannot declare hidden function" ++ [ prettyTCM f ]

    ConInsteadOfDef x def con -> fsep $
      pwords ("Use " ++ con ++ " instead of " ++ def ++ " for constructor") ++
      [prettyTCM x]

    DefInsteadOfCon x def con -> fsep $
      pwords ("Use " ++ def ++ " instead of " ++ con ++ " for non-constructor")
      ++ [prettyTCM x]

    MissingDeclaration x -> fsep $
      pwords "Missing declaration for" ++ [ prettyTCM x ]

    MissingDefinition x -> fsep $
      pwords "Missing definition for" ++ [ prettyTCM x ]

    NakedUnquote -> fwords "`unquote' must be applied to a term"

    NonCanonical kind t ->
      fwords ("Cannot unquote non-canonical " ++ kind)
      $$ nest 2 (prettyTCM t)

    BlockedOnMeta _ m -> fsep $
      pwords $ "Unquote failed because of unsolved meta variables."

    PatLamWithoutClauses _ -> fsep $
      pwords "Cannot unquote pattern lambda without clauses. Use a single `absurd-clause` for absurd lambdas."

    StaleMeta m x ->
      sep
        [ "Cannot unquote stale metavariable"
        , pretty m <> "._" <> pretty (metaId x)
        ]

instance PrettyTCM MissingTypeSignatureInfo where
  prettyTCM = \case
    MissingDataSignature x       -> fsep [ "data"  , "definition", prettyTCM x ]
    MissingRecordSignature x     -> fsep [ "record", "definition", prettyTCM x ]
    MissingFunctionSignature lhs -> fsep [ "left", "hand", "side", prettyTCM lhs ]


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
        (I.Def x _, I.Def y _)
          | isExtendedLambdaName x, isExtendedLambdaName y -> extLamExtLam x y
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

    extLamExtLam :: MonadPretty m => QName -> QName -> m Doc
    extLamExtLam a b = vcat
      [ fwords "Because they are distinct extended lambdas: one is defined at"
      , "  " <+> pretty (nameBindingSite (qnameName a))
      , fwords "and the other at"
      , "  " <+> (pretty (nameBindingSite (qnameName b)) <> ",")
      , fwords "so they have different internal representations."
      ]

class PrettyUnequal a where
  prettyUnequal :: MonadPretty m => a -> m Doc -> a -> m Doc

instance PrettyUnequal Term where
  prettyUnequal t1 ncmp t2 = do
    (d1, d2, d) <- prettyInEqual t1 t2
    fsep $ return d1 : ncmp : return d2 : return d : []

instance PrettyUnequal I.Type where
  prettyUnequal t1 ncmp t2 = prettyUnequal (unEl t1) ncmp (unEl t2)

instance PrettyTCM SplitError where
  prettyTCM :: forall m. MonadPretty m => SplitError -> m Doc
  prettyTCM err = case err of
    NotADatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot split on argument of non-datatype" ++ [prettyTCM t]

    BlockedType b t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot split on argument of unresolved type" ++ [prettyTCM t]

    ErasedDatatype reason t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot branch on erased argument of datatype" ++
      [prettyTCM t] ++
      case reason of
        NoErasedMatches ->
          pwords "because the option --erased-matches is not active"
        NoK ->
          pwords "because the K rule is turned off"
        SeveralConstructors ->
          []

    CoinductiveDatatype t -> enterClosure t $ \ t -> fsep $
      pwords "Cannot pattern match on the coinductive type" ++ [prettyTCM t]

{- UNUSED
    NoRecordConstructor t -> fsep $
      pwords "Cannot pattern match on record" ++ [prettyTCM t] ++
      pwords "because it has no constructor"
 -}

    UnificationStuck b c tel cIxs gIxs errs
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
            (fsep $ [ "Possible", pluralS errs "reason" ] ++ pwords "why unification failed:")
            : map (nest 2 . prettyTCM) errs
        ]
      where
        -- Andreas, 2019-08-08, issue #3943
        -- To not print hidden indices just as {_}, we strip the Arg and print
        -- the hiding information manually.
        prEq :: Arg Term -> Arg Term -> m Doc
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
        displayAbs :: Abs I.Type -> m Doc
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



explainWhyInScope :: forall m. MonadPretty m => WhyInScopeData -> m Doc
explainWhyInScope (WhyInScopeData y _ Nothing [] []) = text (prettyShow  y ++ " is not in scope.")
explainWhyInScope (WhyInScopeData y _ v xs ms) = vcat
  [ text (prettyShow y ++ " is in scope as")
  , nest 2 $ vcat [variable v xs, modules ms]
  ]
  where
    -- variable :: Maybe _ -> [_] -> m Doc
    variable Nothing vs = names vs
    variable (Just x) vs
      | null vs   = asVar
      | otherwise = vcat
         [ sep [ asVar, nest 2 $ shadowing x]
         , nest 2 $ names vs
         ]
      where
        asVar :: m Doc
        asVar = do
          "* a variable bound at" <+> prettyTCM (nameBindingSite $ localVar x)
        shadowing :: LocalVar -> m Doc
        shadowing (LocalVar _ _ [])    = "shadowing"
        shadowing _ = "in conflict with"
    names   = vcat . map pName
    modules = vcat . map pMod

    pKind = \case
      ConName                  -> "constructor"
      CoConName                -> "coinductive constructor"
      FldName                  -> "record field"
      PatternSynName           -> "pattern synonym"
      GeneralizeName           -> "generalizable variable"
      DisallowedGeneralizeName -> "generalizable variable from let open"
      MacroName                -> "macro name"
      QuotableName             -> "quotable name"
      -- previously DefName:
      DataName                 -> "data type"
      RecName                  -> "record type"
      AxiomName                -> "postulate"
      PrimName                 -> "primitive function"
      FunName                  -> "defined name"
      OtherDefName             -> "defined name"

    pName :: AbstractName -> m Doc
    pName a = sep
      [ "* a"
        <+> pKind (anameKind a)
        <+> text (prettyShow $ anameName a)
      , nest 2 $ "brought into scope by"
      ] $$
      nest 2 (pWhy (nameBindingSite $ qnameName $ anameName a) (anameLineage a))
    pMod :: AbstractModule -> m Doc
    pMod  a = sep
      [ "* a module" <+> text (prettyShow $ amodName a)
      , nest 2 $ "brought into scope by"
      ] $$
      nest 2 (pWhy (nameBindingSite $ qnameName $ mnameToQName $ amodName a) (amodLineage a))

    pWhy :: Range -> WhyInScope -> m Doc
    pWhy r Defined = "- its definition at" <+> prettyTCM r
    pWhy r (Opened (C.QName x) w) | isNoName x = pWhy r w
    pWhy r (Opened m w) =
      "- the opening of"
      <+> prettyTCM m
      <+> "at"
      <+> prettyTCM (getRange m)
      $$
      pWhy r w
    pWhy r (Applied m w) =
      "- the application of"
      <+> prettyTCM m
      <+> "at"
      <+> prettyTCM (getRange m)
      $$
      pWhy r w



---------------------------------------------------------------------------
-- * Natural language
---------------------------------------------------------------------------

class Verbalize a where
  verbalize :: a -> String

instance Verbalize Hiding where
  verbalize = hidingToString

instance Verbalize Relevance where
  verbalize r =
    case r of
      Relevant        {} -> "relevant"
      Irrelevant      {} -> "irrelevant"
      ShapeIrrelevant {} -> "shape-irrelevant"

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

instance Verbalize ModalPolarity where
  verbalize r =
    case r of
      UnusedPolarity -> "unused"
      StrictlyPositive -> "strictly positive"
      Positive -> "positive"
      Negative -> "negative"
      MixedPolarity -> "mixed"

instance Verbalize PolarityModality where
  verbalize (PolarityModality p o l) = verbalize p

instance Verbalize Modality where
  verbalize mod | mod == defaultModality = "default"
  verbalize (Modality rel qnt coh pol) = intercalate ", " $
    [ verbalize rel | rel /= defaultRelevance ] ++
    [ verbalize qnt | qnt /= defaultQuantity ] ++
    [ verbalize coh | coh /= defaultCohesion ] ++
    [ verbalize pol | pol /= defaultPolarity ]

-- | Indefinite article.
data Indefinite a = Indefinite a

instance Verbalize a => Verbalize (Indefinite a) where
  verbalize (Indefinite a) =
    case verbalize a of
      "" -> ""
      w@(c:cs) | c `elem` ['a','e','i','o'] -> "an " ++ w
               | otherwise                  -> "a " ++ w
      -- Aarne Ranta would whip me if he saw this.
