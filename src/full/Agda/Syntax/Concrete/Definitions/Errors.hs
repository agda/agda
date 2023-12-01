module Agda.Syntax.Concrete.Definitions.Errors where

import Control.DeepSeq

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Definitions.Types

import Agda.Interaction.Options.Warnings

import Agda.Utils.Null ( empty )
import Agda.Utils.CallStack ( CallStack )
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.List2 (List2, pattern List2)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Singleton

------------------------------------------------------------------------
-- Errors

-- | Exception with internal source code callstack
data DeclarationException = DeclarationException
  { deLocation  :: CallStack
  , deException :: DeclarationException'
  }

-- | The exception type.
data DeclarationException'
  = MultipleEllipses Pattern
  | InvalidName Name
  | DuplicateDefinition Name
  | DuplicateAnonDeclaration Range
  | MissingWithClauses Name LHS
  | WrongDefinition Name DataRecOrFun DataRecOrFun
  | DeclarationPanic String
  | WrongContentBlock KindOfBlock Range
  | AmbiguousFunClauses LHS (List1 Name)
      -- ^ In a mutual block, a clause could belong to any of the ≥2 type signatures ('Name').
  | AmbiguousConstructor Range Name [Name]
      -- ^ In an interleaved mutual block, a constructor could belong to any of the data signatures ('Name')
  | InvalidMeasureMutual Range
      -- ^ In a mutual block, all or none need a MEASURE pragma.
      --   Range is of mutual block.
  | UnquoteDefRequiresSignature (List1 Name)
  | BadMacroDef NiceDeclaration
  | UnfoldingOutsideOpaque Range
    -- ^ An unfolding declaration was not the first declaration
    -- contained in an opaque block.
  | OpaqueInMutual Range
      -- ^ @opaque@ block nested in a @mutual@ block. This can never
      -- happen, even with reordering.
  | DisallowedInterleavedMutual Range String (List1 Name)
      -- ^ A declaration that breaks an implicit mutual block (named by
      -- the String argument) was present while the given lone type
      -- signatures were still without their definitions.
    deriving Show

------------------------------------------------------------------------
-- Warnings

data DeclarationWarning = DeclarationWarning
  { dwLocation :: CallStack
  , dwWarning  :: DeclarationWarning'
  } deriving (Show, Generic)

-- | Non-fatal errors encountered in the Nicifier.
data DeclarationWarning'
  -- Please keep in alphabetical order.
  = EmptyAbstract Range    -- ^ Empty @abstract@  block.
  | EmptyConstructor Range -- ^ Empty @constructor@ block.
  | EmptyField Range       -- ^ Empty @field@     block.
  | EmptyGeneralize Range  -- ^ Empty @variable@  block.
  | EmptyInstance Range    -- ^ Empty @instance@  block
  | EmptyMacro Range       -- ^ Empty @macro@     block.
  | EmptyMutual Range      -- ^ Empty @mutual@    block.
  | EmptyPostulate Range   -- ^ Empty @postulate@ block.
  | EmptyPrivate Range     -- ^ Empty @private@   block.
  | EmptyPrimitive Range   -- ^ Empty @primitive@ block.
  | HiddenGeneralize Range
      -- ^ A 'Hidden' identifier in a @variable@ declaration.
      --   Hiding has no effect there as generalized variables are always hidden
      --   (or instance variables).
  | InvalidCatchallPragma Range
      -- ^ A {-\# CATCHALL \#-} pragma
      --   that does not precede a function clause.
  | InvalidConstructor Range
      -- ^ Invalid definition in a constructor block
  | InvalidConstructorBlock Range
      -- ^ Invalid constructor block (not inside an interleaved mutual block)
  | InvalidCoverageCheckPragma Range
      -- ^ A {-\# NON_COVERING \#-} pragma that does not apply to any function.
  | InvalidNoPositivityCheckPragma Range
      -- ^ A {-\# NO_POSITIVITY_CHECK \#-} pragma
      --   that does not apply to any data or record type.
  | InvalidNoUniverseCheckPragma Range
      -- ^ A {-\# NO_UNIVERSE_CHECK \#-} pragma
      --   that does not apply to a data or record type.
  | InvalidRecordDirective Range
      -- ^ A record directive outside of a record / below existing fields.
  | InvalidTerminationCheckPragma Range
      -- ^ A {-\# TERMINATING \#-} and {-\# NON_TERMINATING \#-} pragma
      --   that does not apply to any function.
  | MissingDeclarations [(Name, Range)]
      -- ^ Definitions (e.g. constructors or functions) without a declaration.
  | MissingDefinitions [(Name, Range)]
      -- ^ Declarations (e.g. type signatures) without a definition.
  | NotAllowedInMutual Range String
  | OpenPublicPrivate Range
      -- ^ @private@ has no effect on @open public@.  (But the user might think so.)
  | OpenPublicAbstract Range
      -- ^ @abstract@ has no effect on @open public@.  (But the user might think so.)
  | PolarityPragmasButNotPostulates [Name]
  | PragmaNoTerminationCheck Range
      -- ^ Pragma @{-\# NO_TERMINATION_CHECK \#-}@ has been replaced
      --   by @{-\# TERMINATING \#-}@ and @{-\# NON_TERMINATING \#-}@.
  | PragmaCompiled Range
      -- ^ @COMPILE@ pragmas are not allowed in safe mode.
  | SafeFlagEta               Range -- ^ @ETA@                 pragma is unsafe.
  | SafeFlagInjective         Range -- ^ @INJECTIVE@           pragma is unsafe.
  | SafeFlagNoCoverageCheck   Range -- ^ @NON_COVERING@        pragma is unsafe.
  | SafeFlagNoPositivityCheck Range -- ^ @NO_POSITIVITY_CHECK@ pragma is unsafe.
  | SafeFlagNoUniverseCheck   Range -- ^ @NO_UNIVERSE_CHECK@   pragma is unsafe.
  | SafeFlagNonTerminating    Range -- ^ @NON_TERMINATING@     pragma is unsafe.
  | SafeFlagPolarity          Range -- ^ @POLARITY@            pragma is unsafe.
  | SafeFlagTerminating       Range -- ^ @TERMINATING@         pragma is unsafe.
  | ShadowingInTelescope (List1 (Name, List2 Range))
  | UnknownFixityInMixfixDecl [Name]
  | UnknownNamesInFixityDecl [Name]
  | UnknownNamesInPolarityPragmas [Name]
  | UselessAbstract Range
      -- ^ @abstract@ block with nothing that can (newly) be made abstract.
  | UselessInstance Range
      -- ^ @instance@ block with nothing that can (newly) become an instance.
  | UselessPrivate Range
      -- ^ @private@ block with nothing that can (newly) be made private.
  deriving (Show, Generic)

declarationWarningName :: DeclarationWarning -> WarningName
declarationWarningName = declarationWarningName' . dwWarning

declarationWarningName' :: DeclarationWarning' -> WarningName
declarationWarningName' = \case
  -- Please keep in alphabetical order.
  EmptyAbstract{}                   -> EmptyAbstract_
  EmptyConstructor{}                -> EmptyConstructor_
  EmptyField{}                      -> EmptyField_
  EmptyGeneralize{}                 -> EmptyGeneralize_
  EmptyInstance{}                   -> EmptyInstance_
  EmptyMacro{}                      -> EmptyMacro_
  EmptyMutual{}                     -> EmptyMutual_
  EmptyPrivate{}                    -> EmptyPrivate_
  EmptyPostulate{}                  -> EmptyPostulate_
  EmptyPrimitive{}                  -> EmptyPrimitive_
  HiddenGeneralize{}                -> HiddenGeneralize_
  InvalidCatchallPragma{}           -> InvalidCatchallPragma_
  InvalidConstructor{}              -> InvalidConstructor_
  InvalidConstructorBlock{}         -> InvalidConstructorBlock_
  InvalidNoPositivityCheckPragma{}  -> InvalidNoPositivityCheckPragma_
  InvalidNoUniverseCheckPragma{}    -> InvalidNoUniverseCheckPragma_
  InvalidRecordDirective{}          -> InvalidRecordDirective_
  InvalidTerminationCheckPragma{}   -> InvalidTerminationCheckPragma_
  InvalidCoverageCheckPragma{}      -> InvalidCoverageCheckPragma_
  MissingDeclarations{}             -> MissingDeclarations_
  MissingDefinitions{}              -> MissingDefinitions_
  NotAllowedInMutual{}              -> NotAllowedInMutual_
  OpenPublicPrivate{}               -> OpenPublicPrivate_
  OpenPublicAbstract{}              -> OpenPublicAbstract_
  PolarityPragmasButNotPostulates{} -> PolarityPragmasButNotPostulates_
  PragmaNoTerminationCheck{}        -> PragmaNoTerminationCheck_
  PragmaCompiled{}                  -> PragmaCompiled_
  SafeFlagEta                    {} -> SafeFlagEta_
  SafeFlagInjective              {} -> SafeFlagInjective_
  SafeFlagNoCoverageCheck        {} -> SafeFlagNoCoverageCheck_
  SafeFlagNoPositivityCheck      {} -> SafeFlagNoPositivityCheck_
  SafeFlagNoUniverseCheck        {} -> SafeFlagNoUniverseCheck_
  SafeFlagNonTerminating         {} -> SafeFlagNonTerminating_
  SafeFlagPolarity               {} -> SafeFlagPolarity_
  SafeFlagTerminating            {} -> SafeFlagTerminating_
  ShadowingInTelescope{}            -> ShadowingInTelescope_
  UnknownFixityInMixfixDecl{}       -> UnknownFixityInMixfixDecl_
  UnknownNamesInFixityDecl{}        -> UnknownNamesInFixityDecl_
  UnknownNamesInPolarityPragmas{}   -> UnknownNamesInPolarityPragmas_
  UselessAbstract{}                 -> UselessAbstract_
  UselessInstance{}                 -> UselessInstance_
  UselessPrivate{}                  -> UselessPrivate_

-- | Nicifier warnings turned into errors in @--safe@ mode.
unsafeDeclarationWarning :: DeclarationWarning -> Bool
unsafeDeclarationWarning = unsafeDeclarationWarning' . dwWarning

unsafeDeclarationWarning' :: DeclarationWarning' -> Bool
unsafeDeclarationWarning' = \case
  -- Please keep in alphabetical order.
  EmptyAbstract{}                   -> False
  EmptyConstructor{}                -> False
  EmptyField{}                      -> False
  EmptyGeneralize{}                 -> False
  EmptyInstance{}                   -> False
  EmptyMacro{}                      -> False
  EmptyMutual{}                     -> False
  EmptyPrivate{}                    -> False
  EmptyPostulate{}                  -> False
  EmptyPrimitive{}                  -> False
  HiddenGeneralize{}                -> False
  InvalidCatchallPragma{}           -> False
  InvalidConstructor{}              -> False
  InvalidConstructorBlock{}         -> False
  InvalidNoPositivityCheckPragma{}  -> False
  InvalidNoUniverseCheckPragma{}    -> False
  InvalidRecordDirective{}          -> False
  InvalidTerminationCheckPragma{}   -> False
  InvalidCoverageCheckPragma{}      -> False
  MissingDeclarations{}             -> True  -- not safe
  MissingDefinitions{}              -> True  -- not safe
  NotAllowedInMutual{}              -> False -- really safe?
  OpenPublicPrivate{}               -> False
  OpenPublicAbstract{}              -> False
  PolarityPragmasButNotPostulates{} -> False
  PragmaNoTerminationCheck{}        -> True  -- not safe
  PragmaCompiled{}                  -> True  -- not safe
  SafeFlagEta                    {} -> True
  SafeFlagInjective              {} -> True
  SafeFlagNoCoverageCheck        {} -> True
  SafeFlagNoPositivityCheck      {} -> True
  SafeFlagNoUniverseCheck        {} -> True
  SafeFlagNonTerminating         {} -> True
  SafeFlagPolarity               {} -> True
  SafeFlagTerminating            {} -> True
  ShadowingInTelescope{}            -> False
  UnknownFixityInMixfixDecl{}       -> False
  UnknownNamesInFixityDecl{}        -> False
  UnknownNamesInPolarityPragmas{}   -> False
  UselessAbstract{}                 -> False
  UselessInstance{}                 -> False
  UselessPrivate{}                  -> False

-- | Pragmas not allowed in @--safe@ mode produce an 'unsafeDeclarationWarning'.
--
unsafePragma :: CMaybe DeclarationWarning' m => Pragma -> m
unsafePragma p =
  case p of
    BuiltinPragma{}            -> empty
    CatchallPragma{}           -> empty
    CompilePragma{}            -> singleton $ PragmaCompiled r
    DisplayPragma{}            -> empty
    EtaPragma{}                -> singleton $ SafeFlagEta r
    ForeignPragma{}            -> empty
    ImpossiblePragma{}         -> empty
    InjectivePragma{}          -> singleton $ SafeFlagInjective r
    InlinePragma{}             -> empty
    NoCoverageCheckPragma{}    -> singleton $ SafeFlagNoCoverageCheck r
    NoPositivityCheckPragma{}  -> singleton $ SafeFlagNoPositivityCheck r
    NoUniverseCheckPragma{}    -> singleton $ SafeFlagNoUniverseCheck r
    NotProjectionLikePragma{}  -> empty
    OptionsPragma{}            -> empty
    PolarityPragma{}           -> singleton $ SafeFlagPolarity r
    RewritePragma{}            -> empty
      -- @RewritePragma@ already requires --rewriting which is incompatible with --safe
    StaticPragma{}             -> empty
    TerminationCheckPragma _ m ->
      case m of
        NonTerminating         -> singleton $ SafeFlagNonTerminating r
        Terminating            -> singleton $ SafeFlagTerminating r
        TerminationCheck       -> empty
        TerminationMeasure{}   -> empty
        -- @NO_TERMINATION_CHECK@ pragma was removed, but still parses. See Issue #1763.
        -- There is the unsafe @'PragmaNoTerminationCheck'@ warning thrown already,
        -- so we need not throw anything here.
        NoTerminationCheck     -> empty
    WarningOnImport{}          -> empty
    WarningOnUsage{}           -> empty
  where
    r = getRange p

------------------------------------------------------------------------
-- Instances

instance HasRange DeclarationException where
  getRange (DeclarationException _ err) = getRange err

instance HasRange DeclarationException' where
  getRange (MultipleEllipses d)                 = getRange d
  getRange (InvalidName x)                      = getRange x
  getRange (DuplicateDefinition x)              = getRange x
  getRange (DuplicateAnonDeclaration r)         = r
  getRange (MissingWithClauses x lhs)           = getRange lhs
  getRange (WrongDefinition x k k')             = getRange x
  getRange (AmbiguousFunClauses lhs xs)         = getRange lhs
  getRange (AmbiguousConstructor r _ _)         = r
  getRange (DeclarationPanic _)                 = noRange
  getRange (WrongContentBlock _ r)              = r
  getRange (InvalidMeasureMutual r)             = r
  getRange (UnquoteDefRequiresSignature x)      = getRange x
  getRange (BadMacroDef d)                      = getRange d
  getRange (UnfoldingOutsideOpaque r)           = r
  getRange (OpaqueInMutual r)                   = r
  getRange (DisallowedInterleavedMutual r _ _)  = r

instance HasRange DeclarationWarning where
  getRange (DeclarationWarning _ w) = getRange w

instance HasRange DeclarationWarning' where
  getRange = \case
    EmptyAbstract r                    -> r
    EmptyConstructor r                 -> r
    EmptyField r                       -> r
    EmptyGeneralize r                  -> r
    EmptyInstance r                    -> r
    EmptyMacro r                       -> r
    EmptyMutual r                      -> r
    EmptyPostulate r                   -> r
    EmptyPrimitive r                   -> r
    EmptyPrivate r                     -> r
    HiddenGeneralize r                 -> r
    InvalidCatchallPragma r            -> r
    InvalidConstructor r               -> r
    InvalidConstructorBlock r          -> r
    InvalidCoverageCheckPragma r       -> r
    InvalidNoPositivityCheckPragma r   -> r
    InvalidNoUniverseCheckPragma r     -> r
    InvalidRecordDirective r           -> r
    InvalidTerminationCheckPragma r    -> r
    MissingDeclarations xs             -> getRange xs
    MissingDefinitions xs              -> getRange xs
    NotAllowedInMutual r x             -> r
    OpenPublicAbstract r               -> r
    OpenPublicPrivate r                -> r
    PolarityPragmasButNotPostulates xs -> getRange xs
    PragmaCompiled r                   -> r
    PragmaNoTerminationCheck r         -> r
    SafeFlagEta r                      -> r
    SafeFlagInjective r                -> r
    SafeFlagNoCoverageCheck r          -> r
    SafeFlagNoPositivityCheck r        -> r
    SafeFlagNoUniverseCheck r          -> r
    SafeFlagNonTerminating r           -> r
    SafeFlagPolarity r                 -> r
    SafeFlagTerminating r              -> r
    ShadowingInTelescope ns            -> getRange ns
    UnknownFixityInMixfixDecl xs       -> getRange xs
    UnknownNamesInFixityDecl xs        -> getRange xs
    UnknownNamesInPolarityPragmas xs   -> getRange xs
    UselessAbstract r                  -> r
    UselessInstance r                  -> r
    UselessPrivate r                   -> r

-- These error messages can (should) be terminated by a dot ".",
-- there is no error context printed after them.
instance Pretty DeclarationException' where
  pretty (MultipleEllipses p) = fsep $
    pwords "Multiple ellipses in left-hand side" ++ [pretty p]
  pretty (InvalidName x) = fsep $
    pwords "Invalid name:" ++ [pretty x]
  pretty (DuplicateDefinition x) = fsep $
    pwords "Duplicate definition of" ++ [pretty x]
  pretty (DuplicateAnonDeclaration _) = fsep $
    pwords "Duplicate declaration of _"
  pretty (MissingWithClauses x lhs) = fsep $
    pwords "Missing with-clauses for function" ++ [pretty x]

  pretty (WrongDefinition x k k') = fsep $ pretty x :
    pwords ("has been declared as a " ++ prettyShow k ++
      ", but is being defined as a " ++ prettyShow k')
  pretty (AmbiguousFunClauses lhs xs) = sep
    [ fsep $
        pwords "More than one matching type signature for left hand side " ++ [pretty lhs] ++
        pwords "it could belong to any of:"
    , vcat $ fmap (pretty . PrintRange) xs
    ]
  pretty (AmbiguousConstructor _ n ns) = sep
    [ fsep (pwords "Could not find a matching data signature for constructor " ++ [pretty n])
    , vcat (case ns of
              [] -> [fsep $ pwords "There was no candidate."]
              _  -> fsep (pwords "It could be any of:") : fmap (pretty . PrintRange) ns
           )
    ]
  pretty (WrongContentBlock b _)      = fsep . pwords $
    case b of
      PostulateBlock -> "A `postulate` block can only contain type signatures, possibly under keywords `instance` and `private`"
      DataBlock -> "A data definition can only contain type signatures, possibly under keyword instance"
      _ -> "Unexpected declaration"
  pretty (InvalidMeasureMutual _) = fsep $
    pwords "In a mutual block, either all functions must have the same (or no) termination checking pragma."
  pretty (UnquoteDefRequiresSignature xs) = fsep $
    pwords "Missing type signatures for unquoteDef" ++ map pretty (List1.toList xs)
  pretty (BadMacroDef nd) = fsep $
    text (declName nd) : pwords "are not allowed in macro blocks"
  pretty (DeclarationPanic s) = text s
  pretty (UnfoldingOutsideOpaque _) = fsep . pwords $
    "Unfolding declarations can only appear as the first declaration immediately contained in an opaque block."
  pretty (OpaqueInMutual _) = fsep $
    pwords "Opaque blocks can not participate in mutual recursion. If the opaque definitions are to be mutually recursive, move the `mutual` block inside the `opaque` block."
  pretty (DisallowedInterleavedMutual _ what xs) = vcat $ List1.concat
    [ singleton $ fsep $ pwords "The following names are declared, but not accompanied by a definition:"
      -- Andreas, 2023-09-07, issue #6823: print also the range.
      -- Print a bullet list; thus, the plural version of this error message is sufficient.
    , fmap (("-" <+>) . pretty . PrintRange) xs
    , singleton $ fwords $ "Since " ++ what ++ " can not participate in mutual recursion, their definition must be given before this point."
    ]

instance Pretty DeclarationWarning where
  pretty (DeclarationWarning _ w) = pretty w

instance Pretty DeclarationWarning' where
  pretty = \case

    UnknownNamesInFixityDecl xs -> fsep $
      pwords "The following names are not declared in the same scope as their syntax or fixity declaration (i.e., either not in scope at all, imported from another module, or declared in a super module):"
      ++ punctuate comma (map pretty xs)

    UnknownFixityInMixfixDecl xs -> fsep $
      pwords "The following mixfix names do not have an associated fixity declaration:"
      ++ punctuate comma (map pretty xs)

    UnknownNamesInPolarityPragmas xs -> fsep $
      pwords "The following names are not declared in the same scope as their polarity pragmas (they could for instance be out of scope, imported from another module, or declared in a super module):"
      ++ punctuate comma  (map pretty xs)

    MissingDeclarations xs -> fsep $
     pwords "The following names are defined but not accompanied by a declaration:"
     ++ punctuate comma (map (pretty . fst) xs)

    MissingDefinitions xs -> fsep $
     pwords "The following names are declared but not accompanied by a definition:"
     ++ punctuate comma (map (pretty . fst) xs)

    NotAllowedInMutual r nd -> fsep $
      text nd : pwords "in mutual blocks are not supported.  Suggestion: get rid of the mutual block by manually ordering declarations"

    PolarityPragmasButNotPostulates xs -> fsep $
      pwords "Polarity pragmas have been given for the following identifiers which are not postulates:"
      ++ punctuate comma (map pretty xs)

    UselessPrivate _ -> fsep $
      pwords "Using private here has no effect. Private applies only to declarations that introduce new identifiers into the module, like type signatures and data, record, and module declarations."

    UselessAbstract _ -> fsep $
      pwords "Using abstract here has no effect. Abstract applies to only definitions like data definitions, record type definitions and function clauses."

    UselessInstance _ -> fsep $
      pwords "Using instance here has no effect. Instance applies only to declarations that introduce new identifiers into the module, like type signatures and axioms."

    EmptyMutual    _ -> fsep $ pwords "Empty mutual block."

    EmptyConstructor{}  -> fsep $ pwords "Empty constructor block."

    EmptyAbstract  _ -> fsep $ pwords "Empty abstract block."

    EmptyPrivate   _ -> fsep $ pwords "Empty private block."

    EmptyInstance  _ -> fsep $ pwords "Empty instance block."

    EmptyMacro     _ -> fsep $ pwords "Empty macro block."

    EmptyPostulate _ -> fsep $ pwords "Empty postulate block."

    EmptyGeneralize _ -> fsep $ pwords "Empty variable block."

    EmptyPrimitive _ -> fsep $ pwords "Empty primitive block."

    EmptyField _ -> fsep $ pwords "Empty field block."

    HiddenGeneralize _ -> fsep $ pwords "Declaring a variable as hidden has no effect in a variable block. Generalization never introduces visible arguments."

    InvalidRecordDirective{} -> fsep $
      pwords "Record directives can only be used inside record definitions and before field declarations."

    InvalidTerminationCheckPragma _ -> fsep $
      pwords "Termination checking pragmas can only precede a function definition or a mutual block (that contains a function definition)."

    InvalidConstructor{} -> fsep $
      pwords "`constructor' blocks may only contain type signatures for constructors."

    InvalidConstructorBlock{} -> fsep $
      pwords "No `constructor' blocks outside of `interleaved mutual' blocks."

    InvalidCoverageCheckPragma _ -> fsep $
      pwords "Coverage checking pragmas can only precede a function definition or a mutual block (that contains a function definition)."

    InvalidNoPositivityCheckPragma _ -> fsep $
      pwords "NO_POSITIVITY_CHECKING pragmas can only precede a data/record definition or a mutual block (that contains a data/record definition)."

    InvalidCatchallPragma _ -> fsep $
      pwords "The CATCHALL pragma can only precede a function clause."

    InvalidNoUniverseCheckPragma _ -> fsep $
      pwords "NO_UNIVERSE_CHECKING pragmas can only precede a data/record definition."

    PragmaNoTerminationCheck _ -> fsep $
      pwords "Pragma {-# NO_TERMINATION_CHECK #-} has been removed.  To skip the termination check, label your definitions either as {-# TERMINATING #-} or {-# NON_TERMINATING #-}."

    PragmaCompiled _ -> fsep $
      pwords "COMPILE pragma not allowed in safe mode."

    OpenPublicAbstract _ -> fsep $
      pwords "public does not have any effect in an abstract block."

    OpenPublicPrivate _ -> fsep $
      pwords "public does not have any effect in a private block."

    ShadowingInTelescope nrs -> fsep $
      pwords "Shadowing in telescope, repeated variable names:"
      ++ punctuate comma (fmap (pretty . fst) nrs)

    SafeFlagEta               _ -> unsafePragma "ETA"
    SafeFlagInjective         _ -> unsafePragma "INJECTIVE"
    SafeFlagNoCoverageCheck   _ -> unsafePragma "NON_COVERING"
    SafeFlagNoPositivityCheck _ -> unsafePragma "NO_POSITIVITY_CHECK"
    SafeFlagNoUniverseCheck   _ -> unsafePragma "NO_UNIVERSE_CHECK"
    SafeFlagNonTerminating    _ -> unsafePragma "NON_TERMINATING"
    SafeFlagPolarity          _ -> unsafePragma "POLARITY"
    SafeFlagTerminating       _ -> unsafePragma "TERMINATING"

    where
      unsafePragma s = fsep $ ["Cannot", "use", s] ++ pwords "pragma with safe flag."

instance NFData DeclarationWarning
instance NFData DeclarationWarning'
