module Agda.Syntax.Concrete.Definitions.Errors where

import Control.DeepSeq

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Definitions.Types

import Agda.Interaction.Options.Warnings

import Agda.Utils.CallStack ( CallStack )
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.List2 (List2, pattern List2)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Pretty

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
  -- ^ @COMPILE@ pragmas are not allowed in safe mode
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
  ShadowingInTelescope{}            -> False
  UnknownFixityInMixfixDecl{}       -> False
  UnknownNamesInFixityDecl{}        -> False
  UnknownNamesInPolarityPragmas{}   -> False
  UselessAbstract{}                 -> False
  UselessInstance{}                 -> False
  UselessPrivate{}                  -> False

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

instance HasRange DeclarationWarning where
  getRange (DeclarationWarning _ w) = getRange w

instance HasRange DeclarationWarning' where
  getRange (UnknownNamesInFixityDecl xs)        = getRange xs
  getRange (UnknownFixityInMixfixDecl xs)       = getRange xs
  getRange (UnknownNamesInPolarityPragmas xs)   = getRange xs
  getRange (PolarityPragmasButNotPostulates xs) = getRange xs
  getRange (MissingDeclarations xs)             = getRange xs
  getRange (MissingDefinitions xs)              = getRange xs
  getRange (UselessPrivate r)                   = r
  getRange (NotAllowedInMutual r x)             = r
  getRange (UselessAbstract r)                  = r
  getRange (UselessInstance r)                  = r
  getRange (EmptyConstructor r)                 = r
  getRange (EmptyMutual r)                      = r
  getRange (EmptyAbstract r)                    = r
  getRange (EmptyPrivate r)                     = r
  getRange (EmptyInstance r)                    = r
  getRange (EmptyMacro r)                       = r
  getRange (EmptyPostulate r)                   = r
  getRange (EmptyGeneralize r)                  = r
  getRange (EmptyPrimitive r)                   = r
  getRange (EmptyField r)                       = r
  getRange (HiddenGeneralize r)                 = r
  getRange (InvalidTerminationCheckPragma r)    = r
  getRange (InvalidCoverageCheckPragma r)       = r
  getRange (InvalidNoPositivityCheckPragma r)   = r
  getRange (InvalidCatchallPragma r)            = r
  getRange (InvalidConstructor r)               = r
  getRange (InvalidConstructorBlock r)          = r
  getRange (InvalidNoUniverseCheckPragma r)     = r
  getRange (InvalidRecordDirective r)           = r
  getRange (PragmaNoTerminationCheck r)         = r
  getRange (PragmaCompiled r)                   = r
  getRange (OpenPublicAbstract r)               = r
  getRange (OpenPublicPrivate r)                = r
  getRange (ShadowingInTelescope ns)            = getRange ns

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
      PostulateBlock -> "A postulate block can only contain type signatures, possibly under keyword instance"
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

instance Pretty DeclarationWarning where
  pretty (DeclarationWarning _ w) = pretty w

instance Pretty DeclarationWarning' where
  pretty (UnknownNamesInFixityDecl xs) = fsep $
    pwords "The following names are not declared in the same scope as their syntax or fixity declaration (i.e., either not in scope at all, imported from another module, or declared in a super module):"
    ++ punctuate comma (map pretty xs)
  pretty (UnknownFixityInMixfixDecl xs) = fsep $
    pwords "The following mixfix names do not have an associated fixity declaration:"
    ++ punctuate comma (map pretty xs)
  pretty (UnknownNamesInPolarityPragmas xs) = fsep $
    pwords "The following names are not declared in the same scope as their polarity pragmas (they could for instance be out of scope, imported from another module, or declared in a super module):"
    ++ punctuate comma  (map pretty xs)
  pretty (MissingDeclarations xs) = fsep $
   pwords "The following names are defined but not accompanied by a declaration:"
   ++ punctuate comma (map (pretty . fst) xs)
  pretty (MissingDefinitions xs) = fsep $
   pwords "The following names are declared but not accompanied by a definition:"
   ++ punctuate comma (map (pretty . fst) xs)
  pretty (NotAllowedInMutual r nd) = fsep $
    text nd : pwords "in mutual blocks are not supported.  Suggestion: get rid of the mutual block by manually ordering declarations"
  pretty (PolarityPragmasButNotPostulates xs) = fsep $
    pwords "Polarity pragmas have been given for the following identifiers which are not postulates:"
    ++ punctuate comma (map pretty xs)
  pretty (UselessPrivate _)      = fsep $
    pwords "Using private here has no effect. Private applies only to declarations that introduce new identifiers into the module, like type signatures and data, record, and module declarations."
  pretty (UselessAbstract _)      = fsep $
    pwords "Using abstract here has no effect. Abstract applies to only definitions like data definitions, record type definitions and function clauses."
  pretty (UselessInstance _)      = fsep $
    pwords "Using instance here has no effect. Instance applies only to declarations that introduce new identifiers into the module, like type signatures and axioms."
  pretty (EmptyMutual    _)  = fsep $ pwords "Empty mutual block."
  pretty EmptyConstructor{}  = fsep $ pwords "Empty constructor block."
  pretty (EmptyAbstract  _)  = fsep $ pwords "Empty abstract block."
  pretty (EmptyPrivate   _)  = fsep $ pwords "Empty private block."
  pretty (EmptyInstance  _)  = fsep $ pwords "Empty instance block."
  pretty (EmptyMacro     _)  = fsep $ pwords "Empty macro block."
  pretty (EmptyPostulate _)  = fsep $ pwords "Empty postulate block."
  pretty (EmptyGeneralize _) = fsep $ pwords "Empty variable block."
  pretty (EmptyPrimitive _)  = fsep $ pwords "Empty primitive block."
  pretty (EmptyField _)      = fsep $ pwords "Empty field block."
  pretty (HiddenGeneralize _) = fsep $ pwords "Declaring a variable as hidden has no effect in a variable block. Generalization never introduces visible arguments."
  pretty InvalidRecordDirective{} = fsep $
    pwords "Record directives can only be used inside record definitions and before field declarations."
  pretty (InvalidTerminationCheckPragma _) = fsep $
    pwords "Termination checking pragmas can only precede a function definition or a mutual block (that contains a function definition)."
  pretty InvalidConstructor{} = fsep $
    pwords "`constructor' blocks may only contain type signatures for constructors."
  pretty InvalidConstructorBlock{} = fsep $
    pwords "No `constructor' blocks outside of `interleaved mutual' blocks."
  pretty (InvalidCoverageCheckPragma _)    = fsep $
    pwords "Coverage checking pragmas can only precede a function definition or a mutual block (that contains a function definition)."
  pretty (InvalidNoPositivityCheckPragma _) = fsep $
    pwords "NO_POSITIVITY_CHECKING pragmas can only precede a data/record definition or a mutual block (that contains a data/record definition)."
  pretty (InvalidCatchallPragma _) = fsep $
    pwords "The CATCHALL pragma can only precede a function clause."
  pretty (InvalidNoUniverseCheckPragma _) = fsep $
    pwords "NO_UNIVERSE_CHECKING pragmas can only precede a data/record definition."
  pretty (PragmaNoTerminationCheck _) = fsep $
    pwords "Pragma {-# NO_TERMINATION_CHECK #-} has been removed.  To skip the termination check, label your definitions either as {-# TERMINATING #-} or {-# NON_TERMINATING #-}."
  pretty (PragmaCompiled _) = fsep $
    pwords "COMPILE pragma not allowed in safe mode."
  pretty (OpenPublicAbstract _) = fsep $
    pwords "public does not have any effect in an abstract block."
  pretty (OpenPublicPrivate _) = fsep $
    pwords "public does not have any effect in a private block."
  pretty (ShadowingInTelescope nrs) = fsep $
    pwords "Shadowing in telescope, repeated variable names:"
    ++ punctuate comma (fmap (pretty . fst) nrs)

instance NFData DeclarationWarning
instance NFData DeclarationWarning'
