{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
    , Nice, runNice
    , niceDeclarations
    , notSoNiceDeclarations
    , niceHasAbstract
    , Measure
    , declarationWarningName
    ) where

import Prelude hiding (null)

import Control.Monad.Except
import Control.Monad.State

import Data.Bifunctor
import Data.Data (Data)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
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

import Agda.Interaction.Options.Warnings

import Agda.Utils.AffineHole
import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List (isSublistOf)
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Three
import Agda.Utils.Tuple
import Agda.Utils.Update

import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

{-| The nice declarations. No fixity declarations and function definitions are
    contained in a single constructor instead of spread out between type
    signatures and clauses. The @private@, @postulate@, @abstract@ and @instance@
    modifiers have been distributed to the individual declarations.

    Observe the order of components:

      Range
      Fixity'
      Access
      IsAbstract
      IsInstance
      TerminationCheck
      PositivityCheck

      further attributes

      (Q)Name

      content (Expr, Declaration ...)
-}
data NiceDeclaration
  = Axiom Range Access IsAbstract IsInstance ArgInfo Name Expr
      -- ^ 'IsAbstract' argument: We record whether a declaration was made in an @abstract@ block.
      --
      --   'ArgInfo' argument: Axioms and functions can be declared irrelevant.
      --   ('Hiding' should be 'NotHidden'.)
  | NiceField Range Access IsAbstract IsInstance TacticAttribute Name (Arg Expr)
  | PrimitiveFunction Range Access IsAbstract Name (Arg Expr)
  | NiceMutual Range TerminationCheck CoverageCheck PositivityCheck [NiceDeclaration]
  | NiceModule Range Access IsAbstract QName Telescope [Declaration]
  | NiceModuleMacro Range Access Name ModuleApplication OpenShortHand ImportDirective
  | NiceOpen Range QName ImportDirective
  | NiceImport Range QName (Maybe AsName) OpenShortHand ImportDirective
  | NicePragma Range Pragma
  | NiceRecSig Range Access IsAbstract PositivityCheck UniverseCheck Name [LamBinding] Expr
  | NiceDataSig Range Access IsAbstract PositivityCheck UniverseCheck Name [LamBinding] Expr
  | NiceFunClause Range Access IsAbstract TerminationCheck CoverageCheck Catchall Declaration
    -- ^ An uncategorized function clause, could be a function clause
    --   without type signature or a pattern lhs (e.g. for irrefutable let).
    --   The 'Declaration' is the actual 'FunClause'.
  | FunSig Range Access IsAbstract IsInstance IsMacro ArgInfo TerminationCheck CoverageCheck Name Expr
  | FunDef Range [Declaration] IsAbstract IsInstance TerminationCheck CoverageCheck Name [Clause]
      -- ^ Block of function clauses (we have seen the type signature before).
      --   The 'Declaration's are the original declarations that were processed
      --   into this 'FunDef' and are only used in 'notSoNiceDeclaration'.
      --   Andreas, 2017-01-01: Because of issue #2372, we add 'IsInstance' here.
      --   An alias should know that it is an instance.
  | NiceDataDef Range Origin IsAbstract PositivityCheck UniverseCheck Name [LamBinding] [NiceConstructor]
  | NiceRecDef Range Origin IsAbstract PositivityCheck UniverseCheck Name (Maybe (Ranged Induction)) (Maybe HasEta0)
      (Maybe Range) (Maybe (Name, IsInstance)) [LamBinding] [Declaration]
      -- ^ @(Maybe Range)@ gives range of the 'pattern' declaration.
  | NicePatternSyn Range Access Name [Arg Name] Pattern
  | NiceGeneralize Range Access ArgInfo TacticAttribute Name Expr
  | NiceUnquoteDecl Range Access IsAbstract IsInstance TerminationCheck CoverageCheck [Name] Expr
  | NiceUnquoteDef Range Access IsAbstract TerminationCheck CoverageCheck [Name] Expr
  deriving (Data, Show)

type TerminationCheck = Common.TerminationCheck Measure

-- | Termination measure is, for now, a variable name.
type Measure = Name

type Catchall = Bool

-- | Only 'Axiom's.
type NiceConstructor = NiceTypeSignature

-- | Only 'Axiom's.
type NiceTypeSignature  = NiceDeclaration

-- | One clause in a function definition. There is no guarantee that the 'LHS'
--   actually declares the 'Name'. We will have to check that later.
data Clause = Clause Name Catchall LHS RHS WhereClause [Clause]
    deriving (Data, Show)

-- | Exception with internal source code callstack
data DeclarationException = DeclarationException
  { deLocation  :: CallStack
  , deException :: DeclarationException'
  }

declarationException :: HasCallStack => DeclarationException' -> Nice a
declarationException e = withCallerCallStack $ throwError . flip DeclarationException e

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
  | InvalidMeasureMutual Range
      -- ^ In a mutual block, all or none need a MEASURE pragma.
      --   Range is of mutual block.
  | UnquoteDefRequiresSignature (List1 Name)
  | BadMacroDef NiceDeclaration
    deriving (Data, Show)


data DeclarationWarning = DeclarationWarning
  { dwLocation :: CallStack
  , dwWarning  :: DeclarationWarning'
  } deriving (Show)

declarationWarning' :: DeclarationWarning' -> CallStack -> Nice ()
declarationWarning' w loc = niceWarning $ DeclarationWarning loc w

declarationWarning :: HasCallStack => DeclarationWarning' -> Nice ()
declarationWarning = withCallerCallStack . declarationWarning'

-- | Non-fatal errors encountered in the Nicifier.
data DeclarationWarning'
  -- Please keep in alphabetical order.
  = EmptyAbstract Range   -- ^ Empty @abstract@  block.
  | EmptyField Range      -- ^ Empty @field@     block.
  | EmptyGeneralize Range -- ^ Empty @variable@  block.
  | EmptyInstance Range   -- ^ Empty @instance@  block
  | EmptyMacro Range      -- ^ Empty @macro@     block.
  | EmptyMutual Range     -- ^ Empty @mutual@    block.
  | EmptyPostulate Range  -- ^ Empty @postulate@ block.
  | EmptyPrivate Range    -- ^ Empty @private@   block.
  | EmptyPrimitive Range  -- ^ Empty @primitive@ block.
  | InvalidCatchallPragma Range
      -- ^ A {-\# CATCHALL \#-} pragma
      --   that does not precede a function clause.
  | InvalidCoverageCheckPragma Range
      -- ^ A {-\# NON_COVERING \#-} pragma that does not apply to any function.
  | InvalidNoPositivityCheckPragma Range
      -- ^ A {-\# NO_POSITIVITY_CHECK \#-} pragma
      --   that does not apply to any data or record type.
  | InvalidNoUniverseCheckPragma Range
      -- ^ A {-\# NO_UNIVERSE_CHECK \#-} pragma
      --   that does not apply to a data or record type.
  | InvalidTerminationCheckPragma Range
      -- ^ A {-\# TERMINATING \#-} and {-\# NON_TERMINATING \#-} pragma
      --   that does not apply to any function.
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
  | ShadowingInTelescope [(Name, [Range])]
  | UnknownFixityInMixfixDecl [Name]
  | UnknownNamesInFixityDecl [Name]
  | UnknownNamesInPolarityPragmas [Name]
  | UselessAbstract Range
      -- ^ @abstract@ block with nothing that can (newly) be made abstract.
  | UselessInstance Range
      -- ^ @instance@ block with nothing that can (newly) become an instance.
  | UselessPrivate Range
      -- ^ @private@ block with nothing that can (newly) be made private.
  deriving (Data, Show)

declarationWarningName :: DeclarationWarning -> WarningName
declarationWarningName = declarationWarningName' . dwWarning

declarationWarningName' :: DeclarationWarning' -> WarningName
declarationWarningName' = \case
  -- Please keep in alphabetical order.
  EmptyAbstract{}                   -> EmptyAbstract_
  EmptyField{}                      -> EmptyField_
  EmptyGeneralize{}                 -> EmptyGeneralize_
  EmptyInstance{}                   -> EmptyInstance_
  EmptyMacro{}                      -> EmptyMacro_
  EmptyMutual{}                     -> EmptyMutual_
  EmptyPrivate{}                    -> EmptyPrivate_
  EmptyPostulate{}                  -> EmptyPostulate_
  EmptyPrimitive{}                  -> EmptyPrimitive_
  InvalidCatchallPragma{}           -> InvalidCatchallPragma_
  InvalidNoPositivityCheckPragma{}  -> InvalidNoPositivityCheckPragma_
  InvalidNoUniverseCheckPragma{}    -> InvalidNoUniverseCheckPragma_
  InvalidTerminationCheckPragma{}   -> InvalidTerminationCheckPragma_
  InvalidCoverageCheckPragma{}      -> InvalidCoverageCheckPragma_
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
  EmptyField{}                      -> False
  EmptyGeneralize{}                 -> False
  EmptyInstance{}                   -> False
  EmptyMacro{}                      -> False
  EmptyMutual{}                     -> False
  EmptyPrivate{}                    -> False
  EmptyPostulate{}                  -> False
  EmptyPrimitive{}                  -> False
  InvalidCatchallPragma{}           -> False
  InvalidNoPositivityCheckPragma{}  -> False
  InvalidNoUniverseCheckPragma{}    -> False
  InvalidTerminationCheckPragma{}   -> False
  InvalidCoverageCheckPragma{}      -> False
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

-- | Several declarations expect only type signatures as sub-declarations.  These are:
data KindOfBlock
  = PostulateBlock  -- ^ @postulate@
  | PrimitiveBlock  -- ^ @primitive@.  Ensured by parser.
  | InstanceBlock   -- ^ @instance@.  Actually, here all kinds of sub-declarations are allowed a priori.
  | FieldBlock      -- ^ @field@.  Ensured by parser.
  | DataBlock       -- ^ @data ... where@.  Here we got a bad error message for Agda-2.5 (Issue 1698).
  deriving (Data, Eq, Ord, Show)


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
  getRange (DeclarationPanic _)                 = noRange
  getRange (WrongContentBlock _ r)              = r
  getRange (InvalidMeasureMutual r)             = r
  getRange (UnquoteDefRequiresSignature x)      = getRange x
  getRange (BadMacroDef d)                      = getRange d

instance HasRange DeclarationWarning where
  getRange (DeclarationWarning _ w) = getRange w

instance HasRange DeclarationWarning' where
  getRange (UnknownNamesInFixityDecl xs)        = getRange xs
  getRange (UnknownFixityInMixfixDecl xs)       = getRange xs
  getRange (UnknownNamesInPolarityPragmas xs)   = getRange xs
  getRange (PolarityPragmasButNotPostulates xs) = getRange xs
  getRange (MissingDefinitions xs)              = getRange xs
  getRange (UselessPrivate r)                   = r
  getRange (NotAllowedInMutual r x)             = r
  getRange (UselessAbstract r)                  = r
  getRange (UselessInstance r)                  = r
  getRange (EmptyMutual r)                      = r
  getRange (EmptyAbstract r)                    = r
  getRange (EmptyPrivate r)                     = r
  getRange (EmptyInstance r)                    = r
  getRange (EmptyMacro r)                       = r
  getRange (EmptyPostulate r)                   = r
  getRange (EmptyGeneralize r)                  = r
  getRange (EmptyPrimitive r)                   = r
  getRange (EmptyField r)                       = r
  getRange (InvalidTerminationCheckPragma r)    = r
  getRange (InvalidCoverageCheckPragma r)       = r
  getRange (InvalidNoPositivityCheckPragma r)   = r
  getRange (InvalidCatchallPragma r)            = r
  getRange (InvalidNoUniverseCheckPragma r)     = r
  getRange (PragmaNoTerminationCheck r)         = r
  getRange (PragmaCompiled r)                   = r
  getRange (OpenPublicAbstract r)               = r
  getRange (OpenPublicPrivate r)                = r
  getRange (ShadowingInTelescope ns)            = getRange ns

instance HasRange NiceDeclaration where
  getRange (Axiom r _ _ _ _ _ _)           = r
  getRange (NiceField r _ _ _ _ _ _)       = r
  getRange (NiceMutual r _ _ _ _)          = r
  getRange (NiceModule r _ _ _ _ _ )       = r
  getRange (NiceModuleMacro r _ _ _ _ _)   = r
  getRange (NiceOpen r _ _)                = r
  getRange (NiceImport r _ _ _ _)          = r
  getRange (NicePragma r _)                = r
  getRange (PrimitiveFunction r _ _ _ _)   = r
  getRange (FunSig r _ _ _ _ _ _ _ _ _)    = r
  getRange (FunDef r _ _ _ _ _ _ _)        = r
  getRange (NiceDataDef r _ _ _ _ _ _ _)   = r
  getRange (NiceRecDef r _ _ _ _ _ _ _ _ _ _ _)  = r
  getRange (NiceRecSig r _ _ _ _ _ _ _)    = r
  getRange (NiceDataSig r _ _ _ _ _ _ _)   = r
  getRange (NicePatternSyn r _ _ _ _)      = r
  getRange (NiceGeneralize r _ _ _ _ _)    = r
  getRange (NiceFunClause r _ _ _ _ _ _)   = r
  getRange (NiceUnquoteDecl r _ _ _ _ _ _ _) = r
  getRange (NiceUnquoteDef r _ _ _ _ _ _)    = r

instance Pretty NiceDeclaration where
  pretty = \case
    Axiom _ _ _ _ _ x _            -> text "postulate" <+> pretty x <+> colon <+> text "_"
    NiceField _ _ _ _ _ x _        -> text "field" <+> pretty x
    PrimitiveFunction _ _ _ x _    -> text "primitive" <+> pretty x
    NiceMutual{}                   -> text "mutual"
    NiceModule _ _ _ x _ _         -> text "module" <+> pretty x <+> text "where"
    NiceModuleMacro _ _ x _ _ _    -> text "module" <+> pretty x <+> text "= ..."
    NiceOpen _ x _                 -> text "open" <+> pretty x
    NiceImport _ x _ _ _           -> text "import" <+> pretty x
    NicePragma{}                   -> text "{-# ... #-}"
    NiceRecSig _ _ _ _ _ x _ _     -> text "record" <+> pretty x
    NiceDataSig _ _ _ _ _ x _ _    -> text "data" <+> pretty x
    NiceFunClause{}                -> text "<function clause>"
    FunSig _ _ _ _ _ _ _ _ x _     -> pretty x <+> colon <+> text "_"
    FunDef _ _ _ _ _ _ x _         -> pretty x <+> text "= _"
    NiceDataDef _ _ _ _ _ x _ _    -> text "data" <+> pretty x <+> text "where"
    NiceRecDef _ _ _ _ _ x _ _ _ _ _ _ -> text "record" <+> pretty x <+> text "where"
    NicePatternSyn _ _ x _ _       -> text "pattern" <+> pretty x
    NiceGeneralize _ _ _ _ x _     -> text "variable" <+> pretty x
    NiceUnquoteDecl _ _ _ _ _ _ xs _ -> text "<unquote declarations>"
    NiceUnquoteDef _ _ _ _ _ xs _    -> text "<unquote definitions>"

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
  pretty (EmptyAbstract  _)  = fsep $ pwords "Empty abstract block."
  pretty (EmptyPrivate   _)  = fsep $ pwords "Empty private block."
  pretty (EmptyInstance  _)  = fsep $ pwords "Empty instance block."
  pretty (EmptyMacro     _)  = fsep $ pwords "Empty macro block."
  pretty (EmptyPostulate _)  = fsep $ pwords "Empty postulate block."
  pretty (EmptyGeneralize _) = fsep $ pwords "Empty variable block."
  pretty (EmptyPrimitive _)  = fsep $ pwords "Empty primitive block."
  pretty (EmptyField _)      = fsep $ pwords "Empty field block."
  pretty (InvalidTerminationCheckPragma _) = fsep $
    pwords "Termination checking pragmas can only precede a function definition or a mutual block (that contains a function definition)."
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
    ++ punctuate comma (map (pretty . fst) nrs)

declName :: NiceDeclaration -> String
declName Axiom{}             = "Postulates"
declName NiceField{}         = "Fields"
declName NiceMutual{}        = "Mutual blocks"
declName NiceModule{}        = "Modules"
declName NiceModuleMacro{}   = "Modules"
declName NiceOpen{}          = "Open declarations"
declName NiceImport{}        = "Import statements"
declName NicePragma{}        = "Pragmas"
declName PrimitiveFunction{} = "Primitive declarations"
declName NicePatternSyn{}    = "Pattern synonyms"
declName NiceGeneralize{}    = "Generalized variables"
declName NiceUnquoteDecl{}   = "Unquoted declarations"
declName NiceUnquoteDef{}    = "Unquoted definitions"
declName NiceRecSig{}        = "Records"
declName NiceDataSig{}       = "Data types"
declName NiceFunClause{}     = "Functions without a type signature"
declName FunSig{}            = "Type signatures"
declName FunDef{}            = "Function definitions"
declName NiceRecDef{}        = "Records"
declName NiceDataDef{}       = "Data types"

{--------------------------------------------------------------------------
    The niceifier
 --------------------------------------------------------------------------}

data InMutual
  = InMutual    -- ^ we are nicifying a mutual block
  | NotInMutual -- ^ we are nicifying decls not in a mutual block
    deriving (Eq, Show)

-- | The kind of the forward declaration.

data DataRecOrFun
  = DataName
    { _kindPosCheck :: PositivityCheck
    , _kindUniCheck :: UniverseCheck
    }
    -- ^ Name of a data type
  | RecName
    { _kindPosCheck :: PositivityCheck
    , _kindUniCheck :: UniverseCheck
    }
    -- ^ Name of a record type
  | FunName TerminationCheck CoverageCheck
    -- ^ Name of a function.
  deriving (Data, Show)

-- Ignore pragmas when checking equality
instance Eq DataRecOrFun where
  DataName{} == DataName{} = True
  RecName{}  == RecName{}  = True
  FunName{}  == FunName{}  = True
  _          == _          = False

instance Pretty DataRecOrFun where
  pretty DataName{} = "data type"
  pretty RecName{}  = "record type"
  pretty FunName{}  = "function"

isFunName :: DataRecOrFun -> Bool
isFunName (FunName{}) = True
isFunName _           = False

sameKind :: DataRecOrFun -> DataRecOrFun -> Bool
sameKind = (==)

terminationCheck :: DataRecOrFun -> TerminationCheck
terminationCheck (FunName tc _) = tc
terminationCheck _ = TerminationCheck

coverageCheck :: DataRecOrFun -> CoverageCheck
coverageCheck (FunName _ cc) = cc
coverageCheck _ = YesCoverageCheck

positivityCheck :: DataRecOrFun -> PositivityCheck
positivityCheck (DataName pc _) = pc
positivityCheck (RecName pc _)  = pc
positivityCheck (FunName _ _)   = YesPositivityCheck

universeCheck :: DataRecOrFun -> UniverseCheck
universeCheck (DataName _ uc) = uc
universeCheck (RecName _ uc)  = uc
universeCheck (FunName _ _)   = YesUniverseCheck

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

-- | Nicifier monad.
--   Preserve the state when throwing an exception.

newtype Nice a = Nice { unNice :: ExceptT DeclarationException (State NiceEnv) a }
  deriving ( Functor, Applicative, Monad
           , MonadState NiceEnv, MonadError DeclarationException
           )

-- | Run a Nicifier computation, return result and warnings
--   (in chronological order).
runNice :: Nice a -> (Either DeclarationException a, NiceWarnings)
runNice m = second (reverse . niceWarn) $
  runExceptT (unNice m) `runState` initNiceEnv

-- | Nicifier state.

data NiceEnv = NiceEnv
  { _loneSigs :: LoneSigs
    -- ^ Lone type signatures that wait for their definition.
  , _termChk  :: TerminationCheck
    -- ^ Termination checking pragma waiting for a definition.
  , _posChk   :: PositivityCheck
    -- ^ Positivity checking pragma waiting for a definition.
  , _uniChk   :: UniverseCheck
    -- ^ Universe checking pragma waiting for a data/rec signature or definition.
  , _catchall :: Catchall
    -- ^ Catchall pragma waiting for a function clause.
  , _covChk  :: CoverageCheck
    -- ^ Coverage pragma waiting for a definition.
  , niceWarn :: NiceWarnings
    -- ^ Stack of warnings. Head is last warning.
  , _nameId  :: NameId
    -- ^ We distinguish different 'NoName's (anonymous definitions) by a unique 'NameId'.
  }

data LoneSig = LoneSig
  { loneSigRange :: Range
  , loneSigName  :: Name
      -- ^ If 'isNoName', this name can have a different 'NameId'
      --   than the key of 'LoneSigs' pointing to it.
  , loneSigKind  :: DataRecOrFun
  }

type LoneSigs     = Map Name LoneSig
     -- ^ We retain the 'Name' also in the codomain since
     --   'Name' as a key is up to @Eq Name@ which ignores the range.
     --   However, without range names are not unique in case the
     --   user gives a second definition of the same name.
     --   This causes then problems in 'replaceSigs' which might
     --   replace the wrong signature.
     --
     --   Another reason is that we want to distinguish different
     --   occurrences of 'NoName' in a mutual block (issue #4157).
     --   The 'NoName' in the codomain will have a unique 'NameId'.

type NiceWarnings = [DeclarationWarning]
     -- ^ Stack of warnings. Head is last warning.

-- | Initial nicifier state.

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { _loneSigs = empty
  , _termChk  = TerminationCheck
  , _posChk   = YesPositivityCheck
  , _uniChk   = YesUniverseCheck
  , _catchall = False
  , _covChk   = YesCoverageCheck
  , niceWarn  = []
  , _nameId   = NameId 1 1   -- The module id is bogus.
  }

lensNameId :: Lens' NameId NiceEnv
lensNameId f e = f (_nameId e) <&> \ i -> e { _nameId = i }

nextNameId :: Nice NameId
nextNameId = do
  i <- use lensNameId
  lensNameId %= succ
  return i

-- * Handling the lone signatures, stored to infer mutual blocks.

-- | Lens for field '_loneSigs'.

loneSigs :: Lens' LoneSigs NiceEnv
loneSigs f e = f (_loneSigs e) <&> \ s -> e { _loneSigs = s }

-- | Adding a lone signature to the state.
--   Return the name (which is made unique if 'isNoName').

addLoneSig :: Range -> Name -> DataRecOrFun -> Nice Name
addLoneSig r x k = do
  -- Andreas, 2020-05-19, issue #4157, make '_' unique.
  x' <- if not $ isNoName x then return x else do
    i <- nextNameId
    return x{ nameId = i }
  loneSigs %== \ s -> do
    let (mr, s') = Map.insertLookupWithKey (\ _k new _old -> new) x (LoneSig r x' k) s
    case mr of
      Nothing -> return s'
      Just{}  -> declarationException $
        if not $ isNoName x then DuplicateDefinition x else DuplicateAnonDeclaration r
  return x'

-- | Remove a lone signature from the state.

removeLoneSig :: Name -> Nice ()
removeLoneSig x = loneSigs %= Map.delete x

-- | Search for forward type signature.

getSig :: Name -> Nice (Maybe DataRecOrFun)
getSig x = fmap loneSigKind . Map.lookup x <$> use loneSigs

-- | Check that no lone signatures are left in the state.

noLoneSigs :: Nice Bool
noLoneSigs = null <$> use loneSigs

-- | Ensure that all forward declarations have been given a definition.

forgetLoneSigs :: Nice ()
forgetLoneSigs = loneSigs .= Map.empty

checkLoneSigs :: LoneSigs -> Nice ()
checkLoneSigs xs = do
  forgetLoneSigs
  unless (Map.null xs) $ declarationWarning $ MissingDefinitions $
    map (\s -> (loneSigName s , loneSigRange s)) $ Map.elems xs

-- | Get names of lone function signatures, plus their unique names.

loneFuns :: LoneSigs -> [(Name,Name)]
loneFuns = map (second loneSigName) . filter (isFunName . loneSigKind . snd) . Map.toList

-- | Create a 'LoneSigs' map from an association list.

loneSigsFromLoneNames :: [(Range, Name, DataRecOrFun)] -> LoneSigs
loneSigsFromLoneNames = Map.fromList . map (\(r,x,k) -> (x, LoneSig r x k))

-- | Lens for field '_termChk'.

terminationCheckPragma :: Lens' TerminationCheck NiceEnv
terminationCheckPragma f e = f (_termChk e) <&> \ s -> e { _termChk = s }

withTerminationCheckPragma :: TerminationCheck -> Nice a -> Nice a
withTerminationCheckPragma tc f = do
  tc_old <- use terminationCheckPragma
  terminationCheckPragma .= tc
  result <- f
  terminationCheckPragma .= tc_old
  return result

coverageCheckPragma :: Lens' CoverageCheck NiceEnv
coverageCheckPragma f e = f (_covChk e) <&> \ s -> e { _covChk = s }

withCoverageCheckPragma :: CoverageCheck -> Nice a -> Nice a
withCoverageCheckPragma tc f = do
  tc_old <- use coverageCheckPragma
  coverageCheckPragma .= tc
  result <- f
  coverageCheckPragma .= tc_old
  return result

-- | Lens for field '_posChk'.

positivityCheckPragma :: Lens' PositivityCheck NiceEnv
positivityCheckPragma f e = f (_posChk e) <&> \ s -> e { _posChk = s }

withPositivityCheckPragma :: PositivityCheck -> Nice a -> Nice a
withPositivityCheckPragma pc f = do
  pc_old <- use positivityCheckPragma
  positivityCheckPragma .= pc
  result <- f
  positivityCheckPragma .= pc_old
  return result

-- | Lens for field '_uniChk'.

universeCheckPragma :: Lens' UniverseCheck NiceEnv
universeCheckPragma f e = f (_uniChk e) <&> \ s -> e { _uniChk = s }

withUniverseCheckPragma :: UniverseCheck -> Nice a -> Nice a
withUniverseCheckPragma uc f = do
  uc_old <- use universeCheckPragma
  universeCheckPragma .= uc
  result <- f
  universeCheckPragma .= uc_old
  return result

-- | Get universe check pragma from a data/rec signature.
--   Defaults to 'YesUniverseCheck'.

getUniverseCheckFromSig :: Name -> Nice UniverseCheck
getUniverseCheckFromSig x = maybe YesUniverseCheck universeCheck <$> getSig x

-- | Lens for field '_catchall'.

catchallPragma :: Lens' Catchall NiceEnv
catchallPragma f e = f (_catchall e) <&> \ s -> e { _catchall = s }

-- | Get current catchall pragma, and reset it for the next clause.

popCatchallPragma :: Nice Catchall
popCatchallPragma = do
  ca <- use catchallPragma
  catchallPragma .= False
  return ca

withCatchallPragma :: Catchall -> Nice a -> Nice a
withCatchallPragma ca f = do
  ca_old <- use catchallPragma
  catchallPragma .= ca
  result <- f
  catchallPragma .= ca_old
  return result

-- | Add a new warning.
niceWarning :: DeclarationWarning -> Nice ()
niceWarning w = modify $ \ st -> st { niceWarn = w : niceWarn st }

data DeclKind
    = LoneSigDecl Range DataRecOrFun Name
    | LoneDefs DataRecOrFun [Name]
    | OtherDecl
  deriving (Eq, Show)

declKind :: NiceDeclaration -> DeclKind
declKind (FunSig r _ _ _ _ _ tc cc x _)     = LoneSigDecl r (FunName tc cc) x
declKind (NiceRecSig r _ _ pc uc x pars _)  = LoneSigDecl r (RecName pc uc) x
declKind (NiceDataSig r _ _ pc uc x pars _) = LoneSigDecl r (DataName pc uc) x
declKind (FunDef r _ abs ins tc cc x _)     = LoneDefs (FunName tc cc) [x]
declKind (NiceDataDef _ _ _ pc uc x pars _) = LoneDefs (DataName pc uc) [x]
declKind (NiceRecDef _ _ _ pc uc x _ _ _ _ pars _)= LoneDefs (RecName pc uc) [x]
declKind (NiceUnquoteDef _ _ _ tc cc xs _)  = LoneDefs (FunName tc cc) xs
declKind Axiom{}                            = OtherDecl
declKind NiceField{}                        = OtherDecl
declKind PrimitiveFunction{}                = OtherDecl
declKind NiceMutual{}                       = OtherDecl
declKind NiceModule{}                       = OtherDecl
declKind NiceModuleMacro{}                  = OtherDecl
declKind NiceOpen{}                         = OtherDecl
declKind NiceImport{}                       = OtherDecl
declKind NicePragma{}                       = OtherDecl
declKind NiceFunClause{}                    = OtherDecl
declKind NicePatternSyn{}                   = OtherDecl
declKind NiceGeneralize{}                   = OtherDecl
declKind NiceUnquoteDecl{}                  = OtherDecl

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
      NiceRecSig r acc abst _ _ x pars t ->
        let e = Generalized $ makePi (lamBindingsToTelescope r pars) t in
        Just (x, Axiom r acc abst NotInstanceDef defaultArgInfo x e)
      NiceDataSig r acc abst _ _ x pars t ->
        let e = Generalized $ makePi (lamBindingsToTelescope r pars) t in
        Just (x, Axiom r acc abst NotInstanceDef defaultArgInfo x e)
      _ -> Nothing

-- | Main. Fixities (or more precisely syntax declarations) are needed when
--   grouping function clauses.
niceDeclarations :: Fixities -> [Declaration] -> Nice [NiceDeclaration]
niceDeclarations fixs ds = do

  -- Run the nicifier in an initial environment. But keep the warnings.
  st <- get
  put $ initNiceEnv { niceWarn = niceWarn st }
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
          let tcccpc = ([terminationCheck k], [coverageCheck k], [positivityCheck k])
          ((tcs, ccs, pcs), (nds0, ds1)) <- untilAllDefined tcccpc ds
          -- If we still have lone signatures without any accompanying definition,
          -- we postulate the definition and substitute the axiom for the lone signature
          ps <- use loneSigs
          checkLoneSigs ps
          let ds0 = replaceSigs ps (d : nds0) -- NB: don't forget the LoneSig the block started with!
          -- We then keep processing the rest of the block
          tc <- combineTerminationChecks (getRange d) tcs
          let cc = combineCoverageChecks ccs
          let pc = combinePositivityChecks pcs
          (NiceMutual (getRange ds0) tc cc pc ds0 :) <$> inferMutualBlocks ds1
      where
        untilAllDefined :: ([TerminationCheck], [CoverageCheck], [PositivityCheck])
                        -> [NiceDeclaration]
                        -> Nice (([TerminationCheck], [CoverageCheck], [PositivityCheck]) -- checks for this block
                                , ([NiceDeclaration]                                      -- mutual block
                                , [NiceDeclaration])                                      -- leftovers
                                )
        untilAllDefined tcccpc@(tc, cc, pc) ds = do
          done <- noLoneSigs
          if done then return (tcccpc, ([], ds)) else
            case ds of
              []     -> return (tcccpc, ([], ds))
              d : ds -> case declKind d of
                LoneSigDecl r k x -> do
                  _ <- addLoneSig r x k
                  let tcccpc' = (terminationCheck k : tc, coverageCheck k : cc, positivityCheck k : pc)
                  cons d (untilAllDefined tcccpc' ds)
                LoneDefs k xs -> do
                  mapM_ removeLoneSig xs
                  let tcccpc' = (terminationCheck k : tc, coverageCheck k : cc, positivityCheck k : pc)
                  cons d (untilAllDefined tcccpc' ds)
                OtherDecl   -> cons d (untilAllDefined tcccpc ds)
          where
            -- ASR (26 December 2015): Type annotated version of the @cons@ function.
            -- cons d = fmap $
            --            (id :: (([TerminationCheck], [PositivityCheck]) -> ([TerminationCheck], [PositivityCheck])))
            --            *** (d :)
            --            *** (id :: [NiceDeclaration] -> [NiceDeclaration])
            cons d = fmap (second (first (d :)))

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
              LHS p [] [] _ | Just x <- isSingleIdentifierP p -> do
                d  <- mkFunDef defaultArgInfo termCheck covCheck x Nothing [d] -- fun def without type signature is relevant
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

        DataSig r x tel t -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          _ <- addLoneSig r x $ DataName pc uc
          (,ds) <$> dataOrRec pc uc NiceDataDef NiceDataSig (niceAxioms DataBlock) r x (Just (tel, t)) Nothing

        Data r x tel t cs -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (DataName pc uc) x (Just t)
          (,ds) <$> dataOrRec pc uc NiceDataDef NiceDataSig (niceAxioms DataBlock) r x ((tel,) <$> mt) (Just (tel, cs))

        DataDef r x tel cs -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (DataName pc uc) x Nothing
          (,ds) <$> dataOrRec pc uc NiceDataDef NiceDataSig (niceAxioms DataBlock) r x ((tel,) <$> mt) (Just (tel, cs))

        RecordSig r x tel t         -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          _ <- addLoneSig r x $ RecName pc uc
          return ([NiceRecSig r PublicAccess ConcreteDef pc uc x tel t] , ds)

        Record r x i e p c tel t cs   -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (RecName pc uc) x (Just t)
          (,ds) <$> dataOrRec pc uc (\ r o a pc uc x tel cs -> NiceRecDef r o a pc uc x i e p c tel cs) NiceRecSig
                      return r x ((tel,) <$> mt) (Just (tel, cs))

        RecordDef r x i e p c tel cs   -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (RecName pc uc) x Nothing
          (,ds) <$> dataOrRec pc uc (\ r o a pc uc x tel cs -> NiceRecDef r o a pc uc x i e p c tel cs) NiceRecSig
                      return r x ((tel,) <$> mt) (Just (tel, cs))

        Mutual r ds' -> do
          -- The lone signatures encountered so far are not in scope
          -- for the mutual definition
          forgetLoneSigs
          case ds' of
            [] -> justWarning $ EmptyMutual r
            _  -> (,ds) <$> (singleton <$> (mkOldMutual r =<< nice ds'))

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

        Module r x tel ds' -> return $
          ([NiceModule r PublicAccess ConcreteDef x tel ds'] , ds)

        ModuleMacro r x modapp op is -> return $
          ([NiceModuleMacro r PublicAccess x modapp op is] , ds)

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

        Pragma p -> nicePragma p ds

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
      declarationWarning $ PragmaCompiled (getRange p)
      return ([NicePragma (getRange p) p], ds)

    nicePragma (PolarityPragma{}) ds = return ([], ds)

    nicePragma (BuiltinPragma r str qn@(QName x)) ds = do
      return ([NicePragma r (BuiltinPragma r str qn)], ds)

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
         -- ^ Construct definition.
      -> (Range -> Access -> IsAbstract -> PositivityCheck -> UniverseCheck -> Name -> [LamBinding] -> Expr -> NiceDeclaration)
         -- ^ Construct signature.
      -> ([a] -> Nice [decl])
         -- ^ Constructor checking.
      -> Range
      -> Name          -- ^ Data/record type name.
      -> Maybe ([LamBinding], Expr)    -- ^ Parameters and type.  If not @Nothing@ a signature is created.
      -> Maybe ([LamBinding], [a])     -- ^ Parameters and constructors.  If not @Nothing@, a definition body is created.
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
      where
        -- | Drop type annotations and lets from bindings.
        dropTypeAndModality :: LamBinding -> [LamBinding]
        dropTypeAndModality (DomainFull (TBind _ xs _)) =
          map (DomainFree . setModality defaultModality) $ List1.toList xs
        dropTypeAndModality (DomainFull TLet{}) = []
        dropTypeAndModality (DomainFree x) = [DomainFree $ setModality defaultModality x]

    -- Translate axioms
    niceAxioms :: KindOfBlock -> [TypeSignatureOrInstanceBlock] -> Nice [NiceDeclaration]
    niceAxioms b ds = List.concat <$> mapM (niceAxiom b) ds

    niceAxiom :: KindOfBlock -> TypeSignatureOrInstanceBlock -> Nice [NiceDeclaration]
    niceAxiom b d = case d of
      TypeSig rel _tac x t -> do
        return [ Axiom (getRange d) PublicAccess ConcreteDef NotInstanceDef rel x t ]
      FieldSig i tac x argt | b == FieldBlock -> do
        return [ NiceField (getRange d) PublicAccess ConcreteDef i tac x argt ]
      InstanceB r decls -> do
        instanceBlock r =<< niceAxioms InstanceBlock decls
      Pragma p@(RewritePragma r _ _) -> do
        return [ NicePragma r p ]
      _ -> declarationException $ WrongContentBlock b $ getRange d

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
    expandEllipsis (d@(FunClause lhs@(LHS p _ _ ell) _ _ _) : ds)
      | ExpandedEllipsis{} <- ell = __IMPOSSIBLE__
      | hasEllipsis p = (d :) <$> expandEllipsis ds
      | otherwise     = (d :) <$> expand (killRange p) ds
      where
        expand :: Pattern -> [Declaration] -> Nice [Declaration]
        expand _ [] = return []
        expand p (d : ds) = do
          case d of
            Pragma (CatchallPragma _) -> do
                  (d :) <$> expand p ds
            FunClause (LHS p0 eqs es NoEllipsis) rhs wh ca -> do
              case hasEllipsis' p0 of
                ManyHoles -> declarationException $ MultipleEllipses p0
                OneHole cxt ~(EllipsisP r) -> do
                  -- Replace the ellipsis by @p@.
                  let p1 = cxt $ setRange r p
                  let ell = ExpandedEllipsis r (numberOfWithPatterns p)
                  let d' = FunClause (LHS p1 eqs es ell) rhs wh ca
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
        numWith = numberOfWithPatterns p + length (filter visible es) where LHS p _ es _ = lhs

        subClauses :: [Declaration] -> ([Declaration],[Declaration])
        subClauses (c@(FunClause (LHS p0 _ _ _) _ _ _) : cs)
         | isEllipsis p0 ||
           numberOfWithPatterns p0 >= numWith = mapFst (c:) (subClauses cs)
         | otherwise                           = ([], c:cs)
        subClauses (c@(Pragma (CatchallPragma r)) : cs) = case subClauses cs of
          ([], cs') -> ([], c:cs')
          (cs, cs') -> (c:cs, cs')
        subClauses [] = ([],[])
        subClauses _  = __IMPOSSIBLE__
    mkClauses _ _ _ = __IMPOSSIBLE__

    -- for finding clauses for a type sig in mutual blocks
    couldBeFunClauseOf :: Maybe Fixity' -> Name -> Declaration -> Bool
    couldBeFunClauseOf mFixity x (Pragma (CatchallPragma{})) = True
    couldBeFunClauseOf mFixity x (FunClause (LHS p _ _ _) _ _ _) = hasEllipsis p ||
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
    couldBeFunClauseOf _ _ _ = False -- trace ("couldBe not (fun default)") $ False

    -- | Turn an old-style mutual block into a new style mutual block
    --   by pushing the definitions to the end.
    mkOldMutual
      :: Range                -- ^ Range of the whole @mutual@ block.
      -> [NiceDeclaration]    -- ^ Declarations inside the block.
      -> Nice NiceDeclaration -- ^ Returns a 'NiceMutual'.
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
        termCheck Axiom{}             = TerminationCheck
        termCheck NiceField{}         = TerminationCheck
        termCheck PrimitiveFunction{} = TerminationCheck
        termCheck NiceModule{}        = TerminationCheck
        termCheck NiceModuleMacro{}   = TerminationCheck
        termCheck NiceOpen{}          = TerminationCheck
        termCheck NiceImport{}        = TerminationCheck
        termCheck NicePragma{}        = TerminationCheck
        termCheck NiceRecSig{}        = TerminationCheck
        termCheck NiceDataSig{}       = TerminationCheck
        termCheck NiceFunClause{}     = TerminationCheck
        termCheck NiceDataDef{}       = TerminationCheck
        termCheck NiceRecDef{}        = TerminationCheck
        termCheck NicePatternSyn{}    = TerminationCheck
        termCheck NiceGeneralize{}    = TerminationCheck

        covCheck :: NiceDeclaration -> CoverageCheck
        covCheck (FunSig _ _ _ _ _ _ _ cc _ _)      = cc
        covCheck (FunDef _ _ _ _ _ cc _ _)          = cc
        -- ASR (28 December 2015): Is this equation necessary?
        covCheck (NiceMutual _ _ cc _ _)            = cc
        covCheck (NiceUnquoteDecl _ _ _ _ _ cc _ _) = cc
        covCheck (NiceUnquoteDef _ _ _ _ cc _ _)    = cc
        covCheck Axiom{}             = YesCoverageCheck
        covCheck NiceField{}         = YesCoverageCheck
        covCheck PrimitiveFunction{} = YesCoverageCheck
        covCheck NiceModule{}        = YesCoverageCheck
        covCheck NiceModuleMacro{}   = YesCoverageCheck
        covCheck NiceOpen{}          = YesCoverageCheck
        covCheck NiceImport{}        = YesCoverageCheck
        covCheck NicePragma{}        = YesCoverageCheck
        covCheck NiceRecSig{}        = YesCoverageCheck
        covCheck NiceDataSig{}       = YesCoverageCheck
        covCheck NiceFunClause{}     = YesCoverageCheck
        covCheck NiceDataDef{}       = YesCoverageCheck
        covCheck NiceRecDef{}        = YesCoverageCheck
        covCheck NicePatternSyn{}    = YesCoverageCheck
        covCheck NiceGeneralize{}    = YesCoverageCheck

        -- ASR (26 December 2015): Do not positivity check a mutual
        -- block if any of its inner declarations comes with a
        -- NO_POSITIVITY_CHECK pragma. See Issue 1614.
        positivityCheckOldMutual :: NiceDeclaration -> PositivityCheck
        positivityCheckOldMutual (NiceDataDef _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (NiceDataSig _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (NiceMutual _ _ _ pc _)        = pc
        positivityCheckOldMutual (NiceRecSig _ _ _ pc _ _ _ _)  = pc
        positivityCheckOldMutual (NiceRecDef _ _ _ pc _ _ _ _ _ _ _ _) = pc
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
      :: Range  -- ^ Range of @instance@ keyword.
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
      :: Range  -- ^ Range of @instance@ keyword.
      -> Updater NiceDeclaration
    mkInstance r0 = \case
        Axiom r p a i rel x e          -> (\ i -> Axiom r p a i rel x e) <$> setInstance r0 i
        FunSig r p a i m rel tc cc x e -> (\ i -> FunSig r p a i m rel tc cc x e) <$> setInstance r0 i
        NiceUnquoteDecl r p a i tc cc x e -> (\ i -> NiceUnquoteDecl r p a i tc cc x e) <$> setInstance r0 i
        NiceMutual r tc cc pc ds        -> NiceMutual r tc cc pc <$> mapM (mkInstance r0) ds
        d@NiceFunClause{}              -> return d
        FunDef r ds a i tc cc x cs     -> (\ i -> FunDef r ds a i tc cc x cs) <$> setInstance r0 i
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

    setInstance
      :: Range  -- ^ Range of @instance@ keyword.
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
      FunDef r ds a i tc cc x cs       -> (\ a -> FunDef r ds a i tc cc x) <$> mkAbstract a <*> mkAbstract cs
      NiceDataDef r o a pc uc x ps cs  -> (\ a -> NiceDataDef r o a pc uc x ps) <$> mkAbstract a <*> mkAbstract cs
      NiceRecDef r o a pc uc x i e p c ps cs -> (\ a -> NiceRecDef r o a pc uc x i e p c ps cs) <$> mkAbstract a
      NiceFunClause r p a tc cc catchall d  -> (\ a -> NiceFunClause r p a tc cc catchall d) <$> mkAbstract a
      -- The following declarations have an @InAbstract@ field
      -- but are not really definitions, so we do count them into
      -- the declarations which can be made abstract
      -- (thus, do not notify progress with @dirty@).
      Axiom r p a i rel x e          -> return $ Axiom             r p AbstractDef i rel x e
      FunSig r p a i m rel tc cc x e -> return $ FunSig            r p AbstractDef i m rel tc cc x e
      NiceRecSig r p a pc uc x ls t  -> return $ NiceRecSig        r p AbstractDef pc uc x ls t
      NiceDataSig r p a pc uc x ls t -> return $ NiceDataSig       r p AbstractDef pc uc x ls t
      NiceField r p _ i tac x e      -> return $ NiceField         r p AbstractDef i tac x e
      PrimitiveFunction r p _ x e    -> return $ PrimitiveFunction r p AbstractDef x e
      -- Andreas, 2016-07-17 it does have effect on unquoted defs.
      -- Need to set updater state to dirty!
      NiceUnquoteDecl r p _ i tc cc x e -> tellDirty $> NiceUnquoteDecl r p AbstractDef i tc cc x e
      NiceUnquoteDef r p _ tc cc x e    -> tellDirty $> NiceUnquoteDef r p AbstractDef tc cc x e
      d@NiceModule{}                 -> return d
      d@NiceModuleMacro{}            -> return d
      d@NicePragma{}                 -> return d
      d@(NiceOpen _ _ directives)              -> do
        whenJust (publicOpen directives) $ lift . declarationWarning . OpenPublicAbstract
        return d
      d@NiceImport{}                 -> return d
      d@NicePatternSyn{}             -> return d
      d@NiceGeneralize{}             -> return d

instance MakeAbstract Clause where
  mkAbstract (Clause x catchall lhs rhs wh with) = do
    Clause x catchall lhs rhs <$> mkAbstract wh <*> mkAbstract with

-- | Contents of a @where@ clause are abstract if the parent is.
instance MakeAbstract WhereClause where
  mkAbstract  NoWhere             = return $ NoWhere
  mkAbstract (AnyWhere r ds)      = dirty $ AnyWhere r [Abstract noRange ds]
  mkAbstract (SomeWhere r m a ds) = dirty $ SomeWhere r m a [Abstract noRange ds]

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
      NiceModule r p a x tel ds                -> (\ p -> NiceModule r p a x tel ds)            <$> mkPrivate o p
      NiceModuleMacro r p x ma op is           -> (\ p -> NiceModuleMacro r p x ma op is)       <$> mkPrivate o p
      FunSig r p a i m rel tc cc x e           -> (\ p -> FunSig r p a i m rel tc cc x e)       <$> mkPrivate o p
      NiceRecSig r p a pc uc x ls t            -> (\ p -> NiceRecSig r p a pc uc x ls t)        <$> mkPrivate o p
      NiceDataSig r p a pc uc x ls t           -> (\ p -> NiceDataSig r p a pc uc x ls t)       <$> mkPrivate o p
      NiceFunClause r p a tc cc catchall d     -> (\ p -> NiceFunClause r p a tc cc catchall d) <$> mkPrivate o p
      NiceUnquoteDecl r p a i tc cc x e        -> (\ p -> NiceUnquoteDecl r p a i tc cc x e)    <$> mkPrivate o p
      NiceUnquoteDef r p a tc cc x e           -> (\ p -> NiceUnquoteDef r p a tc cc x e)       <$> mkPrivate o p
      NicePatternSyn r p x xs p'               -> (\ p -> NicePatternSyn r p x xs p')           <$> mkPrivate o p
      NiceGeneralize r p i tac x t             -> (\ p -> NiceGeneralize r p i tac x t)         <$> mkPrivate o p
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
    SomeWhere r m a ds -> mkPrivate o a <&> \ a' -> SomeWhere r m a' ds

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
    NiceModule r _ _ x tel ds      -> [Module r x tel ds]
    NiceModuleMacro r _ x ma o dir -> [ModuleMacro r x ma o dir]
    NiceOpen r x dir               -> [Open r x dir]
    NiceImport r x as o dir        -> [Import r x as o dir]
    NicePragma _ p                 -> [Pragma p]
    NiceRecSig r _ _ _ _ x bs e    -> [RecordSig r x bs e]
    NiceDataSig r _ _ _ _ x bs e   -> [DataSig r x bs e]
    NiceFunClause _ _ _ _ _ _ d    -> [d]
    FunSig _ _ _ i _ rel _ _ x e   -> inst i [TypeSig rel Nothing x e]
    FunDef _ ds _ _ _ _ _ _        -> ds
    NiceDataDef r _ _ _ _ x bs cs  -> [DataDef r x bs $ concatMap notSoNiceDeclarations cs]
    NiceRecDef r _ _ _ _ x i e p c bs ds -> [RecordDef r x i e p c bs ds]
    NicePatternSyn r _ n as p      -> [PatternSyn r n as p]
    NiceGeneralize r _ i tac n e   -> [Generalize r [TypeSig i tac n e]]
    NiceUnquoteDecl r _ _ i _ _ x e -> inst i [UnquoteDecl r x e]
    NiceUnquoteDef r _ _ _ _ x e    -> [UnquoteDef r x e]
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
    NiceModule _ _ a _ _ _        -> Just a
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
    NiceRecDef _ _ a _ _ _ _ _ _ _ _ _ -> Just a
    NicePatternSyn{}              -> Nothing
    NiceGeneralize{}              -> Nothing
    NiceUnquoteDecl _ _ a _ _ _ _ _ -> Just a
    NiceUnquoteDef _ _ a _ _ _ _    -> Just a
