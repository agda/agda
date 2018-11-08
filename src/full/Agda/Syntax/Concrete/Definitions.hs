{-# LANGUAGE CPP                #-}
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
    , DeclarationWarning(..)
    , Nice, runNice
    , niceDeclarations
    , notSoNiceDeclarations
    , niceHasAbstract
    , Measure
    , declarationWarningName
    ) where

import Prelude hiding (null)

import Control.Arrow ((&&&), (***), first, second)
import Control.Applicative hiding (empty)
import Control.Monad.Except
import Control.Monad.State

import Data.Either ( partitionEithers )
import Data.Function ( on )
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Monoid ( Monoid, mempty, mappend )
import Data.Semigroup ( Semigroup, (<>) )
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse)
import qualified Data.Traversable as Trav

import Data.Data (Data)

import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Pattern
import Agda.Syntax.Common hiding (TerminationCheck())
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete.Pretty ()

import Agda.Interaction.Options.Warnings

import Agda.TypeChecking.Positivity.Occurrence
import {-# SOURCE #-} Agda.TypeChecking.Monad.Builtin ( builtinsNoDef )

import Agda.Utils.AffineHole
import Agda.Utils.Except ( MonadError(throwError,catchError) )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List (caseList, headMaybe, isSublistOf)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as Pretty
import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.Singleton
import Agda.Utils.Three
import Agda.Utils.Tuple
import Agda.Utils.Update

#include "undefined.h"
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
  = Axiom Range Fixity' Access IsAbstract IsInstance ArgInfo (Maybe [Occurrence]) Name Expr
      -- ^ 'IsAbstract' argument: We record whether a declaration was made in an @abstract@ block.
      --
      --   'ArgInfo' argument: Axioms and functions can be declared irrelevant.
      --   ('Hiding' should be 'NotHidden'.)
      --
      --   @Maybe [Occurrence]@ argument: Polarities can be assigned to identifiers.
  | NiceField Range Fixity' Access IsAbstract IsInstance Name (Arg Expr)
  | PrimitiveFunction Range Fixity' Access IsAbstract Name Expr
  | NiceMutual Range TerminationCheck PositivityCheck [NiceDeclaration]
  | NiceModule Range Access IsAbstract QName Telescope [Declaration]
  | NiceModuleMacro Range Access Name ModuleApplication OpenShortHand ImportDirective
  | NiceOpen Range QName ImportDirective
  | NiceImport Range QName (Maybe AsName) OpenShortHand ImportDirective
  | NicePragma Range Pragma
  | NiceRecSig Range Fixity' Access IsAbstract PositivityCheck UniverseCheck Name [LamBinding] Expr
  | NiceDataSig Range Fixity' Access IsAbstract PositivityCheck UniverseCheck Name [LamBinding] Expr
  | NiceFunClause Range Access IsAbstract TerminationCheck Catchall Declaration
    -- ^ An uncategorized function clause, could be a function clause
    --   without type signature or a pattern lhs (e.g. for irrefutable let).
    --   The 'Declaration' is the actual 'FunClause'.
  | FunSig Range Fixity' Access IsAbstract IsInstance IsMacro ArgInfo TerminationCheck Name Expr
  | FunDef Range [Declaration] Fixity' IsAbstract IsInstance TerminationCheck Name [Clause]
      -- ^ Block of function clauses (we have seen the type signature before).
      --   The 'Declaration's are the original declarations that were processed
      --   into this 'FunDef' and are only used in 'notSoNiceDeclaration'.
      --   Andreas, 2017-01-01: Because of issue #2372, we add 'IsInstance' here.
      --   An alias should know that it is an instance.
  | DataDef Range Fixity' IsAbstract PositivityCheck UniverseCheck Name [LamBinding] [NiceConstructor]
  | RecDef Range Fixity' IsAbstract PositivityCheck UniverseCheck Name (Maybe (Ranged Induction)) (Maybe HasEta) (Maybe (ThingWithFixity Name, IsInstance)) [LamBinding] [NiceDeclaration]
  | NicePatternSyn Range Fixity' Name [Arg Name] Pattern
  | NiceGeneralize Range Fixity' Access ArgInfo Name Expr
  | NiceUnquoteDecl Range [Fixity'] Access IsAbstract IsInstance TerminationCheck [Name] Expr
  | NiceUnquoteDef Range [Fixity'] Access IsAbstract TerminationCheck [Name] Expr
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

-- | The exception type.
data DeclarationException
        = MultipleFixityDecls [(Name, [Fixity'])]
        | MultiplePolarityPragmas [Name]
        | MultipleEllipses Pattern
        | InvalidName Name
        | DuplicateDefinition Name
        | MissingWithClauses Name LHS
        | WrongDefinition Name DataRecOrFun DataRecOrFun
        | WrongParameters Name Params Params
          -- ^ 'Name' of symbol, 'Params' of signature, 'Params' of definition.
        | Codata Range
        | DeclarationPanic String
        | WrongContentBlock KindOfBlock Range
        | AmbiguousFunClauses LHS [Name] -- ^ in a mutual block, a clause could belong to any of the @[Name]@ type signatures
        | InvalidMeasureMutual Range
          -- ^ In a mutual block, all or none need a MEASURE pragma.
          --   Range is of mutual block.
        | UnquoteDefRequiresSignature [Name]
        | BadMacroDef NiceDeclaration
    deriving (Data, Show)

-- | Non-fatal errors encountered in the Nicifier
data DeclarationWarning
  = EmptyAbstract Range   -- ^ Empty @abstract@  block.
  | EmptyInstance Range   -- ^ Empty @instance@  block
  | EmptyMacro Range      -- ^ Empty @macro@     block.
  | EmptyMutual Range     -- ^ Empty @mutual@    block.
  | EmptyPostulate Range  -- ^ Empty @postulate@ block.
  | EmptyPrivate Range    -- ^ Empty @private@   block.
  | EmptyGeneralize Range -- ^ Empty @variable@  block.
  | InvalidCatchallPragma Range
      -- ^ A {-\# CATCHALL \#-} pragma
      --   that does not precede a function clause.
  | InvalidNoPositivityCheckPragma Range
      -- ^ A {-\# NO_POSITIVITY_CHECK \#-} pragma
      --   that does not apply to any data or record type.
  | InvalidNoUniverseCheckPragma Range
      -- ^ A {-\# NO_UNIVERSE_CHECK \#-} pragma
      --   that does not apply to a data or record type.
  | InvalidTerminationCheckPragma Range
      -- ^ A {-\# TERMINATING \#-} and {-\# NON_TERMINATING \#-} pragma
      --   that does not apply to any function.
  | MissingDefinitions [Name]
  | NotAllowedInMutual Range String
  | PolarityPragmasButNotPostulates [Name]
  | PragmaNoTerminationCheck Range
  -- ^ Pragma @{-\# NO_TERMINATION_CHECK \#-}@ has been replaced
  --   by @{-\# TERMINATING \#-}@ and @{-\# NON_TERMINATING \#-}@.
  | UnknownFixityInMixfixDecl [Name]
  | UnknownNamesInFixityDecl [Name]
  | UnknownNamesInPolarityPragmas [Name]
  | UselessAbstract Range
  | UselessInstance Range
  | UselessPrivate Range
  deriving (Data, Show)

declarationWarningName :: DeclarationWarning -> WarningName
declarationWarningName dw = case dw of
  EmptyAbstract{}                   -> EmptyAbstract_
  EmptyInstance{}                   -> EmptyInstance_
  EmptyMacro{}                      -> EmptyMacro_
  EmptyMutual{}                     -> EmptyMutual_
  EmptyPrivate{}                    -> EmptyPrivate_
  EmptyPostulate{}                  -> EmptyPostulate_
  EmptyGeneralize{}                 -> EmptyGeneralize_
  InvalidCatchallPragma{}           -> InvalidCatchallPragma_
  InvalidNoPositivityCheckPragma{}  -> InvalidNoPositivityCheckPragma_
  InvalidNoUniverseCheckPragma{}    -> InvalidNoUniverseCheckPragma_
  InvalidTerminationCheckPragma{}   -> InvalidTerminationCheckPragma_
  MissingDefinitions{}              -> MissingDefinitions_
  NotAllowedInMutual{}              -> NotAllowedInMutual_
  PolarityPragmasButNotPostulates{} -> PolarityPragmasButNotPostulates_
  PragmaNoTerminationCheck{}        -> PragmaNoTerminationCheck_
  UnknownFixityInMixfixDecl{}       -> UnknownFixityInMixfixDecl_
  UnknownNamesInFixityDecl{}        -> UnknownNamesInFixityDecl_
  UnknownNamesInPolarityPragmas{}   -> UnknownNamesInPolarityPragmas_
  UselessAbstract{}                 -> UselessAbstract_
  UselessInstance{}                 -> UselessInstance_
  UselessPrivate{}                  -> UselessPrivate_

-- | Several declarations expect only type signatures as sub-declarations.  These are:
data KindOfBlock
  = PostulateBlock  -- ^ @postulate@
  | PrimitiveBlock  -- ^ @primitive@.  Ensured by parser.
  | InstanceBlock   -- ^ @instance@.  Actually, here all kinds of sub-declarations are allowed a priori.
  | FieldBlock      -- ^ @field@.  Ensured by parser.
  | DataBlock       -- ^ @data ... where@.  Here we got a bad error message for Agda-2.5 (Issue 1698).
  deriving (Data, Eq, Ord, Show)


instance HasRange DeclarationException where
  getRange (MultipleFixityDecls xs)             = getRange (fst $ head xs)
  getRange (MultiplePolarityPragmas xs)         = getRange (head xs)
  getRange (MultipleEllipses d)                 = getRange d
  getRange (InvalidName x)                      = getRange x
  getRange (DuplicateDefinition x)              = getRange x
  getRange (MissingWithClauses x lhs)           = getRange lhs
  getRange (WrongDefinition x k k')             = getRange x
  getRange (WrongParameters x _ _)              = getRange x
  getRange (AmbiguousFunClauses lhs xs)         = getRange lhs
  getRange (Codata r)                           = r
  getRange (DeclarationPanic _)                 = noRange
  getRange (WrongContentBlock _ r)              = r
  getRange (InvalidMeasureMutual r)             = r
  getRange (UnquoteDefRequiresSignature x)      = getRange x
  getRange (BadMacroDef d)                      = getRange d

instance HasRange DeclarationWarning where
  getRange (UnknownNamesInFixityDecl xs)        = getRange . head $ xs
  getRange (UnknownFixityInMixfixDecl xs)       = getRange . head $ xs
  getRange (UnknownNamesInPolarityPragmas xs)   = getRange . head $ xs
  getRange (PolarityPragmasButNotPostulates xs) = getRange . head $ xs
  getRange (MissingDefinitions xs)              = getRange . head $ xs
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
  getRange (InvalidTerminationCheckPragma r)    = r
  getRange (InvalidNoPositivityCheckPragma r)   = r
  getRange (InvalidCatchallPragma r)            = r
  getRange (InvalidNoUniverseCheckPragma r)     = r
  getRange (PragmaNoTerminationCheck r)         = r

instance HasRange NiceDeclaration where
  getRange (Axiom r _ _ _ _ _ _ _ _)         = r
  getRange (NiceField r _ _ _ _ _ _)         = r
  getRange (NiceMutual r _ _ _)              = r
  getRange (NiceModule r _ _ _ _ _ )         = r
  getRange (NiceModuleMacro r _ _ _ _ _)     = r
  getRange (NiceOpen r _ _)                  = r
  getRange (NiceImport r _ _ _ _)            = r
  getRange (NicePragma r _)                  = r
  getRange (PrimitiveFunction r _ _ _ _ _)   = r
  getRange (FunSig r _ _ _ _ _ _ _ _ _)      = r
  getRange (FunDef r _ _ _ _ _ _ _)          = r
  getRange (DataDef r _ _ _ _ _ _ _)         = r
  getRange (RecDef r _ _ _ _ _ _ _ _ _ _)    = r
  getRange (NiceRecSig r _ _ _ _ _ _ _ _)    = r
  getRange (NiceDataSig r _ _ _ _ _ _ _ _)   = r
  getRange (NicePatternSyn r _ _ _ _)        = r
  getRange (NiceGeneralize r _ _ _ _ _)      = r
  getRange (NiceFunClause r _ _ _ _ _)       = r
  getRange (NiceUnquoteDecl r _ _ _ _ _ _ _) = r
  getRange (NiceUnquoteDef r _ _ _ _ _ _)    = r

instance Pretty NiceDeclaration where
  pretty = \case
    Axiom _ _ _ _ _ _ _ x _          -> text "postulate" <+> pretty x <+> colon <+> text "_"
    NiceField _ _ _ _ _ x _          -> text "field" <+> pretty x
    PrimitiveFunction _ _ _ _ x _    -> text "primitive" <+> pretty x
    NiceMutual{}                     -> text "mutual"
    NiceModule _ _ _ x _ _           -> text "module" <+> pretty x <+> text "where"
    NiceModuleMacro _ _ x _ _ _      -> text "module" <+> pretty x <+> text "= ..."
    NiceOpen _ x _                   -> text "open" <+> pretty x
    NiceImport _ x _ _ _             -> text "import" <+> pretty x
    NicePragma{}                     -> text "{-# ... #-}"
    NiceRecSig _ _ _ _ _ _ x _ _     -> text "record" <+> pretty x
    NiceDataSig _ _ _ _ _ _ x _ _    -> text "data" <+> pretty x
    NiceFunClause{}                  -> text "<function clause>"
    FunSig _ _ _ _ _ _ _ _ x _       -> pretty x <+> colon <+> text "_"
    FunDef _ _ _ _ _ _ x _           -> pretty x <+> text "= _"
    DataDef _ _ _ _ _ x _ _          -> text "data" <+> pretty x <+> text "where"
    RecDef _ _ _ _ _ x _ _ _ _ _     -> text "record" <+> pretty x <+> text "where"
    NicePatternSyn _ _ x _ _         -> text "pattern" <+> pretty x
    NiceGeneralize _ _ _ _ x _       -> text "variable" <+> pretty x
    NiceUnquoteDecl _ _ _ _ _ _ xs _ -> text "<unquote declarations>"
    NiceUnquoteDef _ _ _ _ _ xs _    -> text "<unquote definitions>"

-- These error messages can (should) be terminated by a dot ".",
-- there is no error context printed after them.
instance Pretty DeclarationException where
  pretty (MultipleFixityDecls xs) =
    sep [ fsep $ pwords "Multiple fixity or syntax declarations for"
        , vcat $ map f xs
        ]
      where
        f (x, fs) = pretty x Pretty.<> ": " <+> fsep (map pretty fs)
  pretty (MultiplePolarityPragmas xs) = fsep $
    pwords "Multiple polarity pragmas for" ++ map pretty xs
  pretty (MultipleEllipses p) = fsep $
    pwords "Multiple ellipses in left-hand side" ++ [pretty p]
  pretty (InvalidName x) = fsep $
    pwords "Invalid name:" ++ [pretty x]
  pretty (DuplicateDefinition x) = fsep $
    pwords "Duplicate definition of" ++ [pretty x]
  pretty (MissingWithClauses x lhs) = fsep $
    pwords "Missing with-clauses for function" ++ [pretty x]

  pretty (WrongDefinition x k k') = fsep $ pretty x :
    pwords ("has been declared as a " ++ show k ++
      ", but is being defined as a " ++ show k')
  pretty (WrongParameters x sig def) = fsep $
    pwords "List of parameters " ++ map pretty def ++
    pwords " does not match parameters " ++ map pretty sig ++
    pwords " of previous signature for " ++ [pretty x]
  pretty (AmbiguousFunClauses lhs xs) = sep
    [ fsep $
        pwords "More than one matching type signature for left hand side " ++ [pretty lhs] ++
        pwords "it could belong to any of:"
    , vcat $ map (pretty . PrintRange) xs
    ]
  pretty (WrongContentBlock b _)      = fsep . pwords $
    case b of
      PostulateBlock -> "A postulate block can only contain type signatures, possibly under keyword instance"
      DataBlock -> "A data definition can only contain type signatures, possibly under keyword instance"
      _ -> "Unexpected declaration"
  pretty (InvalidMeasureMutual _) = fsep $
    pwords "In a mutual block, either all functions must have the same (or no) termination checking pragma."
  pretty (UnquoteDefRequiresSignature xs) = fsep $
    pwords "Missing type signatures for unquoteDef" ++ map pretty xs
  pretty (BadMacroDef nd) = fsep $
    [text $ declName nd] ++ pwords "are not allowed in macro blocks"
  pretty (Codata _) = text $
    "The codata construction has been removed. " ++
    "Use the INFINITY builtin instead."
  pretty (DeclarationPanic s) = text s

instance Pretty DeclarationWarning where
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
   ++ punctuate comma (map pretty xs)
  pretty (NotAllowedInMutual r nd) = fsep $
    [text nd] ++ pwords "in mutual blocks are not supported.  Suggestion: get rid of mutual block by manually ordering declarations"
  pretty (PolarityPragmasButNotPostulates xs) = fsep $
    pwords "Polarity pragmas have been given for the following identifiers which are not postulates:"
    ++ punctuate comma (map pretty xs)
  pretty (UselessPrivate _)      = fsep $
    pwords "Using private here has no effect. Private applies only to declarations that introduce new identifiers into the module, like type signatures and data, record, and module declarations."
  pretty (UselessAbstract _)      = fsep $
    pwords "Using abstract here has no effect. Abstract applies to only definitions like data definitions, record type definitions and function clauses."
  pretty (UselessInstance _)      = fsep $
    pwords "Using instance here has no effect. Instance applies only to declarations that introduce new identifiers into the module, like type signatures and axioms."
  pretty (EmptyMutual    _) = fsep $ pwords "Empty mutual block."
  pretty (EmptyAbstract  _) = fsep $ pwords "Empty abstract block."
  pretty (EmptyPrivate   _) = fsep $ pwords "Empty private block."
  pretty (EmptyInstance  _) = fsep $ pwords "Empty instance block."
  pretty (EmptyMacro     _) = fsep $ pwords "Empty macro block."
  pretty (EmptyPostulate _) = fsep $ pwords "Empty postulate block."
  pretty (EmptyGeneralize _)= fsep $ pwords "Empty variable block."
  pretty (InvalidTerminationCheckPragma _) = fsep $
    pwords "Termination checking pragmas can only precede a function definition or a mutual block (that contains a function definition)."
  pretty (InvalidNoPositivityCheckPragma _) = fsep $
    pwords "NO_POSITIVITY_CHECKING pragmas can only precede a data/record definition or a mutual block (that contains a data/record definition)."
  pretty (InvalidCatchallPragma _) = fsep $
    pwords "The CATCHALL pragma can only precede a function clause."
  pretty (InvalidNoUniverseCheckPragma _) = fsep $
    pwords "NO_UNIVERSE_CHECKING pragmas can only precede a data/record definition."
  pretty (PragmaNoTerminationCheck _) = fsep $
    pwords "Pragma {-# NO_TERMINATION_CHECK #-} has been removed.  To skip the termination check, label your definitions either as {-# TERMINATING #-} or {-# NON_TERMINATING #-}."

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
declName RecDef{}            = "Records"
declName DataDef{}           = "Data types"

{--------------------------------------------------------------------------
    The niceifier
 --------------------------------------------------------------------------}

data InMutual
  = InMutual    -- ^ we are nicifying a mutual block
  | NotInMutual -- ^ we are nicifying decls not in a mutual block
    deriving (Eq, Show)

-- | The kind of the forward declaration, remembering the parameters.

type Params = [Arg BoundName]

data DataRecOrFun
  = DataName
    { kindPosCheck :: PositivityCheck
    , kindUniCheck :: UniverseCheck
    , kindParams :: Params
    }
    -- ^ Name of a data type with parameters.
  | RecName
    { kindPosCheck :: PositivityCheck
    , kindUniCheck :: UniverseCheck
    , kindParams :: Params
    }
    -- ^ Name of a record type with parameters.
  | FunName TerminationCheck
    -- ^ Name of a function.
  deriving Data

-- Ignore pragmas when checking equality
instance Eq DataRecOrFun where
  DataName _ _ p == DataName _ _ q = p == q
  RecName  _ _ p == RecName  _ _ q = p == q
  FunName _      == FunName _      = True
  _              == _              = False

instance Show DataRecOrFun where
  show (DataName _ _ n) = "data type" --  "with " ++ show n ++ " visible parameters"
  show (RecName _ _ n)  = "record type" -- "with " ++ show n ++ " visible parameters"
  show (FunName{})      = "function"

isFunName :: DataRecOrFun -> Bool
isFunName (FunName{}) = True
isFunName _           = False

sameKind :: DataRecOrFun -> DataRecOrFun -> Bool
sameKind DataName{} DataName{} = True
sameKind RecName{} RecName{} = True
sameKind FunName{} FunName{} = True
sameKind _ _ = False

terminationCheck :: DataRecOrFun -> TerminationCheck
terminationCheck (FunName tc) = tc
terminationCheck _ = TerminationCheck

positivityCheck :: DataRecOrFun -> PositivityCheck
positivityCheck (DataName pc _ _) = pc
positivityCheck (RecName pc _ _)  = pc
positivityCheck _                 = True

universeCheck :: DataRecOrFun -> UniverseCheck
universeCheck (DataName _ uc _) = uc
universeCheck (RecName _ uc _)  = uc
universeCheck _                 = YesUniverseCheck

-- | Check that declarations in a mutual block are consistently
--   equipped with MEASURE pragmas, or whether there is a
--   NO_TERMINATION_CHECK pragma.
combineTermChecks :: Range -> [TerminationCheck] -> Nice TerminationCheck
combineTermChecks r tcs = loop tcs where
  loop :: [TerminationCheck] -> Nice TerminationCheck
  loop []         = return TerminationCheck
  loop (tc : tcs) = do
    let failure r = throwError $ InvalidMeasureMutual r
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

-- | Check that the parameters of the data/record definition
--   match the parameters of the corresponding signature.
--
--   The definition may omit some hidden parameters.
--   The names need to match.
--   The types are not checked here.
--
--   Precondition: the signature and definition have the same kind (data/record/fun).
--
matchParameters
  :: Name          -- ^ The data/record name.
  -> DataRecOrFun  -- ^ The data/record signature.
  -> DataRecOrFun  -- ^ The parameters as given in the data/record definition.
  -> Nice ()
matchParameters _ FunName{} FunName{} = return ()
matchParameters x sig def = loop (kindParams sig) (kindParams def)
  where
  failure = throwError $ WrongParameters x (kindParams sig) (kindParams def)
  loop hs     []     = unless (all notVisible hs) failure
  loop []     (_:_)  = failure
  loop (h:hs) (j:js)
    | h == j                  = loop hs js
    | notVisible h, visible j = loop hs (j:js)
    | otherwise               = failure

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
  , fixs     :: Fixities
  , pols     :: Polarities
  , niceWarn :: NiceWarnings
    -- ^ Stack of warnings. Head is last warning.
  }

type LoneSigs   = Map Name DataRecOrFun
type Fixities   = Map Name Fixity'
type Polarities = Map Name [Occurrence]
type NiceWarnings = [DeclarationWarning]
     -- ^ Stack of warnings. Head is last warning.

-- | Initial nicifier state.

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { _loneSigs = empty
  , _termChk  = TerminationCheck
  , _posChk   = True
  , _uniChk   = YesUniverseCheck
  , _catchall = False
  , fixs      = empty
  , pols      = empty
  , niceWarn  = []
  }

-- * Handling the lone signatures, stored to infer mutual blocks.

-- | Lens for field '_loneSigs'.

loneSigs :: Lens' LoneSigs NiceEnv
loneSigs f e = f (_loneSigs e) <&> \ s -> e { _loneSigs = s }

-- | Adding a lone signature to the state.

addLoneSig :: Name -> DataRecOrFun -> Nice ()
addLoneSig x k = loneSigs %== \ s -> do
   let (mr, s') = Map.insertLookupWithKey (\ k new old -> new) x k s
   case mr of
     Nothing -> return s'
     Just{}  -> throwError $ DuplicateDefinition x

-- | Remove a lone signature from the state.

removeLoneSig :: Name -> Nice ()
removeLoneSig x = loneSigs %= Map.delete x

-- | Search for forward type signature.

getSig :: Name -> Nice (Maybe DataRecOrFun)
getSig x = Map.lookup x <$> use loneSigs

-- | Check that no lone signatures are left in the state.

noLoneSigs :: Nice Bool
noLoneSigs = null <$> use loneSigs

-- | Ensure that all forward declarations have been given a definition.

checkLoneSigs :: Map Name DataRecOrFun -> Nice ()
checkLoneSigs xs = do
  loneSigs .= Map.empty
  unless (Map.null xs) (niceWarning $ MissingDefinitions $ Map.keys xs)

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

-- | Check whether name is not "_" and return its fixity.
getFixity :: Name -> Nice Fixity'
getFixity x = Map.findWithDefault noFixity' x <$> gets fixs -- WAS: defaultFixity'

-- | Fail if the name is @_@. Otherwise the name's polarity, if any,
-- is removed from the state and returned.
getPolarity :: Name -> Nice (Maybe [Occurrence])
getPolarity x = do
  p <- gets (Map.lookup x . pols)
  modify (\s -> s { pols = Map.delete x (pols s) })
  return p

data DeclKind
    = LoneSig DataRecOrFun Name
    | LoneDefs DataRecOrFun [Name]
    | OtherDecl
  deriving (Eq, Show)

declKind :: NiceDeclaration -> DeclKind
declKind (FunSig _ _ _ _ _ _ _ tc x _) = LoneSig (FunName tc) x
declKind (NiceRecSig _ _ _ _ pc uc x pars _) = LoneSig (RecName pc uc $ parameters pars) x
declKind (NiceDataSig _ _ _ _ pc uc x pars _) = LoneSig (DataName pc uc $ parameters pars) x
declKind (FunDef r _ fx abs ins tc x _) = LoneDefs (FunName tc) [x]
declKind (DataDef _ _ _ pc uc x pars _) = LoneDefs (DataName pc uc $ parameters pars) [x]
declKind (RecDef _ _ _ pc uc x _ _ _ pars _) = LoneDefs (RecName pc uc $ parameters pars) [x]
declKind (NiceUnquoteDef _ _ _ _ tc xs _) = LoneDefs (FunName tc) xs
declKind Axiom{}                          = OtherDecl
declKind NiceField{}                      = OtherDecl
declKind PrimitiveFunction{}              = OtherDecl
declKind NiceMutual{}                     = OtherDecl
declKind NiceModule{}                     = OtherDecl
declKind NiceModuleMacro{}                = OtherDecl
declKind NiceOpen{}                       = OtherDecl
declKind NiceImport{}                     = OtherDecl
declKind NicePragma{}                     = OtherDecl
declKind NiceFunClause{}                  = OtherDecl
declKind NicePatternSyn{}                 = OtherDecl
declKind NiceGeneralize{}                 = OtherDecl
declKind NiceUnquoteDecl{}                = OtherDecl

-- | Compute parameters of a data or record signature or definition.
parameters :: [LamBinding] -> Params
parameters = List.concatMap $ \case
  DomainFree i x                                      -> [Arg i x]
  DomainFull (TypedBindings _ (Arg _ TLet{}))         -> []
  DomainFull (TypedBindings _ (Arg i (TBind _ xs _))) -> for xs $ \ (WithHiding h x) ->
    mergeHiding $ WithHiding h $ Arg i x

-- | Replace (Data/Rec/Fun)Sigs with Axioms for postulated names
--   The first argument is a list of axioms only.
replaceSigs
  :: Map Name DataRecOrFun  -- ^ Lone signatures to be turned into Axioms
  -> [NiceDeclaration]      -- ^ Declarations containing them
  -> [NiceDeclaration]      -- ^ In the output, everything should be defined
replaceSigs ps = if Map.null ps then id else \case
  []     -> __IMPOSSIBLE__
  (d:ds) ->
    case replaceable d of
      -- If declaration d of x is mentioned in the map of lone signatures then replace
      -- it with an axiom
      Just (x, axiom) | (Just{}, ps') <- Map.updateLookupWithKey (\ _ _ -> Nothing) x ps
        -> axiom : replaceSigs ps' ds
      _ -> d     : replaceSigs ps  ds

  where

    -- A @replaceable@ declaration is a signature. It has a name and we can make an
    -- @Axiom@ out of it.
    replaceable :: NiceDeclaration -> Maybe (Name, NiceDeclaration)
    replaceable = \case
      FunSig r fx acc abst inst _ argi _ x e ->
        Just (x, Axiom r fx acc abst inst argi Nothing x e)
      NiceRecSig r fx acc abst _ _ x pars t ->
        let e = makePi (lamBindingsToTelescope r pars) t in
        Just (x, Axiom r fx acc abst NotInstanceDef defaultArgInfo Nothing x e)
      NiceDataSig r fx acc abst _ _ x pars t ->
        let e = makePi (lamBindingsToTelescope r pars) t in
        Just (x, Axiom r fx acc abst NotInstanceDef defaultArgInfo Nothing x e)
      _ -> Nothing

-- | Main.
niceDeclarations :: [Declaration] -> Nice [NiceDeclaration]
niceDeclarations ds = do

  -- Get fixity and syntax declarations.
  (fixs, polarities) <- fixitiesAndPolarities ds
  let declared    = Set.fromList (concatMap declaredNames ds)

  -- If we have names in fixity declarations
  -- which are not defined in the appropriate scope,
  -- raise a warning and delete them from fixs.
  fixs <- ifNull (Map.keysSet fixs Set.\\ declared) (return fixs) $ \ unknownFixs -> do
    niceWarning $ UnknownNamesInFixityDecl $ Set.toList unknownFixs
    -- Note: Data.Map.restrictKeys requires containers >= 0.5.8.2
    -- return $ Map.restrictKeys fixs declared
    return $ Map.filterWithKey (\ k _ -> Set.member k declared) fixs

  -- Same for undefined names in polarity declarations.
  polarities <- ifNull (Map.keysSet polarities Set.\\ declared) (return polarities) $
    \ unknownPols -> do
      niceWarning $ UnknownNamesInPolarityPragmas $ Set.toList unknownPols
      -- Note: Data.Map.restrictKeys requires containers >= 0.5.8.2
      -- return $ Map.restrictKeys polarities declared
      return $ Map.filterWithKey (\ k _ -> Set.member k declared) polarities

  -- If we have mixfix identifiers without a corresponding fixity
  -- declaration, we raise a warning
  ifNull (Set.filter isOpenMixfix declared Set.\\ Map.keysSet fixs) (return ()) $
    niceWarning . UnknownFixityInMixfixDecl . Set.toList

  -- Run the nicifier in an initial environment of fixity decls
  -- and polarities.  But keep the warnings.
  st <- get
  put $ initNiceEnv { fixs = fixs, pols = polarities, niceWarn = niceWarn st }
  nds <- nice ds

  -- Check that every polarity pragma was used.
  unlessNullM (Map.keys <$> gets pols) $ \ unusedPolarities -> do
    niceWarning $ PolarityPragmasButNotPostulates unusedPolarities

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

    -- Compute the names defined in a declaration.
    -- We stay in the current scope, i.e., do not go into modules.
    declaredNames :: Declaration -> [Name]
    declaredNames d = case d of
      TypeSig _ x _        -> [x]
      Field _ x _          -> [x]
      FunClause (LHS p [] []) _ _ _
        | IdentP (QName x) <- removeSingletonRawAppP p
                           -> [x]
      FunClause{}          -> []
      DataSig _ _ x _ _    -> [x]
      Data _ _ x _ _ cs    -> x : concatMap declaredNames cs
      RecordSig _ x _ _    -> [x]
      Record _ x _ _ c _ _ _ -> x : foldMap (:[]) (fst <$> c)
      Infix _ _            -> []
      Syntax _ _           -> []
      PatternSyn _ x _ _   -> [x]
      Mutual    _ ds       -> concatMap declaredNames ds
      Abstract  _ ds       -> concatMap declaredNames ds
      Private _ _ ds       -> concatMap declaredNames ds
      InstanceB _ ds       -> concatMap declaredNames ds
      Macro     _ ds       -> concatMap declaredNames ds
      Postulate _ ds       -> concatMap declaredNames ds
      Primitive _ ds       -> concatMap declaredNames ds
      Generalize _ ds      -> concatMap declaredNames ds
      Open{}               -> []
      Import{}             -> []
      ModuleMacro{}        -> []
      Module{}             -> []
      UnquoteDecl _ xs _   -> xs
      UnquoteDef{}         -> []
      -- BUILTIN pragmas which do not require an accompanying definition declare
      -- the (unqualified) name they mention.
      Pragma (BuiltinPragma _ b (QName x) _)
        | b `elem` builtinsNoDef -> [x]
      Pragma{}             -> []

    inferMutualBlocks :: [NiceDeclaration] -> Nice [NiceDeclaration]
    inferMutualBlocks [] = return []
    inferMutualBlocks (d : ds) =
      case declKind d of
        OtherDecl    -> (d :) <$> inferMutualBlocks ds
        LoneDefs{}   -> (d :) <$> inferMutualBlocks ds  -- Andreas, 2017-10-09, issue #2576: report error in ConcreteToAbstract
        LoneSig k x  -> do
          addLoneSig x k
          let tcpc = (pure . terminationCheck) &&& (pure . positivityCheck) $ k
          ((tcs, pcs), (nds0, ds1)) <- untilAllDefined tcpc ds
          -- If we still have lone signatures without any accompanying definition,
          -- we postulate the definition and substitute the axiom for the lone signature
          ps <- use loneSigs
          checkLoneSigs ps
          let ds0 = replaceSigs ps (d : nds0) -- NB: don't forget the LoneSig the block started with!
          -- We then keep processing the rest of the block
          tc <- combineTermChecks (getRange d) tcs
          (NiceMutual (getRange ds0) tc (and pcs) ds0 :) <$> inferMutualBlocks ds1
      where
        untilAllDefined :: ([TerminationCheck], [PositivityCheck])
                        -> [NiceDeclaration]
                        -> Nice (([TerminationCheck], [PositivityCheck]), ([NiceDeclaration], [NiceDeclaration]))
        untilAllDefined tcpc@(tc, pc) ds = do
          done <- noLoneSigs
          if done then return (tcpc, ([], ds)) else
            case ds of
              []     -> return (tcpc, ([], ds))
              d : ds -> case declKind d of
                LoneSig k x -> do
                  addLoneSig x k
                  let tcpc' = (terminationCheck k : tc, positivityCheck k : pc)
                  cons d (untilAllDefined tcpc' ds)
                LoneDefs k xs -> do
                  mapM_ removeLoneSig xs
                  let tcpc' = (terminationCheck k : tc, positivityCheck k : pc)
                  cons d (untilAllDefined tcpc' ds)
                OtherDecl   -> cons d (untilAllDefined tcpc ds)
          where
            -- ASR (26 December 2015): Type annotated version of the @cons@ function.
            -- cons d = fmap $
            --            (id :: (([TerminationCheck], [PositivityCheck]) -> ([TerminationCheck], [PositivityCheck])))
            --            *** (d :)
            --            *** (id :: [NiceDeclaration] -> [NiceDeclaration])
            cons d = fmap (id *** (d :) *** id)

    notMeasure TerminationMeasure{} = False
    notMeasure _ = True

    nice :: [Declaration] -> Nice [NiceDeclaration]
    nice [] = return []
    nice ds = do
      (xs , ys) <- nice1 ds
      (xs ++) <$> nice ys

    nice1 :: [Declaration] -> Nice ([NiceDeclaration], [Declaration])
    nice1 []     = return ([], []) -- Andreas, 2017-09-16, issue #2759: no longer __IMPOSSIBLE__
    nice1 (d:ds) = do
      let justWarning w = do niceWarning w; nice1 ds

      case d of

        (TypeSig info x t)            -> do
          termCheck <- use terminationCheckPragma
          fx <- getFixity x
          let r = getRange d
          -- register x as lone type signature, to recognize clauses later
          addLoneSig x $ FunName termCheck
          return ([FunSig r fx PublicAccess ConcreteDef NotInstanceDef NotMacroDef info termCheck x t] , ds)

        Generalize r [] -> justWarning $ EmptyGeneralize r
        Generalize r sigs -> do
          gs <- forM sigs $ \case
            sig@(TypeSig info x t) -> do
              fx <- getFixity x
              return $ NiceGeneralize (getRange sig) fx PublicAccess info x t
            _ -> __IMPOSSIBLE__
          return (gs, ds)

        (FunClause lhs _ _ _)         -> do
          termCheck <- use terminationCheckPragma
          catchall  <- popCatchallPragma
          xs <- map fst . filter (isFunName . snd) . Map.toList
                <$> use loneSigs
          -- for each type signature 'x' waiting for clauses, we try
          -- if we have some clauses for 'x'
          fixs <- gets fixs
          case [ (x, (fits, rest))
               | x <- xs
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
                d  <- mkFunDef defaultArgInfo termCheck x Nothing [d] -- fun def without type signature is relevant
                return (d , ds)
              -- Subcase: The lhs is a proper pattern.
              -- This could be a let-pattern binding. Pass it on.
              -- A missing type signature error might be raise in ConcreteToAbstract
              _ -> do
                return ([NiceFunClause (getRange d) PublicAccess ConcreteDef termCheck catchall d] , ds)

            -- case: clauses match exactly one of the sigs
            [(x,(fits,rest))] -> do
               removeLoneSig x
               ds  <- expandEllipsis fits
               cs  <- mkClauses x ds False
               fx  <- getFixity x
               return ([FunDef (getRange fits) fits fx ConcreteDef NotInstanceDef termCheck x cs] , rest)

            -- case: clauses match more than one sigs (ambiguity)
            l -> throwError $ AmbiguousFunClauses lhs $ reverse $ map fst l -- "ambiguous function clause; cannot assign it uniquely to one type signature"

        Field{}                       -> (,ds) <$> niceAxioms FieldBlock [ d ]
        DataSig r CoInductive _ _ _   -> throwError (Codata r)
        Data r CoInductive _ _ _ _    -> throwError (Codata r)

        (DataSig r Inductive x tel t) -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          addLoneSig x $ DataName pc uc $ parameters tel
          (,) <$> dataOrRec pc uc DataDef NiceDataSig (niceAxioms DataBlock) r x (Just (tel, t)) Nothing
              <*> return ds

        (Data r Inductive x tel mt cs) -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (DataName pc uc $ parameters tel) x mt
          (,) <$> dataOrRec pc uc DataDef NiceDataSig (niceAxioms DataBlock) r x ((tel,) <$> mt) (Just (tel, cs))
              <*> return ds

        (RecordSig r x tel t)         -> do
          pc <- use positivityCheckPragma
          uc <- use universeCheckPragma
          addLoneSig x $ RecName pc uc $ parameters tel
          fx <- getFixity x
          return ([NiceRecSig r fx PublicAccess ConcreteDef pc uc x tel t] , ds)

        (Record r x i e c tel mt cs)   -> do
          pc <- use positivityCheckPragma
          -- Andreas, 2018-10-27, issue #3327
          -- Propagate {-# NO_UNIVERSE_CHECK #-} pragma from signature to definition.
          -- Universe check is performed if both the current value of
          -- 'universeCheckPragma' AND the one from the signature say so.
          uc <- use universeCheckPragma
          uc <- if uc == NoUniverseCheck then return uc else getUniverseCheckFromSig x
          mt <- defaultTypeSig (RecName pc uc $ parameters tel) x mt
          c <- traverse (\(cname, cinst) -> do fix <- getFixity cname; return (ThingWithFixity cname fix, cinst)) c
          (,) <$> dataOrRec pc uc (\ r f a pc uc x tel cs -> RecDef r f a pc uc x i e c tel cs) NiceRecSig
                    niceDeclarations r x ((tel,) <$> mt) (Just (tel, cs))
              <*> return ds

        Mutual r []  -> justWarning $ EmptyMutual r
        Mutual r ds' ->
          (,ds) <$> (singleton <$> (mkOldMutual r =<< nice ds'))

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
          (,ds) <$> (mapM setPolarity =<< niceAxioms PostulateBlock ds')
          where
          setPolarity (Axiom r f acc a i arg Nothing x e) = do
            mp <- getPolarity x
            return (Axiom r f acc a i arg mp x e)
          setPolarity (Axiom _ _ _ _ _ _ (Just _) _ _) = __IMPOSSIBLE__
          setPolarity d = return d

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
          fx <- getFixity n
          return ([NicePatternSyn r fx n as p] , ds)
        Open r x is         -> return ([NiceOpen r x is] , ds)
        Import r x as op is -> return ([NiceImport r x as op is] , ds)

        UnquoteDecl r xs e -> do
          fxs <- mapM getFixity xs
          tc  <- use terminationCheckPragma
          return ([NiceUnquoteDecl r fxs PublicAccess ConcreteDef NotInstanceDef tc xs e] , ds)

        UnquoteDef r xs e -> do
          fxs  <- mapM getFixity xs
          sigs <- map fst . filter (isFunName . snd) . Map.toList <$> use loneSigs
          let missing = filter (`notElem` sigs) xs
          if null missing
            then do
              mapM_ removeLoneSig xs
              return ([NiceUnquoteDef r fxs PublicAccess ConcreteDef TerminationCheck xs e] , ds)
            else throwError $ UnquoteDefRequiresSignature missing

        Pragma p -> nicePragma p ds

    nicePragma :: Pragma -> [Declaration] -> Nice ([NiceDeclaration], [Declaration])

    nicePragma (TerminationCheckPragma r (TerminationMeasure _ x)) ds =
      if canHaveTerminationMeasure ds then
        withTerminationCheckPragma (TerminationMeasure r x) $ nice1 ds
      else do
        niceWarning $ InvalidTerminationCheckPragma r
        nice1 ds

    nicePragma (TerminationCheckPragma r NoTerminationCheck) ds = do
      -- This PRAGMA has been deprecated in favour of (NON_)TERMINATING
      -- We warn the user about it and then assume the function is NON_TERMINATING.
      niceWarning $ PragmaNoTerminationCheck r
      nicePragma (TerminationCheckPragma r NonTerminating) ds

    nicePragma (TerminationCheckPragma r tc) ds =
      if canHaveTerminationCheckPragma ds then
        withTerminationCheckPragma tc $ nice1 ds
      else do
        niceWarning $ InvalidTerminationCheckPragma r
        nice1 ds

    nicePragma (CatchallPragma r) ds =
      if canHaveCatchallPragma ds then
        withCatchallPragma True $ nice1 ds
      else do
        niceWarning $ InvalidCatchallPragma r
        nice1 ds

    nicePragma (NoPositivityCheckPragma r) ds =
      if canHaveNoPositivityCheckPragma ds then
        withPositivityCheckPragma False $ nice1 ds
      else do
        niceWarning $ InvalidNoPositivityCheckPragma r
        nice1 ds

    nicePragma (NoUniverseCheckPragma r) ds =
      if canHaveNoUniverseCheckPragma ds then
        withUniverseCheckPragma NoUniverseCheck $ nice1 ds
      else do
        niceWarning $ InvalidNoUniverseCheckPragma r
        nice1 ds

    nicePragma (PolarityPragma{}) ds = return ([], ds)

    nicePragma (BuiltinPragma r str qn@(QName x) _) ds = do
      fx <- getFixity x
      return ([NicePragma r (BuiltinPragma r str qn fx)], ds)

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

    canHaveCatchallPragma :: [Declaration] -> Bool
    canHaveCatchallPragma []     = False
    canHaveCatchallPragma (d:ds) = case d of
      FunClause{} -> True
      (Pragma p) | isAttachedPragma p -> canHaveCatchallPragma ds
      _           -> False

    canHaveNoPositivityCheckPragma :: [Declaration] -> Bool
    canHaveNoPositivityCheckPragma []     = False
    canHaveNoPositivityCheckPragma (d:ds) = case d of
      Mutual _ ds                 -> any (canHaveNoPositivityCheckPragma . singleton) ds
      (Data _ Inductive _ _ _ _)  -> True
      (DataSig _ Inductive _ _ _) -> True
      Record{}                    -> True
      RecordSig{}                 -> True
      (Pragma p) | isAttachedPragma p -> canHaveNoPositivityCheckPragma ds
      _                           -> False

    canHaveNoUniverseCheckPragma :: [Declaration] -> Bool
    canHaveNoUniverseCheckPragma []     = False
    canHaveNoUniverseCheckPragma (d:ds) = case d of
      (Data _ Inductive _ _ _ _)  -> True
      (DataSig _ Inductive _ _ _) -> True
      Record{}                    -> True
      RecordSig{}                 -> True
      (Pragma p) | isAttachedPragma p -> canHaveNoPositivityCheckPragma ds
      _                           -> False

    -- Pragma that attaches to the following declaration.
    isAttachedPragma :: Pragma -> Bool
    isAttachedPragma p = case p of
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
        unless (sameKind k k') $ throwError $ WrongDefinition x k' k
        unless (k == k') $ matchParameters x k' k
        Nothing <$ removeLoneSig x

    dataOrRec
      :: forall a
      .  PositivityCheck
      -> UniverseCheck
      -> (Range -> Fixity' -> IsAbstract -> PositivityCheck -> UniverseCheck -> Name -> [LamBinding] -> [NiceConstructor] -> NiceDeclaration)
         -- ^ Construct definition.
      -> (Range -> Fixity' -> Access -> IsAbstract -> PositivityCheck -> UniverseCheck -> Name -> [LamBinding] -> Expr -> NiceDeclaration)
         -- ^ Construct signature.
      -> ([a] -> Nice [NiceDeclaration])
         -- ^ Constructor checking.
      -> Range
      -> Name          -- ^ Data/record type name.
      -> Maybe ([LamBinding], Expr)    -- ^ Parameters and type.  If not @Nothing@ a signature is created.
      -> Maybe ([LamBinding], [a])     -- ^ Parameters and constructors.  If not @Nothing@, a definition body is created.
      -> Nice [NiceDeclaration]
    dataOrRec pc uc mkDef mkSig niceD r x mt mcs = do
      mds <- Trav.forM mcs $ \ (tel, cs) -> (tel,) <$> niceD cs
      f   <- getFixity x
      return $ catMaybes $
        [ mt  <&> \ (tel, t)  -> mkSig (fuseRange x t) f PublicAccess ConcreteDef pc uc x tel t
        , mds <&> \ (tel, ds) -> mkDef r f ConcreteDef pc uc x (caseMaybe mt tel $ const $ concatMap dropType tel) ds
          -- If a type is given (mt /= Nothing), we have to delete the types in @tel@
          -- for the data definition, lest we duplicate them.
        ]
      where
        -- | Drop type annotations and lets from bindings.
        dropType :: LamBinding -> [LamBinding]
        dropType (DomainFull (TypedBindings _r (Arg ai (TBind _ xs _)))) =
          map (mergeHiding . fmap (DomainFree ai)) xs
        dropType (DomainFull (TypedBindings _r (Arg _ TLet{}))) = []
        dropType b@DomainFree{} = [b]

    -- Translate axioms
    niceAxioms :: KindOfBlock -> [TypeSignatureOrInstanceBlock] -> Nice [NiceDeclaration]
    niceAxioms b ds = liftM List.concat $ mapM (niceAxiom b) ds

    niceAxiom :: KindOfBlock -> TypeSignatureOrInstanceBlock -> Nice [NiceDeclaration]
    niceAxiom b d = case d of
      TypeSig rel x t -> do
        fx <- getFixity x
        return [ Axiom (getRange d) fx PublicAccess ConcreteDef NotInstanceDef rel Nothing x t ]
      Field i x argt | b == FieldBlock -> do
        fx <- getFixity x
        return [ NiceField (getRange d) fx PublicAccess ConcreteDef i x argt ]
      InstanceB r decls -> do
        instanceBlock r =<< niceAxioms InstanceBlock decls
      Pragma p@(RewritePragma r _) -> do
        return [ NicePragma r p ]
      _ -> throwError $ WrongContentBlock b $ getRange d

    toPrim :: NiceDeclaration -> NiceDeclaration
    toPrim (Axiom r f p a i rel Nothing x t) = PrimitiveFunction r f p a x t
    toPrim _                               = __IMPOSSIBLE__

    -- Create a function definition.
    mkFunDef info termCheck x mt ds0 = do
      ds <- expandEllipsis ds0
      cs <- mkClauses x ds False
      f  <- getFixity x
      return [ FunSig (fuseRange x t) f PublicAccess ConcreteDef NotInstanceDef NotMacroDef info termCheck x t
             , FunDef (getRange ds0) ds0 f ConcreteDef NotInstanceDef termCheck x cs ]
        where
          t = case mt of
                Just t  -> t
                Nothing -> underscore (getRange x)

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
                ManyHoles -> throwError $ MultipleEllipses p0
                OneHole cxt -> do
                  -- Replace the ellipsis by @p@.
                  let p1 = cxt p
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
      niceWarning $ InvalidCatchallPragma r
      mkClauses x cs True
    mkClauses x (Pragma (CatchallPragma r) : cs) False = do
      when (null cs) $ niceWarning $ InvalidCatchallPragma r
      mkClauses x cs True

    mkClauses x (FunClause lhs rhs wh ca : cs) catchall
      | null (lhsWithExpr lhs) || hasEllipsis lhs  =
      (Clause x (ca || catchall) lhs rhs wh [] :) <$> mkClauses x cs False   -- Will result in an error later.

    mkClauses x (FunClause lhs rhs wh ca : cs) catchall = do
      when (null withClauses) $ throwError $ MissingWithClauses x lhs
      wcs <- mkClauses x withClauses False
      (Clause x (ca || catchall) lhs rhs wh wcs :) <$> mkClauses x cs' False
      where
        (withClauses, cs') = subClauses cs

        -- A clause is a subclause if the number of with-patterns is
        -- greater or equal to the current number of with-patterns plus the
        -- number of with arguments.
        numWith = numberOfWithPatterns p + length es where LHS p _ es = lhs

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

    -- for finding clauses for a type sig in mutual blocks
    couldBeFunClauseOf :: Maybe Fixity' -> Name -> Declaration -> Bool
    couldBeFunClauseOf mFixity x (Pragma (CatchallPragma{})) = True
    couldBeFunClauseOf mFixity x (FunClause (LHS p _ _) _ _ _) = hasEllipsis p ||
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
      case (headMaybe pns, mFixity) of
        -- first identifier in the patterns is the fun.symbol?
        (Just y, _) | x == y -> True -- trace ("couldBe since y = " ++ prettyShow y) $ True
        -- are the parts of x contained in p
        _ | xStrings `isSublistOf` patStrings -> True -- trace ("couldBe since isSublistOf") $ True
        -- looking for a mixfix fun.symb
        (_, Just fix) ->  -- also matches in case of a postfix
           let notStrings = stringParts (theNotation fix)
           in  -- trace ("notStrings = " ++ show notStrings) $
               -- trace ("patStrings = " ++ show patStrings) $
               (not $ null notStrings) && (notStrings `isSublistOf` patStrings)
        -- not a notation, not first id: give up
        _ -> False -- trace ("couldBe not (case default)") $ False
    couldBeFunClauseOf _ _ _ = False -- trace ("couldBe not (fun default)") $ False

    isSingleIdentifierP :: Pattern -> Maybe Name
    isSingleIdentifierP p = case removeSingletonRawAppP p of
      IdentP (QName x) -> Just x
      WildP r          -> Just $ noName r
      _                -> Nothing

    removeSingletonRawAppP :: Pattern -> Pattern
    removeSingletonRawAppP p = case p of
        RawAppP _ [p'] -> removeSingletonRawAppP p'
        ParenP _ p'    -> removeSingletonRawAppP p'
        _ -> p

    -- | Turn an old-style mutual block into a new style mutual block
    --   by pushing the definitions to the end.
    mkOldMutual
      :: Range                -- ^ Range of the whole @mutual@ block.
      -> [NiceDeclaration]    -- ^ Declarations inside the block.
      -> Nice NiceDeclaration -- ^ Returns a 'NiceMutual'.
    mkOldMutual r ds' = do
        -- Postulate the missing definitions
        let ps = Map.fromList loneNames
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
        --        else Nothing <$ niceWarning (NotAllowedInMutual (getRange d) $ declName d)
        -- Sort the declarations in the mutual block.
        -- Declarations of names go to the top.  (Includes module definitions.)
        -- Definitions of names go to the bottom.
        -- Some declarations are forbidden, as their positioning could confuse
        -- the user.
        (top, bottom, invalid) <- forEither3M ds $ \ d -> do
          let top       = return (In1 d)
              bottom    = return (In2 d)
              invalid s = In3 d <$ do niceWarning $ NotAllowedInMutual (getRange d) s
          case d of
            -- Andreas, 2013-11-23 allow postulates in mutual blocks
            Axiom{}             -> top
            NiceField{}         -> top
            PrimitiveFunction{} -> top
            -- Nested mutual blocks should have been flattened by now.
            NiceMutual{}        -> __IMPOSSIBLE__
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
            DataDef{}           -> bottom
            RecDef{}            -> bottom
            -- Andreas, 2018-05-11, issue #3052, allow pat.syn.s in mutual blocks
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

              -- Deprecated compiler pragmas:
              CompiledDataPragma{}      -> bottom
              CompiledTypePragma{}      -> bottom
              CompiledPragma{}          -> bottom
              CompiledExportPragma{}    -> bottom
              CompiledJSPragma{}        -> bottom
              CompiledUHCPragma{}       -> bottom
              CompiledDataUHCPragma{}   -> bottom
              HaskellCodePragma{}       -> bottom

              -- New compiler pragmas:
              ForeignPragma{}           -> bottom
              CompilePragma{}           -> bottom
              StaticPragma{}            -> bottom
              InlinePragma{}            -> bottom
              ImportPragma{}            -> bottom
              ImportUHCPragma{}         -> bottom
              -- End compiler pragmas

              ImpossiblePragma{}        -> top     -- error thrown in scope checker
              EtaPragma{}               -> bottom  -- needs record definition
              WarningOnUsage{}          -> top
              InjectivePragma{}         -> top     -- only needs name, not definition
              DisplayPragma{}           -> top     -- only for printing

              -- The attached pragmas have already been handled at this point.
              CatchallPragma{}          -> __IMPOSSIBLE__
              TerminationCheckPragma{}  -> __IMPOSSIBLE__
              NoPositivityCheckPragma{} -> __IMPOSSIBLE__
              PolarityPragma{}          -> __IMPOSSIBLE__
              NoUniverseCheckPragma{}   -> __IMPOSSIBLE__

        -- -- Pull type signatures to the top
        -- let (sigs, other) = List.partition isTypeSig ds

        -- -- Push definitions to the bottom
        -- let (other, defs) = flip List.partition ds $ \case
        --       FunDef{}         -> False
        --       DataDef{}        -> False
        --       RecDef{}         -> False
        --       NiceFunClause{}  -> False
        --       NicePatternSyn{} -> False
        --       NiceUnquoteDef{} -> False
        --       _ -> True

        -- Compute termination checking flag for mutual block
        tc0 <- use terminationCheckPragma
        let tcs = map termCheck ds
        tc <- combineTermChecks r (tc0:tcs)

        -- Compute positivity checking flag for mutual block
        pc0 <- use positivityCheckPragma
        let pc :: PositivityCheck
            pc = pc0 && all positivityCheckOldMutual ds

        return $ NiceMutual r tc pc $ top ++ bottom
        -- return $ NiceMutual r tc pc $ other ++ defs
        -- return $ NiceMutual r tc pc $ sigs ++ other
      where

        -- isTypeSig Axiom{}                     = True
        -- isTypeSig d | LoneSig{} <- declKind d = True
        -- isTypeSig _                           = False

        sigNames  = [ (x, k) | LoneSig k x <- map declKind ds' ]
        defNames  = [ (x, k) | LoneDefs k xs <- map declKind ds', x <- xs ]
        -- compute the set difference with equality just on names
        loneNames = [ (x, k) | (x, k) <- sigNames, List.all ((x /=) . fst) defNames ]

        -- Andreas, 2013-02-28 (issue 804):
        -- do not termination check a mutual block if any of its
        -- inner declarations comes with a {-# NO_TERMINATION_CHECK #-}
        termCheck (FunSig _ _ _ _ _ _ _ tc _ _)      = tc
        termCheck (FunDef _ _ _ _ _ tc _ _)          = tc
        -- ASR (28 December 2015): Is this equation necessary?
        termCheck (NiceMutual _ tc _ _)              = __IMPOSSIBLE__
        termCheck (NiceUnquoteDecl _ _ _ _ _ tc _ _) = tc
        termCheck (NiceUnquoteDef _ _ _ _ tc _ _)    = tc
        termCheck Axiom{}                            = TerminationCheck
        termCheck NiceField{}                        = TerminationCheck
        termCheck PrimitiveFunction{}                = TerminationCheck
        termCheck NiceModule{}                       = TerminationCheck
        termCheck NiceModuleMacro{}                  = TerminationCheck
        termCheck NiceOpen{}                         = TerminationCheck
        termCheck NiceImport{}                       = TerminationCheck
        termCheck NicePragma{}                       = TerminationCheck
        termCheck NiceRecSig{}                       = TerminationCheck
        termCheck NiceDataSig{}                      = TerminationCheck
        termCheck NiceFunClause{}                    = TerminationCheck
        termCheck DataDef{}                          = TerminationCheck
        termCheck RecDef{}                           = TerminationCheck
        termCheck NicePatternSyn{}                   = TerminationCheck
        termCheck NiceGeneralize{}                   = TerminationCheck

        -- ASR (26 December 2015): Do not positivity check a mutual
        -- block if any of its inner declarations comes with a
        -- NO_POSITIVITY_CHECK pragma. See Issue 1614.
        positivityCheckOldMutual :: NiceDeclaration -> PositivityCheck
        positivityCheckOldMutual (DataDef _ _ _ pc _ _ _ _)    = pc
        positivityCheckOldMutual (NiceDataSig _ _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (NiceMutual _ _ pc _)         = __IMPOSSIBLE__
        positivityCheckOldMutual (NiceRecSig _ _ _ _ pc _ _ _ _) = pc
        positivityCheckOldMutual (RecDef _ _ _ pc _ _ _ _ _ _ _) = pc
        positivityCheckOldMutual _                             = True

        -- A mutual block cannot have a measure,
        -- but it can skip termination check.

    abstractBlock _ [] = return []
    abstractBlock r ds = do
      let (ds', anyChange) = runChange $ mkAbstract ds
          inherited        = r == noRange
      if anyChange then return ds' else do
        -- hack to avoid failing on inherited abstract blocks in where clauses
        unless inherited $ niceWarning $ UselessAbstract r
        return ds -- no change!

    privateBlock _ _ [] = return []
    privateBlock r o ds = do
      let (ds', anyChange) = runChange $ mkPrivate o ds
      if anyChange then return ds' else do
        when (o == UserWritten) $ niceWarning $ UselessPrivate r
        return ds -- no change!

    instanceBlock _ [] = return []
    instanceBlock r ds = do
      let (ds', anyChange) = runChange $ mapM mkInstance ds
      if anyChange then return ds' else do
        niceWarning $ UselessInstance r
        return ds -- no change!

    -- Make a declaration eligible for instance search.
    mkInstance :: Updater NiceDeclaration
    mkInstance d =
      case d of
        Axiom r f p a i rel mp x e       -> (\ i -> Axiom r f p a i rel mp x e) <$> setInstance i
        FunSig r f p a i m rel tc x e    -> (\ i -> FunSig r f p a i m rel tc x e) <$> setInstance i
        NiceUnquoteDecl r f p a i tc x e -> (\ i -> NiceUnquoteDecl r f p a i tc x e) <$> setInstance i
        NiceMutual r termCheck pc ds     -> NiceMutual r termCheck pc <$> mapM mkInstance ds
        NiceFunClause{}                  -> return d
        FunDef r ds f a i tc x cs        -> (\ i -> FunDef r ds f a i tc x cs) <$> setInstance i
        NiceField{}                      -> return d  -- Field instance are handled by the parser
        PrimitiveFunction{}              -> return d
        NiceUnquoteDef{}                 -> return d
        NiceRecSig{}                     -> return d
        NiceDataSig{}                    -> return d
        NiceModuleMacro{}                -> return d
        NiceModule{}                     -> return d
        NicePragma{}                     -> return d
        NiceOpen{}                       -> return d
        NiceImport{}                     -> return d
        DataDef{}                        -> return d
        RecDef{}                         -> return d
        NicePatternSyn{}                 -> return d
        NiceGeneralize{}                 -> return d

    setInstance :: Updater IsInstance
    setInstance i = case i of
      InstanceDef -> return i
      _           -> dirty $ InstanceDef

    macroBlock r ds = mapM mkMacro ds

    mkMacro :: NiceDeclaration -> Nice NiceDeclaration
    mkMacro d =
      case d of
        FunSig r f p a i _ rel tc x e -> return $ FunSig r f p a i MacroDef rel tc x e
        FunDef{}                    -> return d
        _                           -> throwError (BadMacroDef d)

-- | Make a declaration abstract.
--
-- Mark computation as 'dirty' if there was a declaration that could be made abstract.
-- If no abstraction is taking place, we want to complain about 'UselessAbstract'.
--
-- Alternatively, we could only flag 'dirty' if a non-abstract thing was abstracted.
-- Then, nested @abstract@s would sometimes also be complained about.

class MakeAbstract a where
  mkAbstract :: Updater a
  default mkAbstract :: (Traversable f, MakeAbstract a', a ~ f a') => Updater a
  mkAbstract = traverse mkAbstract

instance MakeAbstract a => MakeAbstract [a] where
  -- Default definition kicks in here!
  -- But note that we still have to declare the instance!

-- Leads to overlap with 'WhereClause':
-- instance (Traversable f, MakeAbstract a) => MakeAbstract (f a) where
--   mkAbstract = traverse mkAbstract

instance MakeAbstract IsAbstract where
  mkAbstract a = case a of
    AbstractDef -> return a
    ConcreteDef -> dirty $ AbstractDef

instance MakeAbstract NiceDeclaration where
  mkAbstract d =
    case d of
      NiceMutual r termCheck pc ds     -> NiceMutual r termCheck pc <$> mkAbstract ds
      FunDef r ds f a i tc x cs        -> (\ a -> FunDef r ds f a i tc x) <$> mkAbstract a <*> mkAbstract cs
      DataDef r f a pc uc x ps cs      -> (\ a -> DataDef r f a pc uc x ps) <$> mkAbstract a <*> mkAbstract cs
      RecDef r f a pc uc x i e c ps cs -> (\ a -> RecDef r f a pc uc x i e c ps) <$> mkAbstract a <*> mkAbstract cs
      NiceFunClause r p a termCheck catchall d  -> (\ a -> NiceFunClause r p a termCheck catchall d) <$> mkAbstract a
      -- The following declarations have an @InAbstract@ field
      -- but are not really definitions, so we do count them into
      -- the declarations which can be made abstract
      -- (thus, do not notify progress with @dirty@).
      Axiom r f p a i rel mp x e       -> return $ Axiom             r f p AbstractDef i rel mp x e
      FunSig r f p a i m rel tc x e    -> return $ FunSig            r f p AbstractDef i m rel tc x e
      NiceRecSig r f p a pc uc x ls t  -> return $ NiceRecSig        r f p AbstractDef pc uc x ls t
      NiceDataSig r f p a pc uc x ls t -> return $ NiceDataSig       r f p AbstractDef pc uc x ls t
      NiceField r f p _ i x e          -> return $ NiceField         r f p AbstractDef i x e
      PrimitiveFunction r f p _ x e    -> return $ PrimitiveFunction r f p AbstractDef x e
      -- Andreas, 2016-07-17 it does have effect on unquoted defs.
      -- Need to set updater state to dirty!
      NiceUnquoteDecl r f p _ i t x e  -> dirty $ NiceUnquoteDecl r f p AbstractDef i t x e
      NiceUnquoteDef r f p _ t x e     -> dirty $ NiceUnquoteDef r f p AbstractDef t x e
      NiceModule{}                     -> return d
      NiceModuleMacro{}                -> return d
      NicePragma{}                     -> return d
      NiceOpen{}                       -> return d
      NiceImport{}                     -> return d
      NicePatternSyn{}                 -> return d
      NiceGeneralize{}                 -> return d

instance MakeAbstract Clause where
  mkAbstract (Clause x catchall lhs rhs wh with) = do
    Clause x catchall lhs rhs <$> mkAbstract wh <*> mkAbstract with

-- | Contents of a @where@ clause are abstract if the parent is.
instance MakeAbstract WhereClause where
  mkAbstract  NoWhere           = return $ NoWhere
  mkAbstract (AnyWhere ds)      = dirty $ AnyWhere [Abstract noRange ds]
  mkAbstract (SomeWhere m a ds) = dirty $ SomeWhere m a [Abstract noRange ds]

-- | Make a declaration private.
--
-- Andreas, 2012-11-17:
-- Mark computation as 'dirty' if there was a declaration that could be privatized.
-- If no privatization is taking place, we want to complain about 'UselessPrivate'.
--
-- Alternatively, we could only flag 'dirty' if a non-private thing was privatized.
-- Then, nested @private@s would sometimes also be complained about.

class MakePrivate a where
  mkPrivate :: Origin -> Updater a
  default mkPrivate :: (Traversable f, MakePrivate a', a ~ f a') => Origin -> Updater a
  mkPrivate o = traverse $ mkPrivate o

instance MakePrivate a => MakePrivate [a] where
  -- Default definition kicks in here!
  -- But note that we still have to declare the instance!

-- Leads to overlap with 'WhereClause':
-- instance (Traversable f, MakePrivate a) => MakePrivate (f a) where
--   mkPrivate = traverse mkPrivate

instance MakePrivate Access where
  mkPrivate o p = case p of
    PrivateAccess{} -> return p  -- OR? return $ PrivateAccess o
    _               -> dirty $ PrivateAccess o

instance MakePrivate NiceDeclaration where
  mkPrivate o d =
    case d of
      Axiom r f p a i rel mp x e               -> (\ p -> Axiom r f p a i rel mp x e)               <$> mkPrivate o p
      NiceField r f p a i x e                  -> (\ p -> NiceField r f p a i x e)                  <$> mkPrivate o p
      PrimitiveFunction r f p a x e            -> (\ p -> PrimitiveFunction r f p a x e)            <$> mkPrivate o p
      NiceMutual r termCheck pc ds             -> (\ p -> NiceMutual r termCheck pc p)              <$> mkPrivate o ds
      NiceModule r p a x tel ds                -> (\ p -> NiceModule r p a x tel ds)                <$> mkPrivate o p
      NiceModuleMacro r p x ma op is           -> (\ p -> NiceModuleMacro r p x ma op is)           <$> mkPrivate o p
      FunSig r f p a i m rel tc x e            -> (\ p -> FunSig r f p a i m rel tc x e)            <$> mkPrivate o p
      NiceRecSig r f p a pc uc x ls t          -> (\ p -> NiceRecSig r f p a pc uc x ls t)          <$> mkPrivate o p
      NiceDataSig r f p a pc uc x ls t         -> (\ p -> NiceDataSig r f p a pc uc x ls t)         <$> mkPrivate o p
      NiceFunClause r p a termCheck catchall d -> (\ p -> NiceFunClause r p a termCheck catchall d) <$> mkPrivate o p
      NiceUnquoteDecl r f p a i t x e          -> (\ p -> NiceUnquoteDecl r f p a i t x e)          <$> mkPrivate o p
      NiceUnquoteDef r f p a t x e             -> (\ p -> NiceUnquoteDef r f p a t x e)             <$> mkPrivate o p
      NiceGeneralize r f p i x t               -> (\ p -> NiceGeneralize r f p i x t)               <$> mkPrivate o p
      NicePragma _ _                           -> return $ d
      NiceOpen _ _ _                           -> return $ d
      NiceImport _ _ _ _ _                     -> return $ d
      -- Andreas, 2016-07-08, issue #2089
      -- we need to propagate 'private' to the named where modules
      FunDef r ds f a i tc x cls               -> FunDef r ds f a i tc x <$> mkPrivate o cls
      DataDef{}                                -> return $ d
      RecDef{}                                 -> return $ d
      NicePatternSyn _ _ _ _ _                 -> return $ d

instance MakePrivate Clause where
  mkPrivate o (Clause x catchall lhs rhs wh with) = do
    Clause x catchall lhs rhs <$> mkPrivate o wh <*> mkPrivate o with

instance MakePrivate WhereClause where
  mkPrivate o  NoWhere         = return $ NoWhere
  -- @where@-declarations are protected behind an anonymous module,
  -- thus, they are effectively private by default.
  mkPrivate o (AnyWhere ds)    = return $ AnyWhere ds
  -- Andreas, 2016-07-08
  -- A @where@-module is private if the parent function is private.
  -- The contents of this module are not private, unless declared so!
  -- Thus, we do not recurse into the @ds@ (could not anyway).
  mkPrivate o (SomeWhere m a ds) = mkPrivate o a <&> \ a' -> SomeWhere m a' ds

-- | Add more fixities. Throw an exception for multiple fixity declarations.
--   OR:  Disjoint union of fixity maps.  Throws exception if not disjoint.

plusFixities :: Fixities -> Fixities -> Nice Fixities
plusFixities m1 m2
    -- If maps are not disjoint, report conflicts as exception.
    | not (null isect) = throwError $ MultipleFixityDecls isect
    -- Otherwise, do the union.
    | otherwise        = return $ Map.unionWithKey mergeFixites m1 m2
  where
    --  Merge two fixities, assuming there is no conflict
    mergeFixites name (Fixity' f1 s1 r1) (Fixity' f2 s2 r2) = Fixity' f s $ fuseRange r1 r2
              where f | f1 == noFixity = f2
                      | f2 == noFixity = f1
                      | otherwise = __IMPOSSIBLE__
                    s | s1 == noNotation = s2
                      | s2 == noNotation = s1
                      | otherwise = __IMPOSSIBLE__

    -- Compute a list of conflicts in a format suitable for error reporting.
    isect = [ (x, map (Map.findWithDefault __IMPOSSIBLE__ x) [m1,m2])
            | (x, False) <- Map.assocs $ Map.intersectionWith compatible m1 m2 ]

    -- Check for no conflict.
    compatible (Fixity' f1 s1 _) (Fixity' f2 s2 _) =
      (f1 == noFixity   || f2 == noFixity  ) &&
      (s1 == noNotation || s2 == noNotation)

-- | While 'Fixities' and Polarities are not semigroups under disjoint
--   union (which might fail), we get a semigroup instance for the
--   monadic @Nice (Fixities, Polarities)@ which propagates the first
--   error.
instance Semigroup (Nice (Fixities, Polarities)) where
  c1 <> c2 = do
    (f1, p1) <- c1
    (f2, p2) <- c2
    f <- plusFixities f1 f2
    p <- mergePolarities p1 p2
    return (f, p)
    where
    mergePolarities p1 p2
      | Set.null i = return (Map.union p1 p2)
      | otherwise  = throwError $ MultiplePolarityPragmas (Set.toList i)
      where
      i = Set.intersection (Map.keysSet p1) (Map.keysSet p2)

instance Monoid (Nice (Fixities, Polarities)) where
  mempty  = return (Map.empty, Map.empty)
  mappend = (<>)

-- | Get the fixities and polarity pragmas from the current block.
--   Doesn't go inside modules and where blocks.
--   The reason for this is that these declarations have to appear at the same
--   level (or possibly outside an abstract or mutual block) as their target
--   declaration.
fixitiesAndPolarities :: [Declaration] -> Nice (Fixities, Polarities)
fixitiesAndPolarities = foldMap $ \ d -> case d of
  -- These declarations define polarities:
  Pragma (PolarityPragma _ x occs) -> return (Map.empty, Map.singleton x occs)
  -- These declarations define fixities:
  Syntax x syn    -> return ( Map.singleton x (Fixity' noFixity syn $ getRange x)
                            , Map.empty
                            )
  Infix  f xs     -> return ( Map.fromList $ for xs $ \ x -> (x, Fixity' f noNotation$ getRange x)
                            , Map.empty
                            )
  -- We look into these blocks:
  Mutual    _ ds' -> fixitiesAndPolarities ds'
  Abstract  _ ds' -> fixitiesAndPolarities ds'
  Private _ _ ds' -> fixitiesAndPolarities ds'
  InstanceB _ ds' -> fixitiesAndPolarities ds'
  Macro     _ ds' -> fixitiesAndPolarities ds'
  -- All other declarations are ignored.
  -- We expand these boring cases to trigger a revisit
  -- in case the @Declaration@ type is extended in the future.
  TypeSig     {}  -> mempty
  Generalize  {}  -> mempty
  Field       {}  -> mempty
  FunClause   {}  -> mempty
  DataSig     {}  -> mempty
  Data        {}  -> mempty
  RecordSig   {}  -> mempty
  Record      {}  -> mempty
  PatternSyn  {}  -> mempty
  Postulate   {}  -> mempty
  Primitive   {}  -> mempty
  Open        {}  -> mempty
  Import      {}  -> mempty
  ModuleMacro {}  -> mempty
  Module      {}  -> mempty
  UnquoteDecl {}  -> mempty
  UnquoteDef  {}  -> mempty
  Pragma      {}  -> mempty


-- The following function is (at the time of writing) only used three
-- times: for building Lets, and for printing error messages.

-- | (Approximately) convert a 'NiceDeclaration' back to a list of
-- 'Declaration's.
notSoNiceDeclarations :: NiceDeclaration -> [Declaration]
notSoNiceDeclarations d = fixityDecl d ++
  case d of
    Axiom _ _ _ _ i rel mp x e       -> (case mp of
                                           Nothing   -> []
                                           Just occs -> [Pragma (PolarityPragma noRange x occs)]) ++
                                        inst i [TypeSig rel x e]
    NiceField _ _ _ _ i x argt       -> [Field i x argt]
    PrimitiveFunction r _ _ _ x e    -> [Primitive r [TypeSig defaultArgInfo x e]]
    NiceMutual r _ _ ds              -> [Mutual r $ concatMap notSoNiceDeclarations ds]
    NiceModule r _ _ x tel ds        -> [Module r x tel ds]
    NiceModuleMacro r _ x ma o dir   -> [ModuleMacro r x ma o dir]
    NiceOpen r x dir                 -> [Open r x dir]
    NiceImport r x as o dir          -> [Import r x as o dir]
    NicePragma _ p                   -> [Pragma p]
    NiceRecSig r _ _ _ _ _ x bs e    -> [RecordSig r x bs e]
    NiceDataSig r _ _ _ _ _ x bs e   -> [DataSig r Inductive x bs e]
    NiceFunClause _ _ _ _ _ d        -> [d]
    FunSig _ _ _ _ i _ rel tc x e    -> inst i [TypeSig rel x e]
    FunDef _r ds _ _ _ _ _ _         -> ds
    DataDef r _ _ _ _ x bs cs        -> [Data r Inductive x bs Nothing $ concatMap notSoNiceDeclarations cs]
    RecDef r _ _ _ _ x i e c bs ds   -> [Record r x i e (unThing <$> c) bs Nothing $ concatMap notSoNiceDeclarations ds]
      where unThing (ThingWithFixity c _, inst) = (c, inst)
    NicePatternSyn r _ n as p        -> [PatternSyn r n as p]
    NiceGeneralize r _ _ i n e       -> [Generalize r [TypeSig i n e]]
    NiceUnquoteDecl r _ _ _ i _ x e  -> inst i [UnquoteDecl r x e]
    NiceUnquoteDef r _ _ _ _ x e     -> [UnquoteDef r x e]
  where
    inst InstanceDef    ds = [InstanceB (getRange ds) ds]
    inst NotInstanceDef ds = ds

    fixityDecl d = nameAndFixity >>= \ (x, f) -> infixDecl (theFixity f) x ++ syntaxDecl (theNotation f) x
      where
        nameAndFixity = case d of
          Axiom _ f _ _ _ _ _ x _           -> [(x, f)]
          NiceField _ f _ _ _ x _           -> [(x, f)]
          PrimitiveFunction _ f _ _ x _     -> [(x, f)]
          NiceRecSig _ f _ _ _ _ x _ _      -> [(x, f)]
          NiceDataSig _ f _ _ _ _ x _ _     -> [(x, f)]
          FunSig _ f _ _ _ _ _ _ x _        -> [(x, f)]
          NicePatternSyn _ f x _ _          -> [(x, f)]
          NiceGeneralize _ f _ _ x _        -> [(x, f)]
          NiceUnquoteDecl _ fs _ _ _ _ xs _ -> zip xs fs
          NiceUnquoteDef _ fs _ _ _ xs _    -> zip xs fs
          NiceMutual{}      -> []
          NiceModule{}      -> []
          NiceModuleMacro{} -> []
          NiceOpen{}        -> []
          NiceImport{}      -> []
          NicePragma{}      -> []
          NiceFunClause{}   -> []
          FunDef{}          -> []  -- use the fixity from the FunSig/DataSig/RecSig
          DataDef{}         -> []
          RecDef{}          -> []

    infixDecl  f x = [Infix f [x] | notElem f [defaultFixity, noFixity]]
    syntaxDecl n x = [Syntax x n  | not (null n) ]

-- | Has the 'NiceDeclaration' a field of type 'IsAbstract'?
niceHasAbstract :: NiceDeclaration -> Maybe IsAbstract
niceHasAbstract d =
  case d of
    Axiom{}                         -> Nothing
    NiceField _ _ _ a _ _ _         -> Just a
    PrimitiveFunction _ _ _ a _ _   -> Just a
    NiceMutual{}                    -> Nothing
    NiceModule _ _ a _ _ _          -> Just a
    NiceModuleMacro{}               -> Nothing
    NiceOpen{}                      -> Nothing
    NiceImport{}                    -> Nothing
    NicePragma{}                    -> Nothing
    NiceRecSig{}                    -> Nothing
    NiceDataSig{}                   -> Nothing
    NiceFunClause _ _ a _ _ _       -> Just a
    FunSig{}                        -> Nothing
    FunDef _ _ _ a _ _ _ _          -> Just a
    DataDef _ _ a _ _ _ _ _         -> Just a
    RecDef _ _ a _ _ _ _ _ _ _ _    -> Just a
    NicePatternSyn{}                -> Nothing
    NiceGeneralize{}                -> Nothing
    NiceUnquoteDecl _ _ _ a _ _ _ _ -> Just a
    NiceUnquoteDef _ _ _ a _ _ _    -> Just a
