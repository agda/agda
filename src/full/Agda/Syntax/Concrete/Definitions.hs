{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
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
--   * Report basic well-formedness error,
--     when one of the above transformation fails.

module Agda.Syntax.Concrete.Definitions
    ( NiceDeclaration(..)
    , NiceConstructor, NiceTypeSignature
    , Clause(..)
    , DeclarationException(..)
    , Nice, runNice
    , niceDeclarations
    , notSoNiceDeclarations
    , niceHasAbstract
    , Measure
    ) where

import Prelude hiding (null)

import Control.Arrow ((***))
import Control.Applicative hiding (empty)
import Control.Monad.State

#if __GLASGOW_HASKELL__ <= 708
import Data.Foldable ( foldMap )
#endif

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Semigroup ( Semigroup, Monoid, (<>), mempty, mappend )
import Data.List as List hiding (null)
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse)
import qualified Data.Traversable as Trav

import Data.Data (Data)
import Data.Typeable (Typeable)

import Agda.Syntax.Concrete
import Agda.Syntax.Common hiding (TerminationCheck())
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete.Pretty ()

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Except ( MonadError(throwError) )
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
  | NiceRecSig Range Fixity' Access IsAbstract PositivityCheck Name [LamBinding] Expr
  | NiceDataSig Range Fixity' Access IsAbstract PositivityCheck Name [LamBinding] Expr
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
  | DataDef Range Fixity' IsAbstract PositivityCheck Name [LamBinding] [NiceConstructor]
  | RecDef Range Fixity' IsAbstract PositivityCheck Name (Maybe (Ranged Induction)) (Maybe Bool) (Maybe (ThingWithFixity Name, IsInstance)) [LamBinding] [NiceDeclaration]
  | NicePatternSyn Range Fixity' Name [Arg Name] Pattern
  | NiceUnquoteDecl Range [Fixity'] Access IsAbstract IsInstance TerminationCheck [Name] Expr
  | NiceUnquoteDef Range [Fixity'] Access IsAbstract TerminationCheck [Name] Expr
  deriving (Typeable, Data, Show)

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
    deriving (Typeable, Data, Show)

-- | The exception type.
data DeclarationException
        = MultipleFixityDecls [(Name, [Fixity'])]
        | MultiplePolarityPragmas [Name]
        | InvalidName Name
        | DuplicateDefinition Name
        | MissingDefinition Name
        | MissingWithClauses Name
        | MissingTypeSignature LHS -- Andreas 2012-06-02: currently unused, remove after a while -- Fredrik 2012-09-20: now used, can we keep it?
        | MissingDataSignature Name
        | WrongDefinition Name DataRecOrFun DataRecOrFun
        | WrongParameters Name Params Params
          -- ^ 'Name' of symbol, 'Params' of signature, 'Params' of definition.
        | NotAllowedInMutual NiceDeclaration
        | UnknownNamesInFixityDecl [Name]
        | UnknownNamesInPolarityPragmas [Name]
        | PolarityPragmasButNotPostulates [Name]
        | Codata Range
        | DeclarationPanic String
        | UselessPrivate Range
        | UselessAbstract Range
        | UselessInstance Range
        | WrongContentBlock KindOfBlock Range
        | AmbiguousFunClauses LHS [Name] -- ^ in a mutual block, a clause could belong to any of the @[Name]@ type signatures
        | InvalidTerminationCheckPragma Range
        | InvalidMeasureMutual Range
          -- ^ In a mutual block, all or none need a MEASURE pragma.
          --   Range is of mutual block.
        | PragmaNoTerminationCheck Range
          -- ^ Pragma @{-# NO_TERMINATION_CHECK #-}@ has been replaced
          --   by {-# TERMINATING #-} and {-# NON_TERMINATING #-}.
        | InvalidCatchallPragma Range
        | UnquoteDefRequiresSignature [Name]
        | BadMacroDef NiceDeclaration
        | InvalidNoPositivityCheckPragma Range

    deriving (Typeable, Data)

-- | Several declarations expect only type signatures as sub-declarations.  These are:
data KindOfBlock
  = PostulateBlock  -- ^ @postulate@
  | PrimitiveBlock  -- ^ @primitive@.  Ensured by parser.
  | InstanceBlock   -- ^ @instance@.  Actually, here all kinds of sub-declarations are allowed a priori.
  | FieldBlock      -- ^ @field@.  Ensured by parser.
  | DataBlock       -- ^ @data ... where@.  Here we got a bad error message for Agda-2.5 (Issue 1698).
  deriving (Typeable, Data, Eq, Ord, Show)


instance HasRange DeclarationException where
  getRange (MultipleFixityDecls xs)             = getRange (fst $ head xs)
  getRange (MultiplePolarityPragmas xs)         = getRange (head xs)
  getRange (InvalidName x)                      = getRange x
  getRange (DuplicateDefinition x)              = getRange x
  getRange (MissingDefinition x)                = getRange x
  getRange (MissingWithClauses x)               = getRange x
  getRange (MissingTypeSignature x)             = getRange x
  getRange (MissingDataSignature x)             = getRange x
  getRange (WrongDefinition x k k')             = getRange x
  getRange (WrongParameters x _ _)              = getRange x
  getRange (AmbiguousFunClauses lhs xs)         = getRange lhs
  getRange (NotAllowedInMutual x)               = getRange x
  getRange (UnknownNamesInFixityDecl xs)        = getRange . head $ xs
  getRange (UnknownNamesInPolarityPragmas xs)   = getRange . head $ xs
  getRange (PolarityPragmasButNotPostulates xs) = getRange . head $ xs
  getRange (Codata r)                           = r
  getRange (DeclarationPanic _)                 = noRange
  getRange (UselessPrivate r)                   = r
  getRange (UselessAbstract r)                  = r
  getRange (UselessInstance r)                  = r
  getRange (WrongContentBlock _ r)              = r
  getRange (InvalidTerminationCheckPragma r)    = r
  getRange (InvalidMeasureMutual r)             = r
  getRange (PragmaNoTerminationCheck r)         = r
  getRange (InvalidCatchallPragma r)            = r
  getRange (UnquoteDefRequiresSignature x)      = getRange x
  getRange (BadMacroDef d)                      = getRange d
  getRange (InvalidNoPositivityCheckPragma r)   = r

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
  getRange (DataDef r _ _ _ _ _ _)           = r
  getRange (RecDef r _ _ _ _ _ _ _ _ _)      = r
  getRange (NiceRecSig r _ _ _ _ _ _ _)      = r
  getRange (NiceDataSig r _ _ _ _ _ _ _)     = r
  getRange (NicePatternSyn r _ _ _ _)        = r
  getRange (NiceFunClause r _ _ _ _ _)       = r
  getRange (NiceUnquoteDecl r _ _ _ _ _ _ _) = r
  getRange (NiceUnquoteDef r _ _ _ _ _ _)    = r

-- These error messages can (should) be terminated by a dot ".",
-- there is no error context printed after them.
instance Pretty DeclarationException where
  pretty (MultipleFixityDecls xs) =
    sep [ fsep $ pwords "Multiple fixity or syntax declarations for"
        , vcat $ map f xs
        ]
      where
        f (x, fs) = pretty x Pretty.<> text ": " <+> fsep (map pretty fs)
  pretty (MultiplePolarityPragmas xs) = fsep $
    pwords "Multiple polarity pragmas for" ++ map pretty xs
  pretty (InvalidName x) = fsep $
    pwords "Invalid name:" ++ [pretty x]
  pretty (DuplicateDefinition x) = fsep $
    pwords "Duplicate definition of" ++ [pretty x]
  pretty (MissingDefinition x) = fsep $
    pwords "Missing definition for" ++ [pretty x]
  pretty (MissingWithClauses x) = fsep $
    pwords "Missing with-clauses for function" ++ [pretty x]
  pretty (MissingTypeSignature x) = fsep $
    pwords "Missing type signature for left hand side" ++ [pretty x]
  pretty (MissingDataSignature x) = fsep $
    pwords "Missing type signature for " ++ [pretty x]
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
  pretty (UnknownNamesInFixityDecl xs) = fsep $
    pwords "The following names are not declared in the same scope as their syntax or fixity declaration (i.e., either not in scope at all, imported from another module, or declared in a super module):" ++ map pretty xs
  pretty (UnknownNamesInPolarityPragmas xs) = fsep $
    pwords "The following names are not declared in the same scope as their polarity pragmas (they could for instance be out of scope, imported from another module, or declared in a super module):" ++ map pretty xs
  pretty (PolarityPragmasButNotPostulates xs) = fsep $
    pwords "Polarity pragmas have been given for the following identifiers which are not postulates:" ++ map pretty xs
  pretty (UselessPrivate _)      = fsep $
    pwords "Using private here has no effect. Private applies only to declarations that introduce new identifiers into the module, like type signatures and data, record, and module declarations."
  pretty (UselessAbstract _)      = fsep $
    pwords "Using abstract here has no effect. Abstract applies only definitions like data definitions, record type definitions and function clauses."
  pretty (UselessInstance _)      = fsep $
    pwords "Using instance here has no effect. Instance applies only to declarations that introduce new identifiers into the module, like type signatures and axioms."
  pretty (WrongContentBlock b _)      = fsep . pwords $
    case b of
      PostulateBlock -> "A postulate block can only contain type signatures, possibly under keyword instance"
      DataBlock -> "A data definition can only contain type signatures, possibly under keyword instance"
      _ -> "Unexpected declaration"
  pretty (PragmaNoTerminationCheck _) = fsep $
    pwords "Pragma {-# NO_TERMINATION_CHECK #-} has been removed.  To skip the termination check, label your definitions either as {-# TERMINATING #-} or {-# NON_TERMINATING #-}."
  pretty (InvalidTerminationCheckPragma _) = fsep $
    pwords "Termination checking pragmas can only precede a mutual block or a function definition."
  pretty (InvalidMeasureMutual _) = fsep $
    pwords "In a mutual block, either all functions must have the same (or no) termination checking pragma."
  pretty (InvalidCatchallPragma _) = fsep $
    pwords "The CATCHALL pragma can only preceed a function clause."
  pretty (UnquoteDefRequiresSignature xs) = fsep $
    pwords "Missing type signatures for unquoteDef" ++ map pretty xs
  pretty (BadMacroDef nd) = fsep $
    [text $ declName nd] ++ pwords "are not allowed in macro blocks"
  pretty (NotAllowedInMutual nd) = fsep $
    [text $ declName nd] ++ pwords "are not allowed in mutual blocks"
  pretty (Codata _) = text $
    "The codata construction has been removed. " ++
    "Use the INFINITY builtin instead."
  pretty (DeclarationPanic s) = text s
  pretty (InvalidNoPositivityCheckPragma _) = fsep $
    pwords "No positivity checking pragmas can only precede a mutual block or a data/record definition."

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

data DataRecOrFun
  = DataName { kindPosCheck :: PositivityCheck, kindParams :: Params }
    -- ^ Name of a data type with parameters.
  | RecName  { kindPosCheck :: PositivityCheck, kindParams :: Params }
    -- ^ Name of a record type with parameters.
  | FunName  TerminationCheck
    -- ^ Name of a function.
  deriving (Typeable, Data)

-- Ignore pragmas when checking equality
instance Eq DataRecOrFun where
  DataName _ p == DataName _ q = p == q
  RecName  _ p == RecName  _ q = p == q
  FunName  _   == FunName  _   = True
  _            == _            = False

type Params = [Arg BoundName]

instance Show DataRecOrFun where
  show (DataName _ n) = "data type" --  "with " ++ show n ++ " visible parameters"
  show (RecName _ n)  = "record type" -- "with " ++ show n ++ " visible parameters"
  show (FunName{})    = "function"

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
terminationCheck _            = TerminationCheck

positivityCheck :: DataRecOrFun -> PositivityCheck
positivityCheck (DataName pc _) = pc
positivityCheck (RecName pc _)  = pc
positivityCheck _               = True

-- | Check that declarations in a mutual block are consistently
--   equipped with MEASURE pragmas, or whether there is a
--   NO_TERMINATION_CHECK pragma.
combineTermChecks :: Range -> [TerminationCheck] -> Nice TerminationCheck
combineTermChecks r tcs = loop tcs where
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

type Nice = StateT NiceEnv (Either DeclarationException)

-- | Nicifier state.

data NiceEnv = NiceEnv
  { _loneSigs :: LoneSigs
    -- ^ Lone type signatures that wait for their definition.
  , _termChk  :: TerminationCheck
    -- ^ Termination checking pragma waiting for a definition.
  , _posChk   :: PositivityCheck
    -- ^ Positivity checking pragma waiting for a definition.
  , _catchall :: Catchall
    -- ^ Catchall pragma waiting for a function clause.
  , fixs     :: Fixities
  , pols     :: Polarities
  }

type LoneSigs   = Map Name DataRecOrFun
type Fixities   = Map Name Fixity'
type Polarities = Map Name [Occurrence]

-- | Initial nicifier state.

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { _loneSigs = empty
  , _termChk  = TerminationCheck
  , _posChk   = True
  , _catchall = False
  , fixs      = empty
  , pols      = empty
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

checkLoneSigs :: [(Name, a)] -> Nice ()
checkLoneSigs xs =
  case xs of
    []       -> return ()
    (x, _):_ -> throwError $ MissingDefinition x

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

runNice :: Nice a -> Either DeclarationException a
runNice nice = nice `evalStateT` initNiceEnv

data DeclKind
    = LoneSig DataRecOrFun Name
    | LoneDefs DataRecOrFun [Name]
    | OtherDecl
  deriving (Eq, Show)

declKind :: NiceDeclaration -> DeclKind
declKind (FunSig _ _ _ _ _ _ _ tc x _)    = LoneSig (FunName tc) x
declKind (NiceRecSig _ _ _ _ pc x pars _) = LoneSig (RecName pc $ parameters pars) x
declKind (NiceDataSig _ _ _ _ pc x pars _)= LoneSig (DataName pc $ parameters pars) x
declKind (FunDef _ _ _ _ _ tc x _)        = LoneDefs (FunName tc) [x]
declKind (DataDef _ _ _ pc x pars _)      = LoneDefs (DataName pc $ parameters pars) [x]
declKind (RecDef _ _ _ pc x _ _ _ pars _) = LoneDefs (RecName pc $ parameters pars) [x]
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
declKind NiceUnquoteDecl{}                = OtherDecl

-- | Compute parameters of a data or record signature or definition.
parameters :: [LamBinding] -> Params
parameters = List.concatMap $ \case
  DomainFree i x                                      -> [Arg i x]
  DomainFull (TypedBindings _ (Arg _ TLet{}))         -> []
  DomainFull (TypedBindings _ (Arg i (TBind _ xs _))) -> for xs $ \ (WithHiding h x) ->
    mergeHiding $ WithHiding h $ Arg i x

-- | Main.
niceDeclarations :: [Declaration] -> Nice [NiceDeclaration]
niceDeclarations ds = do
  -- Get fixity and syntax declarations.
  (fixs, polarities) <- fixitiesAndPolarities ds
  let declared    = Set.fromList (concatMap declaredNames ds)
      unknownFixs = Map.keysSet fixs       Set.\\ declared
      unknownPols = Map.keysSet polarities Set.\\ declared
  case (Set.null unknownFixs, Set.null unknownPols) of
    -- If we have fixity/syntax decls for names not declared
    -- in the current scope, fail.
    (False, _)   -> throwError $ UnknownNamesInFixityDecl
                                   (Set.toList unknownFixs)
    -- Fail if there are polarity pragmas with undeclared names.
    (_, False)   -> throwError $ UnknownNamesInPolarityPragmas
                                   (Set.toList unknownPols)
    (True, True) -> localState $ do
      -- Run the nicifier in an initial environment of fixity decls
      -- and polarities.
      put $ initNiceEnv { fixs = fixs, pols = polarities }
      ds <- nice ds
      -- Check that every polarity pragma was used.
      unusedPolarities <- gets (Map.keys . pols)
      unless (null unusedPolarities) $ do
        throwError $ PolarityPragmasButNotPostulates unusedPolarities
      -- Check that every signature got its definition.
      checkLoneSigs . Map.toList =<< use loneSigs
      -- Note that loneSigs is ensured to be empty.
      -- (Important, since inferMutualBlocks also uses loneSigs state).
      inferMutualBlocks ds
  where
    -- Compute the names defined in a declaration.
    -- We stay in the current scope, i.e., do not go into modules.
    declaredNames :: Declaration -> [Name]
    declaredNames d = case d of
      TypeSig _ x _        -> [x]
      Field _ x _          -> [x]
      FunClause (LHS p [] [] []) _ _ _
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
      Open{}               -> []
      Import{}             -> []
      ModuleMacro{}        -> []
      Module{}             -> []
      UnquoteDecl _ xs _   -> xs
      UnquoteDef{}         -> []
      Pragma{}             -> []

    inferMutualBlocks :: [NiceDeclaration] -> Nice [NiceDeclaration]
    inferMutualBlocks [] = return []
    inferMutualBlocks (d : ds) =
      case declKind d of
        OtherDecl    -> (d :) <$> inferMutualBlocks ds
        LoneDefs _ xs -> __IMPOSSIBLE__
        LoneSig k x  -> do
          addLoneSig x k
          ((tcs, pcs), (ds0, ds1)) <- untilAllDefined ([terminationCheck k], [positivityCheck k]) ds
          tc <- combineTermChecks (getRange d) tcs

          -- Record modules are, for performance reasons, not always
          -- placed in mutual blocks.

          -- ASR (01 January 2016): If the record module has a
          -- NO_POSITIVITY_CHECK pragma, it is placed in a mutual
          -- block. See Issue 1760.
          let prefix :: [NiceDeclaration] -> [NiceDeclaration]
              prefix = case (d, ds0) of
                (NiceRecSig{}, [r@(RecDef _ _ _ True _ _ _ _ _ _)]) -> ([d, r] ++)
                _                                                   ->
                  (NiceMutual (getRange (d : ds0)) tc (and pcs) (d : ds0) :)

          prefix <$> inferMutualBlocks ds1
      where
        untilAllDefined :: ([TerminationCheck], [PositivityCheck])
                        -> [NiceDeclaration]
                        -> Nice (([TerminationCheck], [PositivityCheck]), ([NiceDeclaration], [NiceDeclaration]))
        untilAllDefined (tc, pc) ds = do
          done <- noLoneSigs
          if done then return ((tc, pc), ([], ds)) else
            case ds of
              []     -> __IMPOSSIBLE__ <$ (checkLoneSigs . Map.toList =<< use loneSigs)
              d : ds -> case declKind d of
                LoneSig k x ->
                  addLoneSig x k >> cons d (untilAllDefined (terminationCheck k : tc, positivityCheck k : pc) ds)
                LoneDefs k xs -> do
                  mapM_ removeLoneSig xs
                  cons d (untilAllDefined (terminationCheck k : tc, positivityCheck k : pc) ds)
                OtherDecl   -> cons d (untilAllDefined (tc, pc) ds)
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
    nice1 []     = __IMPOSSIBLE__
    nice1 (d:ds) = case d of

        (TypeSig info x t)            -> do
          termCheck <- use terminationCheckPragma
          fx <- getFixity x
          -- register x as lone type signature, to recognize clauses later
          addLoneSig x (FunName termCheck)
          return ([FunSig (getRange d) fx PublicAccess ConcreteDef NotInstanceDef NotMacroDef info termCheck x t] , ds)

        (FunClause lhs _ _ _)         -> do
          termCheck <- use terminationCheckPragma
          catchall  <- popCatchallPragma
          xs <- map fst . filter (isFunName . snd) . Map.toList <$> use loneSigs
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
              LHS p [] [] [] | Just x <- isSingleIdentifierP p -> do
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
               cs  <- mkClauses x (expandEllipsis fits) False
               fx  <- getFixity x
               return ([FunDef (getRange fits) fits fx ConcreteDef NotInstanceDef termCheck x cs] , rest)

            -- case: clauses match more than one sigs (ambiguity)
            l -> throwError $ AmbiguousFunClauses lhs $ reverse $ map fst l -- "ambiguous function clause; cannot assign it uniquely to one type signature"

        Field{}                       -> (,ds) <$> niceAxioms FieldBlock [ d ]
        DataSig r CoInductive _ _ _   -> throwError (Codata r)
        Data r CoInductive _ _ _ _    -> throwError (Codata r)

        (DataSig r Inductive x tel t) -> do
          pc <- use positivityCheckPragma
          addLoneSig x (DataName pc $ parameters tel)
          (,) <$> dataOrRec pc DataDef NiceDataSig (niceAxioms DataBlock) r x (Just (tel, t)) Nothing
              <*> return ds

        (Data r Inductive x tel mt cs) -> do
          pc <- use positivityCheckPragma
          mt <- defaultTypeSig (DataName pc $ parameters tel) x mt
          (,) <$> dataOrRec pc DataDef NiceDataSig (niceAxioms DataBlock) r x ((tel,) <$> mt) (Just (tel, cs))
              <*> return ds

        (RecordSig r x tel t)         -> do
          pc <- use positivityCheckPragma
          addLoneSig x (RecName pc $ parameters tel)
          fx <- getFixity x
          return ([NiceRecSig r fx PublicAccess ConcreteDef pc x tel t] , ds)

        (Record r x i e c tel mt cs)   -> do
          pc <- use positivityCheckPragma
          mt <- defaultTypeSig (RecName pc $ parameters tel) x mt
          c <- traverse (\(cname, cinst) -> do fix <- getFixity cname; return (ThingWithFixity cname fix, cinst)) c
          (,) <$> dataOrRec pc (\ r f a pc x tel cs -> RecDef r f a pc x i e c tel cs) NiceRecSig
                    niceDeclarations r x ((tel,) <$> mt) (Just (tel, cs))
              <*> return ds

        Mutual r ds' ->
          (,ds) <$> (singleton <$> (mkOldMutual r =<< nice ds'))

        Abstract r ds' ->
          (,ds) <$> (abstractBlock r =<< nice ds')

        Private r o ds' ->
          (,ds) <$> (privateBlock r o =<< nice ds')

        InstanceB r ds' ->
          (,ds) <$> (instanceBlock r =<< nice ds')

        Macro r ds' ->
          (,ds) <$> (macroBlock r =<< nice ds')

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
      else
        throwError $ InvalidTerminationCheckPragma r

    nicePragma (TerminationCheckPragma r NoTerminationCheck) ds =
      throwError $ PragmaNoTerminationCheck r

    nicePragma (TerminationCheckPragma r tc) ds =
      if canHaveTerminationCheckPragma ds then
        withTerminationCheckPragma tc $ nice1 ds
      else
        throwError $ InvalidTerminationCheckPragma r

    nicePragma (CatchallPragma r) ds =
      if canHaveCatchallPragma ds then
        withCatchallPragma True $ nice1 ds
      else
        throwError $ InvalidCatchallPragma r

    nicePragma (NoPositivityCheckPragma r) ds =
      if canHaveNoPositivityCheckPragma ds then
        withPositivityCheckPragma False $ nice1 ds
      else
        throwError $ InvalidNoPositivityCheckPragma r

    nicePragma (PolarityPragma{}) ds = return ([], ds)

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
      Mutual{}      -> True
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
      Mutual{}                    -> True
      (Data _ Inductive _ _ _ _)  -> True
      (DataSig _ Inductive _ _ _) -> True
      Record{}                    -> True
      RecordSig{}                 -> True
      (Pragma p) | isAttachedPragma p -> canHaveNoPositivityCheckPragma ds
      _                           -> False

    isAttachedPragma :: Pragma -> Bool
    isAttachedPragma p = case p of
      TerminationCheckPragma{}  -> True
      CatchallPragma{}          -> True
      NoPositivityCheckPragma{} -> True
      _                         -> False

    -- We could add a default type signature here, but at the moment we can't
    -- infer the type of a record or datatype, so better to just fail here.
    defaultTypeSig :: DataRecOrFun -> Name -> Maybe Expr -> Nice (Maybe Expr)
    defaultTypeSig k x t@Just{} = return t
    defaultTypeSig k x Nothing  = do
      caseMaybeM (getSig x) (throwError $ MissingDataSignature x) $ \ k' -> do
        unless (sameKind k k') $ throwError $ WrongDefinition x k' k
        unless (k == k') $ matchParameters x k' k
        Nothing <$ removeLoneSig x

    dataOrRec
      :: forall a
      .  PositivityCheck
      -> (Range -> Fixity' -> IsAbstract -> PositivityCheck -> Name -> [LamBinding] -> [NiceConstructor] -> NiceDeclaration)
         -- ^ Construct definition.
      -> (Range -> Fixity' -> Access -> IsAbstract -> PositivityCheck -> Name -> [LamBinding] -> Expr -> NiceDeclaration)
         -- ^ Construct signature.
      -> ([a] -> Nice [NiceDeclaration])
         -- ^ Constructor checking.
      -> Range
      -> Name          -- ^ Data/record type name.
      -> Maybe ([LamBinding], Expr)    -- ^ Parameters and type.  If not @Nothing@ a signature is created.
      -> Maybe ([LamBinding], [a])     -- ^ Parameters and constructors.  If not @Nothing@, a definition body is created.
      -> Nice [NiceDeclaration]
    dataOrRec pc mkDef mkSig niceD r x mt mcs = do
      mds <- Trav.forM mcs $ \ (tel, cs) -> (tel,) <$> niceD cs
      f   <- getFixity x
      return $ catMaybes $
        [ mt  <&> \ (tel, t)  -> mkSig (fuseRange x t) f PublicAccess ConcreteDef pc x tel t
        , mds <&> \ (tel, ds) -> mkDef r f ConcreteDef pc x (caseMaybe mt tel $ const $ concatMap dropType tel) ds
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
      Field i x argt -> do
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
      cs <- mkClauses x (expandEllipsis ds0) False
      f  <- getFixity x
      return [ FunSig (fuseRange x t) f PublicAccess ConcreteDef NotInstanceDef NotMacroDef info termCheck x t
             , FunDef (getRange ds0) ds0 f ConcreteDef NotInstanceDef termCheck x cs ]
        where
          t = case mt of
                Just t  -> t
                Nothing -> underscore (getRange x)

    underscore r = Underscore r Nothing


    expandEllipsis :: [Declaration] -> [Declaration]
    expandEllipsis [] = []
    expandEllipsis (d@(FunClause Ellipsis{} _ _ _) : ds) =
      d : expandEllipsis ds
    expandEllipsis (d@(FunClause lhs@(LHS p ps _ _) _ _ _) : ds) =
      d : expand (wipe p) (map wipe ps) ds
      where
        expand _ _ [] = []
        expand p ps (d@(Pragma (CatchallPragma r)) : ds) = d : expand p ps ds
        expand p ps (FunClause (Ellipsis r ps' eqs es) rhs wh ca : ds) =
          FunClause (LHS (setRange r p) ((setRange r ps) ++ ps') eqs es) rhs wh ca
            : expand p (applyUnless (null es) (++ (map wipe ps')) ps) ds
                       -- If we have with-expressions (es /= []) then the following
                       -- ellipses also get the additional with patterns ps'
        -- We can have ellipses after a fun clause.
        -- They refer to the last clause that introduced new with-expressions.
        expand p ps (d@(FunClause (LHS _ _ _ []) _ _ _) : ds) =
          d : expand p ps ds
        -- Same here: Ff we have new with-expressions, the next ellipses will
        -- refer to us.
        expand _ _ (d@(FunClause (LHS p' ps' _ (_ : _)) _ _ _) : ds) =
          d : expand (wipe p') (map wipe ps') ds
          -- Andreas, Jesper, 2017-05-13, issue #2578
          -- Need to update the range also on the next with-patterns.
        expand _ _ (_ : ds) = __IMPOSSIBLE__
    expandEllipsis (_ : ds) = __IMPOSSIBLE__

    -- Before copying a pattern, remove traces to its origin.
    wipe :: Pattern -> Pattern
    wipe = killRange . setInserted

    setInserted :: Pattern -> Pattern
    setInserted p = case p of
      IdentP{} -> p
      QuoteP{} -> p
      AppP p q -> AppP (setInserted p) (fmap (fmap setInserted) q)
      RawAppP r ps -> RawAppP r (map setInserted ps)
      OpAppP r c ns ps -> OpAppP r c ns (map (fmap $ fmap setInserted) ps)
      HiddenP r p -> HiddenP r (fmap setInserted p)
      InstanceP r p -> InstanceP r (fmap setInserted p)
      ParenP r p -> ParenP r (setInserted p)
      WildP{} -> p
      AbsurdP{} -> p
      AsP r n p -> AsP r n (setInserted p)
      DotP r _ e -> DotP r Inserted e
      LitP{} -> p
      RecP r fs -> RecP r (map (fmap setInserted) fs)

    -- Turn function clauses into nice function clauses.
    mkClauses :: Name -> [Declaration] -> Catchall -> Nice [Clause]
    mkClauses _ [] _ = return []
    mkClauses x (Pragma (CatchallPragma r) : cs) True  = throwError $ InvalidCatchallPragma r
    mkClauses x (Pragma (CatchallPragma r) : cs) False = do
      when (null cs) $ throwError $ InvalidCatchallPragma r
      mkClauses x cs True
    mkClauses x (FunClause lhs@(LHS _ _ _ []) rhs wh ca : cs) catchall =
      (Clause x (ca || catchall) lhs rhs wh [] :) <$> mkClauses x cs False
    mkClauses x (FunClause lhs@(LHS _ ps _ es) rhs wh ca : cs) catchall = do
      when (null with) $ throwError $ MissingWithClauses x
      wcs <- mkClauses x with False
      (Clause x (ca || catchall) lhs rhs wh wcs :) <$> mkClauses x cs' False
      where
        (with, cs') = subClauses cs

        -- A clause is a subclause if the number of with-patterns is
        -- greater or equal to the current number of with-patterns plus the
        -- number of with arguments.
        subClauses :: [Declaration] -> ([Declaration],[Declaration])
        subClauses (c@(FunClause (LHS _ ps' _ _) _ _ _) : cs)
         | length ps' >= length ps + length es = mapFst (c:) (subClauses cs)
         | otherwise                           = ([], c:cs)
        subClauses (c@(FunClause (Ellipsis _ ps' _ _) _ _ _) : cs)
         = mapFst (c:) (subClauses cs)
        subClauses (c@(Pragma (CatchallPragma r)) : cs) = case subClauses cs of
          ([], cs') -> ([], c:cs')
          (cs, cs') -> (c:cs, cs')
        subClauses [] = ([],[])
        subClauses _  = __IMPOSSIBLE__
    mkClauses x (FunClause lhs@Ellipsis{} rhs wh ca : cs) catchall =
      (Clause x (ca || catchall) lhs rhs wh [] :) <$> mkClauses x cs False   -- Will result in an error later.
    mkClauses _ _ _ = __IMPOSSIBLE__

    -- for finding clauses for a type sig in mutual blocks
    couldBeFunClauseOf :: Maybe Fixity' -> Name -> Declaration -> Bool
    couldBeFunClauseOf mFixity x (Pragma (CatchallPragma{})) = True
    couldBeFunClauseOf mFixity x (FunClause Ellipsis{} _ _ _) = True
    couldBeFunClauseOf mFixity x (FunClause (LHS p _ _ _) _ _ _) =
      let
      pns        = patternNames p
      xStrings   = nameStringParts x
      patStrings = concatMap nameStringParts pns
      in
--          trace ("x = " ++ show x) $
--          trace ("pns = " ++ show pns) $
--          trace ("xStrings = " ++ show xStrings) $
--          trace ("patStrings = " ++ show patStrings) $
--          trace ("mFixity = " ++ show mFixity) $
      case (headMaybe pns, mFixity) of
        -- first identifier in the patterns is the fun.symbol?
        (Just y, _) | x == y -> True -- trace ("couldBe since y = " ++ show y) $ True
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

    -- ASR (27 May 2014). Commented out unused code.
    -- @isFunClauseOf@ is for non-mutual blocks where clauses must follow the
    -- type sig immediately
    -- isFunClauseOf :: Name -> Declaration -> Bool
    -- isFunClauseOf x (FunClause Ellipsis{} _ _) = True
    -- isFunClauseOf x (FunClause (LHS p _ _ _) _ _) =
    --  -- p is the whole left hand side, excluding "with" patterns and clauses
    --   case removeSingletonRawAppP p of
    --     IdentP (QName q)    -> x == q  -- lhs is just an identifier
    --     _                   -> True
    --         -- more complicated lhss must come with type signatures, so we just assume
    --         -- it's part of the current definition
    -- isFunClauseOf _ _ = False

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

    -- Make an old style mutual block from a list of mutual declarations
    mkOldMutual :: Range -> [NiceDeclaration] -> Nice NiceDeclaration
    mkOldMutual r ds = do
        -- Check that there aren't any missing definitions
        checkLoneSigs loneNames
        -- Check that there are no declarations that aren't allowed in old style mutual blocks
        case filter notAllowedInMutual ds of
          []  -> return ()
          (NiceFunClause _ _ _ _ s_ (FunClause lhs _ _ _)):_ -> throwError $ MissingTypeSignature lhs
          d:_ -> throwError $ NotAllowedInMutual d
        tc0 <- use terminationCheckPragma
        let tcs = map termCheck ds
        tc <- combineTermChecks r (tc0:tcs)

        pc0 <- use positivityCheckPragma
        let pc :: PositivityCheck
            pc = pc0 && all positivityCheckOldMutual ds

        return $ NiceMutual r tc pc $ sigs ++ other
      where
        -- Andreas, 2013-11-23 allow postulates in mutual blocks
        notAllowedInMutual Axiom{} = False
        notAllowedInMutual d       = declKind d == OtherDecl
        -- Pull type signatures to the top
        (sigs, other) = partition isTypeSig ds
        isTypeSig Axiom{}                     = True
        isTypeSig d | LoneSig{} <- declKind d = True
        isTypeSig _                           = False

        sigNames  = [ (x, k) | LoneSig k x <- map declKind ds ]
        defNames  = [ (x, k) | LoneDefs k xs <- map declKind ds, x <- xs ]
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

        -- ASR (26 December 2015): Do not positivity check a mutual
        -- block if any of its inner declarations comes with a
        -- NO_POSITIVITY_CHECK pragma. See Issue 1614.
        positivityCheckOldMutual :: NiceDeclaration -> PositivityCheck
        positivityCheckOldMutual (DataDef _ _ _ pc _ _ _)      = pc
        positivityCheckOldMutual (NiceDataSig _ _ _ _ pc _ _ _)= pc
        positivityCheckOldMutual (NiceMutual _ _ pc _)         = __IMPOSSIBLE__
        positivityCheckOldMutual (NiceRecSig _ _ _ _ pc _ _ _) = pc
        positivityCheckOldMutual (RecDef _ _ _ pc _ _ _ _ _ _) = pc
        positivityCheckOldMutual _                             = True

        -- A mutual block cannot have a measure,
        -- but it can skip termination check.

    abstractBlock _ [] = return []
    abstractBlock r ds = do
      let (ds', anyChange) = runChange $ mkAbstract ds
          inherited        = r == noRange
          -- hack to avoid failing on inherited abstract blocks in where clauses
      if anyChange || inherited then return ds' else throwError $ UselessAbstract r

    privateBlock _ _ [] = return []
    privateBlock r o ds = do
      let (ds', anyChange) = runChange $ mkPrivate o ds
      if anyChange then return ds' else
        if o == UserWritten then throwError $ UselessPrivate r else return ds -- no change!

    instanceBlock _ [] = return []
    instanceBlock r ds = do
      let (ds', anyChange) = runChange $ mapM mkInstance ds
      if anyChange then return ds' else throwError $ UselessInstance r

    -- Make a declaration eligible for instance search.
    mkInstance :: Updater NiceDeclaration
    mkInstance d =
      case d of
        Axiom r f p a i rel mp x e       -> (\ i -> Axiom r f p a i rel mp x e) <$> setInstance i
        FunSig r f p a i m rel tc x e    -> (\ i -> FunSig r f p a i m rel tc x e) <$> setInstance i
        NiceUnquoteDecl r f p a i tc x e -> (\ i -> NiceUnquoteDecl r f p a i tc x e) <$> setInstance i
        NiceMutual{}                     -> return d
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
      DataDef r f a pc x ps cs         -> (\ a -> DataDef r f a pc x ps) <$> mkAbstract a <*> mkAbstract cs
      RecDef r f a pc x i e c ps cs    -> (\ a -> RecDef r f a pc x i e c ps) <$> mkAbstract a <*> mkAbstract cs
      NiceFunClause r p a termCheck catchall d  -> (\ a -> NiceFunClause r p a termCheck catchall d) <$> mkAbstract a
      -- The following declarations have an @InAbstract@ field
      -- but are not really definitions, so we do count them into
      -- the declarations which can be made abstract
      -- (thus, do not notify progress with @dirty@).
      Axiom r f p a i rel mp x e       -> return $ Axiom             r f p AbstractDef i rel mp x e
      FunSig r f p a i m rel tc x e    -> return $ FunSig            r f p AbstractDef i m rel tc x e
      NiceRecSig r f p a pc x ls t     -> return $ NiceRecSig        r f p AbstractDef pc x ls t
      NiceDataSig r f p a pc x ls t    -> return $ NiceDataSig       r f p AbstractDef pc x ls t
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
      NiceRecSig r f p a pc x ls t             -> (\ p -> NiceRecSig r f p a pc x ls t)             <$> mkPrivate o p
      NiceDataSig r f p a pc x ls t            -> (\ p -> NiceDataSig r f p a pc x ls t)            <$> mkPrivate o p
      NiceFunClause r p a termCheck catchall d -> (\ p -> NiceFunClause r p a termCheck catchall d) <$> mkPrivate o p
      NiceUnquoteDecl r f p a i t x e          -> (\ p -> NiceUnquoteDecl r f p a i t x e)          <$> mkPrivate o p
      NiceUnquoteDef r f p a t x e             -> (\ p -> NiceUnquoteDef r f p a t x e)             <$> mkPrivate o p
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
notSoNiceDeclarations d =
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
    NiceRecSig r _ _ _ _ x bs e      -> [RecordSig r x bs e]
    NiceDataSig r _ _ _ _ x bs e     -> [DataSig r Inductive x bs e]
    NiceFunClause _ _ _ _ _ d        -> [d]
    FunSig _ _ _ _ i _ rel tc x e    -> inst i [TypeSig rel x e]
    FunDef _r ds _ _ _ _ _ _         -> ds
    DataDef r _ _ _ x bs cs          -> [Data r Inductive x bs Nothing $ concatMap notSoNiceDeclarations cs]
    RecDef r _ _ _ x i e c bs ds     -> [Record r x i e (unThing <$> c) bs Nothing $ concatMap notSoNiceDeclarations ds]
      where unThing (ThingWithFixity c _, inst) = (c, inst)
    NicePatternSyn r _ n as p        -> [PatternSyn r n as p]
    NiceUnquoteDecl r _ _ _ i _ x e  -> inst i [UnquoteDecl r x e]
    NiceUnquoteDef r _ _ _ _ x e     -> [UnquoteDef r x e]
  where
    inst InstanceDef    ds = [InstanceB (getRange ds) ds]
    inst NotInstanceDef ds = ds

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
    DataDef _ _ a _ _ _ _           -> Just a
    RecDef _ _ a _ _ _ _ _ _ _      -> Just a
    NicePatternSyn{}                -> Nothing
    NiceUnquoteDecl _ _ _ a _ _ _ _ -> Just a
    NiceUnquoteDef _ _ _ a _ _ _    -> Just a
