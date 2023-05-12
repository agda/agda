module Agda.Syntax.Concrete.Definitions.Types where

import Control.DeepSeq

import Data.Map (Map)
import Data.Semigroup ( Semigroup(..) )

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (TerminationCheck())
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Pretty

import Agda.Utils.Pretty
import Agda.Utils.Impossible
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1

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
  | NiceModule Range Access IsAbstract Erased QName Telescope
      [Declaration]
  | NiceModuleMacro Range Access Erased Name ModuleApplication
      OpenShortHand ImportDirective
  | NiceOpen Range QName ImportDirective
  | NiceImport Range QName (Maybe AsName) OpenShortHand ImportDirective
  | NicePragma Range Pragma
  | NiceRecSig Range Erased Access IsAbstract PositivityCheck
      UniverseCheck Name [LamBinding] Expr
  | NiceDataSig Range Erased Access IsAbstract PositivityCheck
      UniverseCheck Name [LamBinding] Expr
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
  | NiceLoneConstructor Range [NiceConstructor]
  | NiceRecDef Range Origin IsAbstract PositivityCheck UniverseCheck Name RecordDirectives [LamBinding] [Declaration]
      -- ^ @(Maybe Range)@ gives range of the 'pattern' declaration.
  | NicePatternSyn Range Access Name [Arg Name] Pattern
  | NiceGeneralize Range Access ArgInfo TacticAttribute Name Expr
  | NiceUnquoteDecl Range Access IsAbstract IsInstance TerminationCheck CoverageCheck [Name] Expr
  | NiceUnquoteDef Range Access IsAbstract TerminationCheck CoverageCheck [Name] Expr
  | NiceUnquoteData Range Access IsAbstract PositivityCheck UniverseCheck Name [Name] Expr
  | NiceOpaque Range [QName] [NiceDeclaration]
  deriving (Show, Generic)

instance NFData NiceDeclaration

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
    deriving (Show, Generic)

instance NFData Clause

-- | When processing a mutual block we collect the various checks present in the block
--   before combining them.

data MutualChecks = MutualChecks
  { mutualTermination :: [TerminationCheck]
  , mutualCoverage    :: [CoverageCheck]
  , mutualPositivity  :: [PositivityCheck]
  }

instance Semigroup MutualChecks where
  MutualChecks a b c <> MutualChecks a' b' c'
    = MutualChecks (a <> a') (b <> b') (c <> c')

instance Monoid MutualChecks where
  mempty = MutualChecks [] [] []
  mappend = (<>)

-- | In an inferred `mutual' block we keep accumulating nice declarations until all
--   of the lone signatures have an attached definition. The type is therefore a bit
--   span-like: we return an initial segment (the inferred mutual block) together
--   with leftovers.

data InferredMutual = InferredMutual
  { inferredChecks    :: MutualChecks       -- checks for this block
  , inferredBlock     :: [NiceDeclaration]  -- mutual block
  , inferredLeftovers :: [NiceDeclaration]  -- leftovers
  }

extendInferredBlock :: NiceDeclaration -> InferredMutual -> InferredMutual
extendInferredBlock d (InferredMutual cs ds left) = InferredMutual cs (d : ds) left

-- | In an `interleaved mutual' block we collect the data signatures, function signatures,
--   as well as their associated constructors and function clauses respectively.
--   Each signature is given a position in the block (from 0 onwards) and each set
--   of constructor / clauses is given a *distinct* one. This allows for interleaved
--   forward declarations similar to what one gets in a new-style mutual block.
type InterleavedMutual = Map Name InterleavedDecl

data InterleavedDecl
  = InterleavedData
    { interleavedDeclNum  :: DeclNum
        -- ^ Internal number of the data signature.
    , interleavedDeclSig  :: NiceDeclaration
        -- ^ The data signature.
    , interleavedDataCons :: Maybe (DeclNum, List1 [NiceConstructor])
        -- ^ Constructors associated to the data signature.
    }
  | InterleavedFun
    { interleavedDeclNum  :: DeclNum
        -- ^ Internal number of the function signature.
    , interleavedDeclSig  :: NiceDeclaration
        -- ^ The function signature.
    , interleavedFunClauses :: Maybe (DeclNum, List1 ([Declaration],[Clause]))
        -- ^ Function clauses associated to the function signature.
    }

-- | Numbering declarations in an @interleaved mutual@ block.
type DeclNum = Int

isInterleavedFun :: InterleavedDecl -> Maybe ()
isInterleavedFun InterleavedFun{} = Just ()
isInterleavedFun _ = Nothing

isInterleavedData :: InterleavedDecl -> Maybe ()
isInterleavedData InterleavedData{} = Just ()
isInterleavedData _ = Nothing

interleavedDecl :: Name -> InterleavedDecl -> [(DeclNum, NiceDeclaration)]
interleavedDecl k = \case
  InterleavedData i d@(NiceDataSig _ _ acc abs pc uc _ pars _) ds ->
    let fpars   = concatMap dropTypeAndModality pars
        r       = getRange (k, fpars)
        ddef cs = NiceDataDef (getRange (r, cs)) UserWritten
                    abs pc uc k fpars cs
    in (i,d) : maybe [] (\ (j, dss) -> [(j, ddef (sconcat (List1.reverse dss)))]) ds
  InterleavedFun i d@(FunSig r acc abs inst mac info tc cc n e) dcs ->
    let fdef dcss = let (dss, css) = List1.unzip dcss in
                    FunDef r (sconcat dss) abs inst tc cc n (sconcat css)
    in (i,d) : maybe [] (\ (j, dcss) -> [(j, fdef (List1.reverse dcss))]) dcs
  _ -> __IMPOSSIBLE__ -- someone messed up and broke the invariant

-- | Several declarations expect only type signatures as sub-declarations.  These are:
data KindOfBlock
  = PostulateBlock  -- ^ @postulate@
  | PrimitiveBlock  -- ^ @primitive@.  Ensured by parser.
  | InstanceBlock   -- ^ @instance@.  Actually, here all kinds of sub-declarations are allowed a priori.
  | FieldBlock      -- ^ @field@.  Ensured by parser.
  | DataBlock       -- ^ @data ... where@.  Here we got a bad error message for Agda-2.5 (Issue 1698).
  | ConstructorBlock  -- ^ @constructor@, in @interleaved mutual@.
  deriving (Eq, Ord, Show)


instance HasRange NiceDeclaration where
  getRange (Axiom r _ _ _ _ _ _)           = r
  getRange (NiceField r _ _ _ _ _ _)       = r
  getRange (NiceMutual r _ _ _ _)          = r
  getRange (NiceModule r _ _ _ _ _ _ )     = r
  getRange (NiceModuleMacro r _ _ _ _ _ _) = r
  getRange (NiceOpen r _ _)                = r
  getRange (NiceImport r _ _ _ _)          = r
  getRange (NicePragma r _)                = r
  getRange (PrimitiveFunction r _ _ _ _)   = r
  getRange (FunSig r _ _ _ _ _ _ _ _ _)    = r
  getRange (FunDef r _ _ _ _ _ _ _)        = r
  getRange (NiceDataDef r _ _ _ _ _ _ _)   = r
  getRange (NiceLoneConstructor r _)       = r
  getRange (NiceRecDef r _ _ _ _ _ _ _ _)  = r
  getRange (NiceRecSig r _ _ _ _ _ _ _ _)  = r
  getRange (NiceDataSig r _ _ _ _ _ _ _ _) = r
  getRange (NicePatternSyn r _ _ _ _)      = r
  getRange (NiceGeneralize r _ _ _ _ _)    = r
  getRange (NiceFunClause r _ _ _ _ _ _)   = r
  getRange (NiceUnquoteDecl r _ _ _ _ _ _ _) = r
  getRange (NiceUnquoteDef r _ _ _ _ _ _)  = r
  getRange (NiceUnquoteData r _ _ _ _ _ _ _) = r
  getRange (NiceOpaque r _ _)                = r

instance Pretty NiceDeclaration where
  pretty = \case
    Axiom _ _ _ _ _ x _            -> text "postulate" <+> pretty x <+> colon <+> text "_"
    NiceField _ _ _ _ _ x _        -> text "field" <+> pretty x
    PrimitiveFunction _ _ _ x _    -> text "primitive" <+> pretty x
    NiceMutual{}                   -> text "mutual"
    NiceOpaque{}                   -> text "opaque"
    NiceModule _ _ _ _ x _ _       -> text "module" <+> pretty x <+> text "where"
    NiceModuleMacro _ _ _ x _ _ _  -> text "module" <+> pretty x <+> text "= ..."
    NiceOpen _ x _                 -> text "open" <+> pretty x
    NiceImport _ x _ _ _           -> text "import" <+> pretty x
    NicePragma{}                   -> text "{-# ... #-}"
    NiceRecSig _ _ _ _ _ _ x _ _   -> text "record" <+> pretty x
    NiceDataSig _ _ _ _ _ _ x _ _  -> text "data" <+> pretty x
    NiceFunClause{}                -> text "<function clause>"
    FunSig _ _ _ _ _ _ _ _ x _     -> pretty x <+> colon <+> text "_"
    FunDef _ _ _ _ _ _ x _         -> pretty x <+> text "= _"
    NiceDataDef _ _ _ _ _ x _ _    -> text "data" <+> pretty x <+> text "where"
    NiceLoneConstructor _ ds       -> text "constructor"
    NiceRecDef _ _ _ _ _ x  _ _ _  -> text "record" <+> pretty x <+> text "where"
    NicePatternSyn _ _ x _ _       -> text "pattern" <+> pretty x
    NiceGeneralize _ _ _ _ x _     -> text "variable" <+> pretty x
    NiceUnquoteDecl _ _ _ _ _ _ xs _ -> text "<unquote declarations>"
    NiceUnquoteDef _ _ _ _ _ xs _    -> text "<unquote definitions>"
    NiceUnquoteData _ _ _ _ _ x xs _ -> text "<unquote data types>"

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
declName NiceUnquoteData{}   = "Unquoted data types"
declName NiceRecSig{}        = "Records"
declName NiceDataSig{}       = "Data types"
declName NiceFunClause{}     = "Functions without a type signature"
declName FunSig{}            = "Type signatures"
declName FunDef{}            = "Function definitions"
declName NiceRecDef{}        = "Records"
declName NiceDataDef{}       = "Data types"
declName NiceLoneConstructor{} = "Constructors"
declName NiceOpaque{}          = "Opaque blocks"


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
  deriving Show

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

mutualChecks :: DataRecOrFun -> MutualChecks
mutualChecks k = MutualChecks [terminationCheck k] [coverageCheck k] [positivityCheck k]

universeCheck :: DataRecOrFun -> UniverseCheck
universeCheck (DataName _ uc) = uc
universeCheck (RecName _ uc)  = uc
universeCheck (FunName _ _)   = YesUniverseCheck
