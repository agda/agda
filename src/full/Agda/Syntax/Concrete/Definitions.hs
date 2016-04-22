{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

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
    , notSoNiceDeclaration
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
import Data.Monoid ( Monoid(mappend, mempty) )
import Data.List as List hiding (null)
import Data.Traversable (traverse)
import Data.Typeable (Typeable)

import Agda.Syntax.Concrete
import Agda.Syntax.Common hiding (TerminationCheck())
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete.Pretty ()

import Agda.Utils.Except ( Error(strMsg), MonadError(throwError) )
import Agda.Utils.Lens
import Agda.Utils.List (headMaybe, isSublistOf)
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty
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
-}
data NiceDeclaration
  = Axiom Range Fixity' Access IsInstance ArgInfo Name Expr
      -- ^ Axioms and functions can be declared irrelevant. (Hiding should be NotHidden)
  | NiceField Range IsInstance Fixity' Access IsAbstract Name (Arg Expr)
  | PrimitiveFunction Range Fixity' Access IsAbstract Name Expr
  | NiceMutual Range TerminationCheck PositivityCheck [NiceDeclaration]
  | NiceModule Range Access IsAbstract QName Telescope [Declaration]
  | NiceModuleMacro Range Access Name ModuleApplication OpenShortHand ImportDirective
  | NiceOpen Range QName ImportDirective
  | NiceImport Range QName (Maybe AsName) OpenShortHand ImportDirective
  | NicePragma Range Pragma
  | NiceRecSig Range Fixity' Access Name [LamBinding] Expr PositivityCheck
  | NiceDataSig Range Fixity' Access Name [LamBinding] Expr PositivityCheck
  | NiceFunClause Range Access IsAbstract TerminationCheck Catchall Declaration
    -- ^ An uncategorized function clause, could be a function clause
    --   without type signature or a pattern lhs (e.g. for irrefutable let).
    --   The 'Declaration' is the actual 'FunClause'.
  | FunSig Range Fixity' Access IsInstance IsMacro ArgInfo TerminationCheck Name Expr
  | FunDef  Range [Declaration] Fixity' IsAbstract TerminationCheck Name [Clause]
      -- ^ Block of function clauses (we have seen the type signature before).
      --   The 'Declaration's are the original declarations that were processed
      --   into this 'FunDef' and are only used in 'notSoNiceDeclaration'.
  | DataDef Range Fixity' IsAbstract Name [LamBinding] PositivityCheck [NiceConstructor]
  | RecDef Range Fixity' IsAbstract Name (Maybe (Ranged Induction)) (Maybe Bool) (Maybe (ThingWithFixity Name, IsInstance)) [LamBinding] PositivityCheck [NiceDeclaration]
  | NicePatternSyn Range Fixity' Name [Arg Name] Pattern
  | NiceUnquoteDecl Range [Fixity'] Access IsInstance IsAbstract TerminationCheck [Name] Expr
  | NiceUnquoteDef Range [Fixity'] Access IsAbstract TerminationCheck [Name] Expr
  deriving (Typeable, Show)

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
    deriving (Typeable, Show)

-- | The exception type.
data DeclarationException
        = MultipleFixityDecls [(Name, [Fixity'])]
        | InvalidName Name
        | DuplicateDefinition Name
        | MissingDefinition Name
        | MissingWithClauses Name
        | MissingTypeSignature LHS -- Andreas 2012-06-02: currently unused, remove after a while -- Fredrik 2012-09-20: now used, can we keep it?
        | MissingDataSignature Name
        | WrongDefinition Name DataRecOrFun DataRecOrFun
        | WrongParameters Name
        | NotAllowedInMutual NiceDeclaration
        | UnknownNamesInFixityDecl [Name]
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

    deriving (Typeable)

-- | Several declarations expect only type signatures as sub-declarations.  These are:
data KindOfBlock
  = PostulateBlock  -- ^ @postulate@
  | PrimitiveBlock  -- ^ @primitive@.  Ensured by parser.
  | InstanceBlock   -- ^ @instance@.  Actually, here all kinds of sub-declarations are allowed a priori.
  | FieldBlock      -- ^ @field@.  Ensured by parser.
  | DataBlock       -- ^ @data ... where@.  Here we got a bad error message for Agda-2.5 (Issue 1698).
  deriving (Typeable, Eq, Ord, Show)


instance HasRange DeclarationException where
  getRange (MultipleFixityDecls xs)           = getRange (fst $ head xs)
  getRange (InvalidName x)                    = getRange x
  getRange (DuplicateDefinition x)            = getRange x
  getRange (MissingDefinition x)              = getRange x
  getRange (MissingWithClauses x)             = getRange x
  getRange (MissingTypeSignature x)           = getRange x
  getRange (MissingDataSignature x)           = getRange x
  getRange (WrongDefinition x k k')           = getRange x
  getRange (WrongParameters x)                = getRange x
  getRange (AmbiguousFunClauses lhs xs)       = getRange lhs
  getRange (NotAllowedInMutual x)             = getRange x
  getRange (UnknownNamesInFixityDecl xs)      = getRange . head $ xs
  getRange (Codata r)                         = r
  getRange (DeclarationPanic _)               = noRange
  getRange (UselessPrivate r)                 = r
  getRange (UselessAbstract r)                = r
  getRange (UselessInstance r)                = r
  getRange (WrongContentBlock _ r)            = r
  getRange (InvalidTerminationCheckPragma r)  = r
  getRange (InvalidMeasureMutual r)           = r
  getRange (PragmaNoTerminationCheck r)       = r
  getRange (InvalidCatchallPragma r)          = r
  getRange (UnquoteDefRequiresSignature x)    = getRange x
  getRange (BadMacroDef d)                    = getRange d
  getRange (InvalidNoPositivityCheckPragma r) = r

instance HasRange NiceDeclaration where
  getRange (Axiom r _ _ _ _ _ _)             = r
  getRange (NiceField r _ _ _ _ _ _)         = r
  getRange (NiceMutual r _ _ _)              = r
  getRange (NiceModule r _ _ _ _ _ )         = r
  getRange (NiceModuleMacro r _ _ _ _ _)     = r
  getRange (NiceOpen r _ _)                  = r
  getRange (NiceImport r _ _ _ _)            = r
  getRange (NicePragma r _)                  = r
  getRange (PrimitiveFunction r _ _ _ _ _)   = r
  getRange (FunSig r _ _ _ _ _ _ _ _)        = r
  getRange (FunDef r _ _ _ _ _ _)            = r
  getRange (DataDef r _ _ _ _ _ _)           = r
  getRange (RecDef r _ _ _ _ _ _ _ _ _)      = r
  getRange (NiceRecSig r _ _ _ _ _ _)        = r
  getRange (NiceDataSig r _ _ _ _ _ _)       = r
  getRange (NicePatternSyn r _ _ _ _)        = r
  getRange (NiceFunClause r _ _ _ _ _)       = r
  getRange (NiceUnquoteDecl r _ _ _ _ _ _ _) = r
  getRange (NiceUnquoteDef r _ _ _ _ _ _)    = r

instance Error DeclarationException where
  strMsg = DeclarationPanic

-- These error messages can (should) be terminated by a dot ".",
-- there is no error context printed after them.
instance Pretty DeclarationException where
  pretty (MultipleFixityDecls xs) =
    sep [ fsep $ pwords "Multiple fixity or syntax declarations for"
        , vcat $ map f xs
        ]
      where
        f (x, fs) = pretty x <> text ": " <+> fsep (map pretty fs)
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
  pretty (WrongParameters x) = fsep $
    pwords "List of parameters does not match previous signature for" ++ [pretty x]
  pretty (AmbiguousFunClauses lhs xs) = sep
    [ fsep $
        pwords "More than one matching type signature for left hand side " ++ [pretty lhs] ++
        pwords "it could belong to any of:"
    , vcat $ map (pretty . PrintRange) xs
    ]
  pretty (UnknownNamesInFixityDecl xs) = fsep $
    pwords "The following names are not declared in the same scope as their syntax or fixity declaration (i.e., either not in scope at all, imported from another module, or declared in a super module):" ++ map pretty xs
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
      _ -> __IMPOSSIBLE__
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
  = DataName PositivityCheck Params  -- ^ name of a data with parameters
  | RecName  PositivityCheck Params  -- ^ name of a record with parameters
  | FunName  TerminationCheck        -- ^ name of a function

-- Ignore pragmas when checking equality
instance Eq DataRecOrFun where
  DataName _ p == DataName _ q = p == q
  RecName  _ p == RecName  _ q = p == q
  FunName  _   == FunName  _   = True
  _            == _            = False

type Params = [Hiding]

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


-- | Nicifier monad.

type Nice = StateT NiceEnv (Either DeclarationException)

-- | Nicifier state.

data NiceEnv = NiceEnv
  { _loneSigs :: LoneSigs
    -- ^ Lone type signatures that wait for their definition.
  , fixs     :: Fixities
  }

type LoneSigs = Map Name DataRecOrFun
type Fixities = Map Name Fixity'

-- | Initial nicifier state.

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { _loneSigs = empty
  , fixs      = empty
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

-- | Check whether name is not "_" and return its fixity.
getFixity :: Name -> Nice Fixity'
getFixity x = do
  when (isUnderscore x) $ throwError $ InvalidName x
  Map.findWithDefault noFixity' x <$> gets fixs  -- WAS: defaultFixity'

runNice :: Nice a -> Either DeclarationException a
runNice nice = nice `evalStateT` initNiceEnv

data DeclKind
    = LoneSig DataRecOrFun Name
    | LoneDefs DataRecOrFun [Name]
    | OtherDecl
  deriving (Eq, Show)

declKind :: NiceDeclaration -> DeclKind
declKind (FunSig _ _ _ _ _ _ tc x _)      = LoneSig (FunName tc) x
declKind (NiceRecSig _ _ _ x pars _ pc)   = LoneSig (RecName pc $ parameters pars) x
declKind (NiceDataSig _ _ _ x pars _ pc)  = LoneSig (DataName pc $ parameters pars) x
declKind (FunDef _ _ _ _ tc x _)          = LoneDefs (FunName tc) [x]
declKind (DataDef _ _ _ x pars pc _)      = LoneDefs (DataName pc $ parameters pars) [x]
declKind (RecDef _ _ _ x _ _ _ pars pc _) = LoneDefs (RecName pc $ parameters pars) [x]
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

-- | Compute visible parameters of a data or record signature or definition.
parameters :: [LamBinding] -> Params
parameters = List.concat . List.map numP where
  numP (DomainFree i _) = [argInfoHiding i]
  numP (DomainFull (TypedBindings _ (Arg i (TBind _ xs _)))) = List.replicate (length xs) $ argInfoHiding i
  numP (DomainFull (TypedBindings _ (Arg _ TLet{})))         = []

-- | Main.
niceDeclarations :: [Declaration] -> Nice [NiceDeclaration]
niceDeclarations ds = do
  -- Get fixity and syntax declarations.
  fixs <- fixities ds
  case Map.keys fixs \\ concatMap declaredNames ds of
    -- If we have fixity/syntax decls for names not declared
    -- in the current scope, fail.
    xs@(_:_) -> throwError $ UnknownNamesInFixityDecl xs
    []       -> localState $ do
      -- Run the nicifier in an initial environment of fixity decls.
      put $ initNiceEnv { fixs = fixs }
      ds <- nice ds
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
      Private   _ ds       -> concatMap declaredNames ds
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
                (NiceRecSig{}, [r@(RecDef _ _ _ _ _ _ _ _ True _)]) -> ([d, r] ++)
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

    nice (Pragma (TerminationCheckPragma r NoTerminationCheck) : _) =
      throwError $ PragmaNoTerminationCheck r

    nice (Pragma (TerminationCheckPragma r tc) : ds@(Mutual{} : _)) | notMeasure tc = do
      ds <- nice ds
      case ds of
        NiceMutual r _ pc ds' : ds -> return $ NiceMutual r tc pc ds' : ds
        _                          -> __IMPOSSIBLE__

    nice (Pragma (TerminationCheckPragma r tc) : d@TypeSig{} : ds) =
      niceTypeSig tc d ds

    nice (Pragma (TerminationCheckPragma r tc) : d@FunClause{} : ds) | notMeasure tc =
      niceFunClause tc False d ds

    nice (Pragma (TerminationCheckPragma r tc) : ds@(UnquoteDecl{} : _)) | notMeasure tc = do
      NiceUnquoteDecl r f p a i _ x e : ds <- nice ds
      return $ NiceUnquoteDecl r f p a i tc x e : ds

    nice (Pragma (TerminationCheckPragma r tc) : d@(Pragma (NoPositivityCheckPragma _)) : ds@(Mutual{} : _)) | notMeasure tc = do
      ds <- nice (d : ds)
      case ds of
        NiceMutual r _ pc ds' : ds -> return $ NiceMutual r tc pc ds' : ds
        _                          -> __IMPOSSIBLE__

    nice (Pragma (CatchallPragma r) : d@FunClause{} : ds) =
      niceFunClause TerminationCheck True d ds

    nice (d@TypeSig{} : Pragma (TerminationCheckPragma r (TerminationMeasure _ x)) : ds) =
      niceTypeSig (TerminationMeasure r x) d ds

    -- nice (Pragma (MeasurePragma r x) : d@FunClause{} : ds) =
    --   niceFunClause (TerminationMeasure r x) d ds

    nice (Pragma (NoPositivityCheckPragma _) : ds@(Mutual{} : _)) = do
      ds <- nice ds
      case ds of
        NiceMutual r tc _ ds' : ds -> return $ NiceMutual r tc False ds' : ds
        _                          -> __IMPOSSIBLE__

    nice (Pragma (NoPositivityCheckPragma _) : d@(Data _ Inductive _ _ _ _) : ds) =
      niceDataDef False d ds

    nice (Pragma (NoPositivityCheckPragma _) : d@(DataSig _ Inductive _ _ _) : ds) =
      niceDataSig False d ds

    nice (Pragma (NoPositivityCheckPragma _) : d@Record{} : ds) =
      niceRecord False d ds

    nice (Pragma (NoPositivityCheckPragma _) : d@RecordSig{} : ds) =
      niceRecordSig False d ds

    nice (Pragma (NoPositivityCheckPragma _) : d@(Pragma (TerminationCheckPragma _ _)) : ds@(Mutual{} : _)) = do
      ds <- nice (d : ds)
      case ds of
        NiceMutual r tc _ ds' : ds -> return $ NiceMutual r tc False ds' : ds
        _                          -> __IMPOSSIBLE__

    nice (d:ds) = do
      case d of
        TypeSig{}                     -> niceTypeSig TerminationCheck d ds
        FunClause{}                   -> niceFunClause TerminationCheck False d ds
        Field{}                       -> (++) <$> niceAxioms FieldBlock [ d ] <*> nice ds
        DataSig r CoInductive _ _ _   -> throwError (Codata r)
        Data r CoInductive _ _ _ _    -> throwError (Codata r)
        d@(DataSig _ Inductive _ _ _) -> niceDataSig True d ds
        d@(Data _ Inductive _ _ _ _)  -> niceDataDef True d ds
        d@RecordSig{}                 -> niceRecordSig True d ds
        d@Record{}                    -> niceRecord True d ds

        Mutual r ds' ->
          (:) <$> (mkOldMutual r =<< nice ds') <*> nice ds

        Abstract r ds' ->
          (++) <$> (abstractBlock r =<< nice ds') <*> nice ds

        Private r ds' ->
          (++) <$> (privateBlock r =<< nice ds') <*> nice ds

        InstanceB r ds' ->
          (++) <$> (instanceBlock r =<< nice ds') <*> nice ds

        Macro r ds' ->
          (++) <$> (macroBlock r =<< nice ds') <*> nice ds

        Postulate _ ds' -> (++) <$> niceAxioms PostulateBlock ds' <*> nice ds

        Primitive _ ds' -> (++) <$> (map toPrim <$> niceAxioms PrimitiveBlock ds') <*> nice ds

        Module r x tel ds' ->
          (NiceModule r PublicAccess ConcreteDef x tel ds' :) <$> nice ds

        ModuleMacro r x modapp op is ->
          (NiceModuleMacro r PublicAccess x modapp op is :)
            <$> nice ds

        -- Fixity and syntax declarations have been looked at already.
        Infix _ _           -> nice ds
        Syntax _ _          -> nice ds

        PatternSyn r n as p -> do
          fx <- getFixity n
          (NicePatternSyn r fx n as p :) <$> nice ds
        Open r x is         -> (NiceOpen r x is :) <$> nice ds
        Import r x as op is -> (NiceImport r x as op is :) <$> nice ds

        UnquoteDecl r xs e -> do
          fxs <- mapM getFixity xs
          (NiceUnquoteDecl r fxs PublicAccess NotInstanceDef ConcreteDef TerminationCheck xs e :) <$> nice ds

        UnquoteDef r xs e -> do
          fxs  <- mapM getFixity xs
          sigs <- map fst . filter (isFunName . snd) . Map.toList <$> use loneSigs
          let missing = filter (`notElem` sigs) xs
          if null missing
            then do
              mapM_ removeLoneSig xs
              (NiceUnquoteDef r fxs PublicAccess ConcreteDef TerminationCheck xs e :) <$> nice ds
            else throwError $ UnquoteDefRequiresSignature missing

        Pragma (TerminationCheckPragma r NoTerminationCheck) ->
          throwError $ PragmaNoTerminationCheck r
        Pragma (TerminationCheckPragma r _) ->
          throwError $ InvalidTerminationCheckPragma r

        Pragma (CatchallPragma r) ->
          throwError $ InvalidCatchallPragma r

        Pragma (NoPositivityCheckPragma r) ->
          throwError $ InvalidNoPositivityCheckPragma r

        Pragma p -> (NicePragma (getRange p) p :) <$> nice ds

    niceFunClause :: TerminationCheck -> Catchall -> Declaration -> [Declaration] -> Nice [NiceDeclaration]
    niceFunClause termCheck catchall d@(FunClause lhs _ _ _) ds = do
          xs <- map fst . filter (isFunName . snd) . Map.toList <$> use loneSigs
          -- for each type signature 'x' waiting for clauses, we try
          -- if we have some clauses for 'x'
          fixs <- gets fixs
          case [ (x, (fits, rest))
               | x <- xs
               , let (fits, rest) =
                      span (couldBeFunClauseOf (Map.lookup x fixs) x) (d : ds)
               , not (null fits)
               ] of

            -- case: clauses match none of the sigs
            [] -> case lhs of
              -- Subcase: The lhs is single identifier.
              -- Treat it as a function clause without a type signature.
              LHS p [] [] [] | IdentP (QName x) <- removeSingletonRawAppP p -> do
                ds <- nice ds
                d  <- mkFunDef defaultArgInfo termCheck x Nothing [d] -- fun def without type signature is relevant
                return $ d ++ ds
              -- Subcase: The lhs is a proper pattern.
              -- This could be a let-pattern binding. Pass it on.
              -- A missing type signature error might be raise in ConcreteToAbstract
              _ -> do
                ds <- nice ds
                return $ NiceFunClause (getRange d) PublicAccess ConcreteDef termCheck catchall d : ds

            -- case: clauses match exactly one of the sigs
            [(x,(fits,rest))] -> do
               removeLoneSig x
               cs  <- mkClauses x (expandEllipsis fits) False
               ds1 <- nice rest
               fx  <- getFixity x
               d   <- return $ FunDef (getRange fits) fits fx ConcreteDef termCheck x cs
               return $ d : ds1

            -- case: clauses match more than one sigs (ambiguity)
            l -> throwError $ AmbiguousFunClauses lhs $ reverse $ map fst l -- "ambiguous function clause; cannot assign it uniquely to one type signature"
    niceFunClause _ _ _ _ = __IMPOSSIBLE__

    niceTypeSig :: TerminationCheck -> Declaration -> [Declaration] -> Nice [NiceDeclaration]
    niceTypeSig termCheck d@(TypeSig info x t) ds = do
      fx <- getFixity x
      -- register x as lone type signature, to recognize clauses later
      addLoneSig x (FunName termCheck)
      ds <- nice ds
      return $ FunSig (getRange d) fx PublicAccess NotInstanceDef NotMacroDef info termCheck x t : ds
    niceTypeSig _ _ _ = __IMPOSSIBLE__

    niceDataDef :: PositivityCheck -> Declaration -> [Declaration] ->
                   Nice [NiceDeclaration]
    niceDataDef pc (Data r Inductive x tel t cs) ds = do
      t <- defaultTypeSig (DataName pc $ parameters tel) x t
      (++) <$> dataOrRec pc DataDef NiceDataSig (niceAxioms DataBlock) r x tel t (Just cs)
           <*> nice ds
    niceDataDef _ _ _ = __IMPOSSIBLE__

    niceDataSig :: PositivityCheck -> Declaration -> [Declaration] ->
                   Nice [NiceDeclaration]
    niceDataSig pc (DataSig r Inductive x tel t) ds = do
      addLoneSig x (DataName pc $ parameters tel)
      (++) <$> dataOrRec pc DataDef NiceDataSig (niceAxioms DataBlock) r x tel (Just t) Nothing
           <*> nice ds
    niceDataSig _ _ _ = __IMPOSSIBLE__

    niceRecord :: PositivityCheck -> Declaration -> [Declaration] ->
                  Nice [NiceDeclaration]
    niceRecord pc (Record r x i e c tel t cs) ds = do
      t <- defaultTypeSig (RecName pc $ parameters tel) x t
      c <- traverse (\(cname, cinst) -> do fix <- getFixity cname; return (ThingWithFixity cname fix, cinst)) c
      (++) <$> dataOrRec pc (\x1 x2 x3 x4 -> RecDef x1 x2 x3 x4 i e c) NiceRecSig
                 niceDeclarations r x tel t (Just cs)
           <*> nice ds
    niceRecord _ _ _ = __IMPOSSIBLE__

    niceRecordSig :: PositivityCheck -> Declaration -> [Declaration] ->
                     Nice [NiceDeclaration]
    niceRecordSig pc (RecordSig r x tel t) ds = do
      addLoneSig x (RecName pc $ parameters tel)
      fx <- getFixity x
      (NiceRecSig r fx PublicAccess x tel t pc :) <$> nice ds
    niceRecordSig _ _ _ = __IMPOSSIBLE__

    -- We could add a default type signature here, but at the moment we can't
    -- infer the type of a record or datatype, so better to just fail here.
    defaultTypeSig :: DataRecOrFun -> Name -> Maybe Expr -> Nice (Maybe Expr)
    defaultTypeSig k x t@Just{} = return t
    defaultTypeSig k x Nothing  = do
      mk <- getSig x
      case mk of
        Nothing -> throwError $ MissingDataSignature x
        Just k' | k == k'       -> Nothing <$ removeLoneSig x
                | sameKind k k' -> throwError $ WrongParameters x
                | otherwise     -> throwError $ WrongDefinition x k' k

    dataOrRec :: forall a .
                 PositivityCheck ->
                 (Range -> Fixity' -> IsAbstract -> Name -> [LamBinding] ->
                   PositivityCheck -> [NiceConstructor] -> NiceDeclaration) ->
                 (Range -> Fixity' -> Access -> Name -> [LamBinding] -> Expr ->
                   PositivityCheck -> NiceDeclaration) ->
                 ([a] -> Nice [NiceDeclaration]) ->
                 Range ->
                 Name ->
                 [LamBinding] ->
                 Maybe Expr ->
                 Maybe [a] ->
                 Nice [NiceDeclaration]
    dataOrRec pc mkDef mkSig niceD r x tel mt mcs = do
      mds <- traverse niceD mcs
      f   <- getFixity x
      return $ catMaybes $
        [ mt <&> \ t -> mkSig (fuseRange x t) f PublicAccess x tel t pc
        , mkDef r f ConcreteDef x (concatMap dropType tel) pc <$> mds
        ]
      where
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
        return [ Axiom (getRange d) fx PublicAccess NotInstanceDef rel x t ]
      Field i x argt -> do
        fx <- getFixity x
        return [ NiceField (getRange d) i fx PublicAccess ConcreteDef x argt ]
      InstanceB r decls -> do
        instanceBlock r =<< niceAxioms InstanceBlock decls
      Pragma p@(RewritePragma r _) -> do
        return [ NicePragma r p ]
      _ -> throwError $ WrongContentBlock b $ getRange d

    toPrim :: NiceDeclaration -> NiceDeclaration
    toPrim (Axiom r f a i rel x t) = PrimitiveFunction r f a ConcreteDef x t
    toPrim _                     = __IMPOSSIBLE__

    -- Create a function definition.
    mkFunDef info termCheck x mt ds0 = do
      cs <- mkClauses x (expandEllipsis ds0) False
      f  <- getFixity x
      return [ FunSig (fuseRange x t) f PublicAccess NotInstanceDef NotMacroDef info termCheck x t
             , FunDef (getRange ds0) ds0 f ConcreteDef termCheck x cs ]
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
      d : expand p ps ds
      where
        expand _ _ [] = []
        expand p ps (d@(Pragma (CatchallPragma r)) : ds) = d : expand p ps ds
        expand p ps (FunClause (Ellipsis r ps' eqs []) rhs wh ca : ds) =
          FunClause (LHS (setRange r p) ((setRange r ps) ++ ps') eqs []) rhs wh ca : expand p ps ds
        expand p ps (FunClause (Ellipsis r ps' eqs es) rhs wh ca : ds) =
          FunClause (LHS (setRange r p) ((setRange r ps) ++ ps') eqs es) rhs wh ca : expand p (ps ++ ps') ds
        expand p ps (d@(FunClause (LHS _ _ _ []) _ _ _) : ds) =
          d : expand p ps ds
        expand _ _ (d@(FunClause (LHS p ps _ (_ : _)) _ _ _) : ds) =
          d : expand p ps ds
        expand _ _ (_ : ds) = __IMPOSSIBLE__
    expandEllipsis (_ : ds) = __IMPOSSIBLE__

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

    removeSingletonRawAppP :: Pattern -> Pattern
    removeSingletonRawAppP p =
      case p of
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
        let tcs = map termCheck ds
        tc <- combineTermChecks r tcs

        let pc :: PositivityCheck
            pc = all positivityCheckOldMutual ds

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
        termCheck (FunSig _ _ _ _ _ _ tc _ _)        = tc
        termCheck (FunDef _ _ _ _ tc _ _)            = tc
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
        positivityCheckOldMutual (DataDef _ _ _ _ _ pc _)      = pc
        positivityCheckOldMutual (NiceDataSig _ _ _ _ _ _ pc)  = pc
        positivityCheckOldMutual (NiceMutual _ _ pc _)         = __IMPOSSIBLE__
        positivityCheckOldMutual (NiceRecSig _ _ _ _ _ _ pc)   = pc
        positivityCheckOldMutual (RecDef _ _ _ _ _ _ _ _ pc _) = pc
        positivityCheckOldMutual _                             = True

        -- A mutual block cannot have a measure,
        -- but it can skip termination check.

    abstractBlock _ [] = return []
    abstractBlock r ds = do
      let (ds', anyChange) = runChange $ mapM mkAbstract ds
          inherited        = r == noRange
          -- hack to avoid failing on inherited abstract blocks in where clauses
      if anyChange || inherited then return ds' else throwError $ UselessAbstract r

    -- Make a declaration abstract
    mkAbstract :: Updater NiceDeclaration
    mkAbstract d =
      case d of
        NiceMutual r termCheck pc ds     -> NiceMutual r termCheck pc <$> mapM mkAbstract ds
        FunDef r ds f a tc x cs          -> (\ a -> FunDef r ds f a tc x) <$> setAbstract a <*> mapM mkAbstractClause cs
        DataDef r f a x ps pc cs         -> (\ a -> DataDef r f a x ps pc) <$> setAbstract a <*> mapM mkAbstract cs
        RecDef r f a x i e c ps pc cs    -> (\ a -> RecDef r f a x i e c ps pc) <$> setAbstract a <*> mapM mkAbstract cs
        NiceFunClause r p a termCheck catchall d  -> (\ a -> NiceFunClause r p a termCheck catchall d) <$> setAbstract a
        -- no effect on fields or primitives, the InAbstract field there is unused
        NiceField r i f p _ x e          -> return $ NiceField r i f p AbstractDef x e
        PrimitiveFunction r f p _ x e    -> return $ PrimitiveFunction r f p AbstractDef x e
        NiceUnquoteDecl r f p i _ t x e  -> return $ NiceUnquoteDecl r f p i AbstractDef t x e
        NiceUnquoteDef r f p _ t x e     -> return $ NiceUnquoteDef r f p AbstractDef t x e
        NiceModule{}                     -> return d
        NiceModuleMacro{}                -> return d
        Axiom{}                          -> return d
        NicePragma{}                     -> return d
        NiceOpen{}                       -> return d
        NiceImport{}                     -> return d
        FunSig{}                         -> return d
        NiceRecSig{}                     -> return d
        NiceDataSig{}                    -> return d
        NicePatternSyn{}                 -> return d

    setAbstract :: Updater IsAbstract
    setAbstract a = case a of
      AbstractDef -> return a
      ConcreteDef -> dirty $ AbstractDef

    mkAbstractClause :: Updater Clause
    mkAbstractClause (Clause x catchall lhs rhs wh with) = do
        wh <- mkAbstractWhere wh
        Clause x catchall lhs rhs wh <$> mapM mkAbstractClause with

    mkAbstractWhere :: Updater WhereClause
    mkAbstractWhere  NoWhere         = return $ NoWhere
    mkAbstractWhere (AnyWhere ds)    = dirty $ AnyWhere [Abstract noRange ds]
    mkAbstractWhere (SomeWhere m ds) = dirty $SomeWhere m [Abstract noRange ds]

    privateBlock _ [] = return []
    privateBlock r ds = do
      let (ds', anyChange) = runChange $ mapM mkPrivate ds
      if anyChange then return ds' else throwError $ UselessPrivate r

    -- Make a declaration private.
    -- Andreas, 2012-11-17:
    -- Mark computation 'dirty' if there was a declaration that could be privatized.
    -- If no privatization is taking place, we want to complain about 'UselessPrivate'.
    -- Alternatively, we could only dirty if a non-private thing was privatized.
    -- Then, nested 'private's would sometimes also be complained about.
    mkPrivate :: Updater NiceDeclaration
    mkPrivate d =
      case d of
        Axiom r f p i rel x e            -> (\ p -> Axiom r f p i rel x e) <$> setPrivate p
        NiceField r i f p a x e          -> (\ p -> NiceField r i f p a x e) <$> setPrivate p
        PrimitiveFunction r f p a x e    -> (\ p -> PrimitiveFunction r f p a x e) <$> setPrivate p
        NiceMutual r termCheck pc ds     -> NiceMutual r termCheck pc <$> mapM mkPrivate ds
        NiceModule r p a x tel ds        -> (\ p -> NiceModule r p a x tel ds) <$> setPrivate p
        NiceModuleMacro r p x ma op is   -> (\ p -> NiceModuleMacro r p x ma op is) <$> setPrivate p
        FunSig r f p i m rel tc x e      -> (\ p -> FunSig r f p i m rel tc x e) <$> setPrivate p
        NiceRecSig r f p x ls t pc       -> (\ p -> NiceRecSig r f p x ls t pc) <$> setPrivate p
        NiceDataSig r f p x ls t pc      -> (\ p -> NiceDataSig r f p x ls t pc) <$> setPrivate p
        NiceFunClause r p a termCheck catchall d -> (\ p -> NiceFunClause r p a termCheck catchall d) <$> setPrivate p
        NiceUnquoteDecl r f p i a t x e  -> (\ p -> NiceUnquoteDecl r f p i a t x e) <$> setPrivate p
        NiceUnquoteDef r f p a t x e     -> (\ p -> NiceUnquoteDef r f p a t x e) <$> setPrivate p
        NicePragma _ _                   -> return $ d
        NiceOpen _ _ _                   -> return $ d
        NiceImport _ _ _ _ _             -> return $ d
        FunDef{}                         -> return $ d
        DataDef{}                        -> return $ d
        RecDef{}                         -> return $ d
        NicePatternSyn _ _ _ _ _         -> return $ d

    setPrivate :: Updater Access
    setPrivate p = case p of
      PrivateAccess -> return p
      _             -> dirty $ PrivateAccess

    -- Andreas, 2012-11-22: Q: is this necessary?
    -- Are where clauses not always private?
    mkPrivateClause :: Updater Clause
    mkPrivateClause (Clause x catchall lhs rhs wh with) = do
        wh <- mkPrivateWhere wh
        Clause x catchall lhs rhs wh <$> mapM mkPrivateClause with

    mkPrivateWhere :: Updater WhereClause
    mkPrivateWhere  NoWhere         = return $ NoWhere
    mkPrivateWhere (AnyWhere ds)    = dirty  $ AnyWhere [Private (getRange ds) ds]
    mkPrivateWhere (SomeWhere m ds) = dirty  $ SomeWhere m [Private (getRange ds) ds]

    instanceBlock _ [] = return []
    instanceBlock r ds = do
      let (ds', anyChange) = runChange $ mapM mkInstance ds
      if anyChange then return ds' else throwError $ UselessInstance r

    -- Make a declaration eligible for instance search.
    mkInstance :: Updater NiceDeclaration
    mkInstance d =
      case d of
        Axiom r f p i rel x e            -> (\ i -> Axiom r f p i rel x e) <$> setInstance i
        FunSig r f p i m rel tc x e      -> (\ i -> FunSig r f p i m rel tc x e) <$> setInstance i
        NiceUnquoteDecl r f p i a tc x e -> (\ i -> NiceUnquoteDecl r f p i a tc x e) <$> setInstance i
        NiceMutual{}                     -> return d
        NiceFunClause{}                  -> return d
        FunDef{}                         -> return d
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
        FunSig r f p i _ rel tc x e -> return $ FunSig r f p i MacroDef rel tc x e
        FunDef{}                    -> return d
        _                           -> throwError (BadMacroDef d)

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
    mergeFixites name (Fixity' f1 s1) (Fixity' f2 s2) = Fixity' f s
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
    compatible (Fixity' f1 s1) (Fixity' f2 s2) = (f1 == noFixity || f2 == noFixity) &&
                                                 (s1 == noNotation || s2 == noNotation)

-- | While 'Fixities' is not a monoid under disjoint union (which might fail),
--   we get the monoid instance for the monadic @Nice Fixities@ which propagates
--   the first error.
instance Monoid (Nice Fixities) where
  mempty        = return $ Map.empty
  mappend c1 c2 = plusFixities ==<< (c1, c2)

-- | Get the fixities from the current block.
--   Doesn't go inside modules and where blocks.
--   The reason for this is that fixity declarations have to appear at the same
--   level (or possibly outside an abstract or mutual block) as its target
--   declaration.
fixities :: [Declaration] -> Nice Fixities
fixities = foldMap $ \ d -> case d of
  -- These declarations define fixities:
  Syntax x syn    -> return $ Map.singleton x $ Fixity' noFixity syn
  Infix  f xs     -> return $ Map.fromList $ map (,Fixity' f noNotation) xs
  -- We look into these blocks:
  Mutual    _ ds' -> fixities ds'
  Abstract  _ ds' -> fixities ds'
  Private   _ ds' -> fixities ds'
  InstanceB _ ds' -> fixities ds'
  Macro     _ ds' -> fixities ds'
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


-- Andreas, 2012-04-07
-- The following function is only used twice, for building a Let, and for
-- printing an error message.

-- | (Approximately) convert a 'NiceDeclaration' back to a 'Declaration'.
notSoNiceDeclaration :: NiceDeclaration -> Declaration
notSoNiceDeclaration d =
  case d of
    Axiom _ _ _ _ rel x e            -> TypeSig rel x e
    NiceField _ i _ _ _ x argt       -> Field i x argt
    PrimitiveFunction r _ _ _ x e    -> Primitive r [TypeSig defaultArgInfo x e]
    NiceMutual r _ _ ds              -> Mutual r $ map notSoNiceDeclaration ds
    NiceModule r _ _ x tel ds        -> Module r x tel ds
    NiceModuleMacro r _ x ma o dir   -> ModuleMacro r x ma o dir
    NiceOpen r x dir                 -> Open r x dir
    NiceImport r x as o dir          -> Import r x as o dir
    NicePragma _ p                   -> Pragma p
    NiceRecSig r _ _ x bs e _        -> RecordSig r x bs e
    NiceDataSig r _ _ x bs e _       -> DataSig r Inductive x bs e
    NiceFunClause _ _ _ _ _ d        -> d
    FunSig _ _ _ _ _ rel tc x e      -> TypeSig rel x e
    FunDef r [d] _ _ _ _ _           -> d
    FunDef r ds _ _ _ _ _            -> Mutual r ds -- Andreas, 2012-04-07 Hack!
    DataDef r _ _ x bs _ cs          -> Data r Inductive x bs Nothing $ map notSoNiceDeclaration cs
    RecDef r _ _ x i e c bs _ ds     -> Record r x i e (unThing <$> c) bs Nothing $ map notSoNiceDeclaration ds
      where unThing (ThingWithFixity c _, inst) = (c, inst)
    NicePatternSyn r _ n as p        -> PatternSyn r n as p
    NiceUnquoteDecl r _ _ _ _ _ x e  -> UnquoteDecl r x e
    NiceUnquoteDef r _ _ _ _ x e     -> UnquoteDef r x e

-- | Has the 'NiceDeclaration' a field of type 'IsAbstract'?
niceHasAbstract :: NiceDeclaration -> Maybe IsAbstract
niceHasAbstract d =
  case d of
    Axiom{}                         -> Nothing
    NiceField _ _ _ _ a _ _         -> Just a
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
    FunDef _ _ _ a _ _ _            -> Just a
    DataDef _ _ a _ _ _ _           -> Just a
    RecDef _ _ a _ _ _ _ _ _ _      -> Just a
    NicePatternSyn{}                -> Nothing
    NiceUnquoteDecl _ _ _ _ a _ _ _ -> Just a
    NiceUnquoteDef _ _ _ a _ _ _    -> Just a
