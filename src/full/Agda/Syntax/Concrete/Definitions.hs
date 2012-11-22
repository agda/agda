{-# LANGUAGE CPP, PatternGuards, DeriveDataTypeable #-}

module Agda.Syntax.Concrete.Definitions
    ( NiceDeclaration(..)
    , NiceConstructor, NiceTypeSignature
    , Clause(..)
    , DeclarationException(..)
    , Nice, runNice
    , niceDeclarations
    , notSoNiceDeclaration
    ) where

import Control.Arrow ((***), (&&&))
import Control.Applicative
import Data.Typeable (Typeable)
import Data.Foldable hiding (concatMap, mapM_, notElem, elem, all)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Error
import Control.Monad.State
import Data.List as List
import Data.Maybe
import Data.Traversable (traverse)

import Debug.Trace (trace)
import Agda.Syntax.Concrete
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete.Pretty
import Agda.Utils.Pretty
import Agda.Utils.List (mhead, isSublistOf)
import Agda.Utils.Monad
import Agda.Utils.Update

#include "../../undefined.h"
import Agda.Utils.Impossible

import Control.Applicative
import Control.Monad.Error
import Data.Char

import Debug.Trace

{--------------------------------------------------------------------------
    Types
 --------------------------------------------------------------------------}

{-| The nice declarations. No fixity declarations and function definitions are
    contained in a single constructor instead of spread out between type
    signatures and clauses. The @private@, @postulate@, and @abstract@
    modifiers have been distributed to the individual declarations.
-}
data NiceDeclaration
        = Axiom Range Fixity' Access Relevance Name Expr
            -- ^ Axioms and functions can be declared irrelevant.
        | NiceField Range Fixity' Access IsAbstract Name (Arg Expr)
        | PrimitiveFunction Range Fixity' Access IsAbstract Name Expr
        | NiceMutual Range TerminationCheck [NiceDeclaration]
        | NiceModule Range Access IsAbstract QName Telescope [Declaration]
        | NiceModuleMacro Range Access Name ModuleApplication OpenShortHand ImportDirective
        | NiceOpen Range QName ImportDirective
        | NiceImport Range QName (Maybe AsName) OpenShortHand ImportDirective
        | NicePragma Range Pragma
        | NiceRecSig Range Fixity' Access Name [LamBinding] Expr
        | NiceDataSig Range Fixity' Access Name [LamBinding] Expr
        | NiceFunClause Range Access IsAbstract TerminationCheck Declaration
          -- ^ a uncategorized function clause, could be a function clause
          --   without type signature or a pattern lhs (e.g. for irrefutable let)x
        | FunSig Range Fixity' Access Relevance TerminationCheck Name Expr
        | FunDef  Range [Declaration] Fixity' IsAbstract TerminationCheck HasTypeSig Name [Clause] -- ^ block of function clauses (we have seen the type signature before)
        | DataDef Range Fixity' IsAbstract Name [LamBinding] [NiceConstructor]
        | RecDef Range Fixity' IsAbstract Name (Maybe Induction) (Maybe (ThingWithFixity Name)) [LamBinding] [NiceDeclaration]
        | NicePatternSyn Range Fixity' Name [Name] Pattern
    deriving (Typeable, Show)

-- | Termination check? (Default = True).
type TerminationCheck = Bool

-- | Only 'Axiom's.
type NiceConstructor = NiceTypeSignature

-- | Only 'Axiom's.
type NiceTypeSignature  = NiceDeclaration

-- | One clause in a function definition. There is no guarantee that the 'LHS'
--   actually declares the 'Name'. We will have to check that later.
data Clause = Clause Name LHS RHS WhereClause [Clause]
    deriving (Typeable, Show)

-- | The exception type.
data DeclarationException
        = MultipleFixityDecls [(Name, [Fixity'])]
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
        | AmbiguousFunClauses LHS [Name] -- ^ in a mutual block, a clause could belong to any of the @[Name]@ type signatures
        | InvalidNoTerminationCheckPragma Range
    deriving (Typeable)

instance HasRange DeclarationException where
    getRange (MultipleFixityDecls xs)      = getRange (fst $ head xs)
    getRange (MissingDefinition x)         = getRange x
    getRange (MissingWithClauses x)        = getRange x
    getRange (MissingTypeSignature x)      = getRange x
    getRange (MissingDataSignature x)      = getRange x
    getRange (WrongDefinition x k k')      = getRange x
    getRange (WrongParameters x)           = getRange x
    getRange (AmbiguousFunClauses lhs xs)  = getRange lhs
    getRange (NotAllowedInMutual x)        = getRange x
    getRange (UnknownNamesInFixityDecl xs) = getRange . head $ xs
    getRange (Codata r)                    = r
    getRange (DeclarationPanic _)          = noRange
    getRange (UselessPrivate r)            = r
    getRange (UselessAbstract r)           = r
    getRange (InvalidNoTerminationCheckPragma r) = r

instance HasRange NiceDeclaration where
  getRange (Axiom r _ _ _ _ _)             = r
  getRange (NiceField r _ _ _ _ _)         = r
  getRange (NiceMutual r _ _)              = r
  getRange (NiceModule r _ _ _ _ _)        = r
  getRange (NiceModuleMacro r _ _ _ _ _)   = r
  getRange (NiceOpen r _ _)                = r
  getRange (NiceImport r _ _ _ _)          = r
  getRange (NicePragma r _)                = r
  getRange (PrimitiveFunction r _ _ _ _ _) = r
  getRange (FunSig r _ _ _ _ _ _)          = r
  getRange (FunDef r _ _ _ _ _ _ _)        = r
  getRange (DataDef r _ _ _ _ _)           = r
  getRange (RecDef r _ _ _ _ _ _ _)        = r
  getRange (NiceRecSig r _ _ _ _ _)        = r
  getRange (NiceDataSig r _ _ _ _ _)       = r
  getRange (NicePatternSyn r _ _ _ _)      = r
  getRange (NiceFunClause r _ _ _ _)       = r

instance Error DeclarationException where
  noMsg  = strMsg ""
  strMsg = DeclarationPanic

instance Show DeclarationException where
  show (MultipleFixityDecls xs) = show $
    sep [ fsep $ pwords "Multiple fixity declarations for"
        , vcat $ map f xs
        ]
      where
        f (x, fs) = pretty x <> text ":" <+> fsep (map (text . show) fs)
  show (MissingDefinition x) = show $ fsep $
    pwords "Missing definition for" ++ [pretty x]
  show (MissingWithClauses x) = show $ fsep $
    pwords "Missing with-clauses for function" ++ [pretty x]
  show (MissingTypeSignature x) = show $ fsep $
    pwords "Missing type signature for left hand side" ++ [pretty x]
  show (MissingDataSignature x) = show $ fsep $
    pwords "Missing type signature for " ++ [pretty x]
  show (WrongDefinition x k k') = show $ fsep $ pretty x :
    pwords ("has been declared as a " ++ show k ++
      ", but is being defined as a " ++ show k')
  show (WrongParameters x) = show $ fsep $
    pwords "List of parameters does not match previous signature for" ++ [pretty x]
  show (AmbiguousFunClauses lhs xs) = show $ fsep $
    pwords "More than one matching type signature for left hand side" ++ [pretty lhs] ++
    pwords "it could belong to any of:" ++ map pretty xs
  show (UnknownNamesInFixityDecl xs) = show $ fsep $
    pwords "Names out of scope in fixity declarations:" ++ map pretty xs
  show (UselessPrivate _)      = show $ fsep $
    pwords "Using private here has no effect. Private applies only to declarations that introduce new identifiers into the module, like type signatures and data, record, and module declarations."
  show (UselessAbstract _)      = show $ fsep $
    pwords "Using abstract here has no effect. Abstract applies only definitions like data definitions, record type definitions and function clauses."
  show (InvalidNoTerminationCheckPragma _) = show $ fsep $
    pwords "The NO_TERMINATION_CHECK pragma can only preceed a mutual block or a function definition."
  show (NotAllowedInMutual nd) = show $ fsep $
    [text $ decl nd] ++ pwords "are not allowed in mutual blocks"
    where
      decl (Axiom{})             = "Postulates"
      decl (NiceField{})         = "Fields"
      decl (NiceMutual{})        = "Mutual blocks"
      decl (NiceModule{})        = "Modules"
      decl (NiceModuleMacro{})   = "Modules"
      decl (NiceOpen{})          = "Open declarations"
      decl (NiceImport{})        = "Import statements"
      decl (NicePragma{})        = "Pragmas"
      decl (PrimitiveFunction{}) = "Primitive declarations"
      decl (NicePatternSyn{})    = "Pattern synonyms"
      decl _ = __IMPOSSIBLE__
  show (Codata _) =
    "The codata construction has been removed. " ++
    "Use the INFINITY builtin instead."
  show (DeclarationPanic s) = s

{--------------------------------------------------------------------------
    The niceifier
 --------------------------------------------------------------------------}

data InMutual
  = InMutual    -- ^ we are nicifying a mutual block
  | NotInMutual -- ^ we are nicifying decls not in a mutual block
    deriving (Eq, Show)

-- | The kind of the forward declaration, remembering the parameters.
data DataRecOrFun
  = DataName Params           -- ^ name of a data with parameters
  | RecName  Params           -- ^ name of a record with parameters
  | FunName  TerminationCheck -- ^ name of a function
  deriving (Eq, Ord)

type Params = [Hiding]

instance Show DataRecOrFun where
  show (DataName n) = "data type" --  "with " ++ show n ++ " visible parameters"
  show (RecName n)  = "record type" -- "with " ++ show n ++ " visible parameters"
  show (FunName{})  = "function"

isFunName :: DataRecOrFun -> Bool
isFunName (FunName{}) = True
isFunName _           = False

sameKind :: DataRecOrFun -> DataRecOrFun -> Bool
sameKind DataName{} DataName{} = True
sameKind RecName{} RecName{} = True
sameKind FunName{} FunName{} = True
sameKind _ _ = False

terminationCheck :: DataRecOrFun -> Bool
terminationCheck (FunName tc) = tc
terminationCheck _            = True

type LoneSigs = [(DataRecOrFun, Name)]
data NiceEnv = NiceEnv
  { loneSigs :: LoneSigs -- ^ lone type signatures that wait for their definition
  , fixs     :: Map Name Fixity'
  }

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { loneSigs = []
  , fixs     = Map.empty
  }

type Nice = StateT NiceEnv (Either DeclarationException)

{- Andreas, 2012-04-30 MOVED to Utils.Monad
localState :: Nice a -> Nice a
localState m = bracket get put (const m)
-}

addLoneSig :: DataRecOrFun -> Name -> Nice ()
addLoneSig k x = modify $ \ niceEnv -> niceEnv { loneSigs = (k, x) : loneSigs niceEnv }

removeLoneSig :: Name -> Nice ()
removeLoneSig x = modify $ \ niceEnv ->
  niceEnv { loneSigs = filter (\ (k', x') -> x /= x') $ loneSigs niceEnv }

-- | Search for forward type signature that
getSig :: Name -> Nice (Maybe DataRecOrFun)
getSig n = gets $ fmap fst . List.find (\ (k, x) -> x == n) . loneSigs

noLoneSigs :: Nice Bool
noLoneSigs = gets $ null . loneSigs

-- | Ensure that all forward declarations have been given a definition.
checkLoneSigs :: LoneSigs -> Nice ()
checkLoneSigs xs =
  case xs of
    []       -> return ()
    (_, x):_ -> throwError $ MissingDefinition x

getFixity :: Name -> Nice Fixity'
getFixity x = gets $ Map.findWithDefault defaultFixity' x . fixs

runNice :: Nice a -> Either DeclarationException a
runNice nice = nice `evalStateT` initNiceEnv

data DeclKind
  = LoneSig DataRecOrFun Name
  | LoneDef DataRecOrFun Name
  | Alias Bool -- ^ A simple definition @x = e@ without type signature.
               --   Should we check termination?
  | OtherDecl

declKind (FunSig _ _ _ _ tc x _)      = LoneSig (FunName tc) x
declKind (NiceRecSig _ _ _ x pars _)  = LoneSig (RecName $ parameters pars) x
declKind (NiceDataSig _ _ _ x pars _) = LoneSig (DataName $ parameters pars) x
declKind (FunDef _ _ _ _ tc HasTypeSig x _) = LoneDef (FunName tc) x
declKind (FunDef _ _ _ _ tc NoTypeSig{} x _) = Alias tc
declKind (DataDef _ _ _ x pars _)     = LoneDef (DataName $ parameters pars) x
declKind (RecDef _ _ _ x _ _ pars _)  = LoneDef (RecName $ parameters pars) x
declKind _                            = OtherDecl

-- | Compute visible parameters of a data or record signature or definition.
parameters :: [LamBinding] -> Params
parameters = List.concat . List.map numP where
  numP (DomainFree h _ _) = [h]
  numP (DomainFull (TypedBindings _ (Arg h _ (TBind _ xs _)))) = List.replicate (length xs) h
  numP (DomainFull (TypedBindings _ (Arg _ _ (TNoBind{})))) =  __IMPOSSIBLE__

{- OLD:

-- | Compute number of visible parameters of a data or record signature or definition.
numberOfPars :: [LamBinding] -> Params
numberOfPars = List.sum . List.map numP where
  numP (DomainFree NotHidden _ _) = 1
  numP (DomainFull (TypedBindings _ (Arg NotHidden _ (TBind _ xs _)))) = length xs
  numP (DomainFull (TypedBindings _ (Arg _ _ (TNoBind{})))) =  __IMPOSSIBLE__
  numP _ = 0  -- hidden / instance argument
-- | Compute number of parameters of a data or record signature or definition.
numberOfPars :: [LamBinding] -> Int
numberOfPars = List.sum . List.map numP where
  numP (DomainFree{}) = 1
  numP (DomainFull (TypedBindings _ arg)) = nP $ unArg arg where
    nP (TBind _ xs _) = length xs
    nP (TNoBind _)    = __IMPOSSIBLE__
-}

niceDeclarations :: [Declaration] -> Nice [NiceDeclaration]
niceDeclarations ds = do
  fixs <- fixities ds
  case Map.keys fixs \\ concatMap declaredNames ds of
    []  -> localState $ do
      put $ initNiceEnv { fixs = fixs }
      ds <- nice ds
      checkLoneSigs =<< gets loneSigs
      modify $ \s -> s { loneSigs = [] }
      inferMutualBlocks ds
    xs  -> throwError $ UnknownNamesInFixityDecl xs
  where
    -- Compute the names defined in a declaration
    declaredNames :: Declaration -> [Name]
    declaredNames d = case d of
      TypeSig _ x _                                -> [x]
      Field x _                                    -> [x]
      FunClause (LHS p [] _ _) _ _
        | IdentP (QName x) <- removeSingletonRawAppP p -> [x]
      FunClause{}                                  -> []
      DataSig _ _ x _ _                            -> [x]
      Data _ _ x _ _ cs                            -> x : concatMap declaredNames cs
      RecordSig _ x _ _                            -> [x]
      Record _ x _ c _ _ _                         -> x : foldMap (:[]) c
      Infix _ _                                    -> []
      Syntax _ _                                   -> []
      PatternSyn _ x _ _                           -> [x]
      Mutual _ ds                                  -> concatMap declaredNames ds
      Abstract _ ds                                -> concatMap declaredNames ds
      Private _ ds                                 -> concatMap declaredNames ds
      Postulate _ ds                               -> concatMap declaredNames ds
      Primitive _ ds                               -> concatMap declaredNames ds
      Open{}                                       -> []
      Import{}                                     -> []
      ModuleMacro{}                                -> []
      Module{}                                     -> []
      Pragma{}                                     -> []

    inferMutualBlocks :: [NiceDeclaration] -> Nice [NiceDeclaration]
    inferMutualBlocks [] = return []
    inferMutualBlocks (d : ds) =
      case declKind d of
        OtherDecl   -> (d :) <$> inferMutualBlocks ds
        Alias tc    -> (NiceMutual (getRange d) tc [d] :) <$> inferMutualBlocks ds
        LoneDef _ x -> __IMPOSSIBLE__
        LoneSig k x -> do
          addLoneSig k x
          (tc, (ds0, ds1)) <- untilAllDefined (terminationCheck k) ds

          -- Record modules are, for performance reasons, not always
          -- placed in mutual blocks.
          let prefix = case (d, ds0) of
                (NiceRecSig{}, [r@RecDef{}]) -> ([d, r] ++)
                _                            ->
                  (NiceMutual (getRange (d : ds0)) tc (d : ds0) :)
          prefix <$> inferMutualBlocks ds1
      where
        untilAllDefined :: TerminationCheck
          -> [NiceDeclaration]
          -> Nice (TerminationCheck, ([NiceDeclaration], [NiceDeclaration]))
        untilAllDefined tc ds = do
          done <- noLoneSigs
          if done then return (tc, ([], ds)) else
            case ds of
              []     -> __IMPOSSIBLE__ <$ (checkLoneSigs =<< gets loneSigs)
              d : ds -> case declKind d of
                LoneSig k x -> addLoneSig  k x >> cons d (untilAllDefined (tc && terminationCheck k) ds)
                LoneDef k x -> removeLoneSig x >> cons d (untilAllDefined (tc && terminationCheck k) ds)
                OtherDecl   -> cons d (untilAllDefined tc ds)
          where
            cons d = fmap (id *** (d :) *** id)

    nice :: [Declaration] -> Nice [NiceDeclaration]
    nice [] = return []
    nice (Pragma (NoTerminationCheckPragma r) : ds@(Mutual{} : _)) = do
      ds <- nice ds
      case ds of
        NiceMutual r _ ds' : ds -> return $ NiceMutual r False ds' : ds
        _ -> __IMPOSSIBLE__
    nice (Pragma (NoTerminationCheckPragma r) : d@TypeSig{} : ds) =
      niceTypeSig False d ds
    nice (Pragma (NoTerminationCheckPragma r) : d@FunClause{} : ds) =
      niceFunClause False d ds
    nice (d:ds) = do
      case d of
        TypeSig{} -> niceTypeSig True d ds
        FunClause{} -> niceFunClause True d ds
        Field x t                     -> (++) <$> niceAxioms [ d ] <*> nice ds
        DataSig r CoInductive x tel t -> throwError (Codata r)
        Data r CoInductive x tel t cs -> throwError (Codata r)
        DataSig r Inductive   x tel t -> do
          addLoneSig (DataName $ parameters tel) x
          (++) <$> dataOrRec DataDef NiceDataSig niceAxioms r x tel (Just t) Nothing
               <*> nice ds
        Data r Inductive x tel t cs -> do
          t <- defaultTypeSig (DataName $ parameters tel) x t
          (++) <$> dataOrRec DataDef NiceDataSig niceAxioms r x tel t (Just cs)
               <*> nice ds
        RecordSig r x tel t -> do
          addLoneSig (RecName $ parameters tel) x
          fx <- getFixity x
          (NiceRecSig r fx PublicAccess x tel t :) <$> nice ds
        Record r x i c tel t cs -> do
          t <- defaultTypeSig (RecName $ parameters tel) x t
          c <- traverse (\c -> ThingWithFixity c <$> getFixity c) c
          (++) <$> dataOrRec (\x1 x2 x3 x4 -> RecDef x1 x2 x3 x4 i c) NiceRecSig
                             niceDeclarations r x tel t (Just cs)
               <*> nice ds
        Mutual r ds' ->
          (:) <$> (mkOldMutual r =<< nice ds') <*> nice ds

        Abstract r ds' ->
          (++) <$> (abstractBlock r =<< nice ds') <*> nice ds

        Private r ds' ->
          (++) <$> (privateBlock r =<< nice ds') <*> nice ds

        Postulate _ ds' -> (++) <$> niceAxioms ds' <*> nice ds

        Primitive _ ds' -> (++) <$> (map toPrim <$> niceAxioms ds') <*> nice ds

        Module r x tel ds' ->
          (NiceModule r PublicAccess ConcreteDef x tel ds' :) <$> nice ds

        ModuleMacro r x modapp op is ->
          (NiceModuleMacro r PublicAccess x modapp op is :)
            <$> nice ds

        Infix _ _           -> nice ds
        Syntax _ _          -> nice ds
        PatternSyn r n as p -> do
          fx <- getFixity n
          (NicePatternSyn r fx n as p :) <$> nice ds
        Open r x is         -> (NiceOpen r x is :) <$> nice ds
        Import r x as op is -> (NiceImport r x as op is :) <$> nice ds

        Pragma (NoTerminationCheckPragma r) ->
          throwError $ InvalidNoTerminationCheckPragma r
        Pragma p            -> (NicePragma (getRange p) p :) <$> nice ds

    niceFunClause :: TerminationCheck -> Declaration -> [Declaration] -> Nice [NiceDeclaration]
    niceFunClause termCheck d@(FunClause lhs _ _) ds = do
          xs <- gets $ map snd . filter (isFunName . fst) . loneSigs
          -- for each type signature 'x' waiting for clauses, we try
          -- if we have some clauses for 'x'
          fixs <- gets fixs
{- OLD CODE, a bit dense
          case filter (\ (x,(fits,rest)) -> not $ null fits) $
                  map (\ x -> (x, span (couldBeFunClauseOf (Map.lookup x fixs) x) $ d : ds)) xs of
-}
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
              LHS p [] _ _ | IdentP (QName x) <- removeSingletonRawAppP p -> do
                ds <- nice ds
                d  <- mkFunDef Relevant termCheck x Nothing [d] -- fun def without type signature is relevant
                return $ d ++ ds
              -- Subcase: The lhs is a proper pattern.
              -- This could be a let-pattern binding. Pass it on.
              -- A missing type signature error might be raise in ConcreteToAbstract
              _ -> do
                ds <- nice ds
                return $ NiceFunClause (getRange d) PublicAccess ConcreteDef termCheck d : ds

            -- case: clauses match exactly one of the sigs
            [(x,(fits,rest))] -> do
               removeLoneSig x
               cs  <- mkClauses x $ expandEllipsis fits
               ds1 <- nice rest
               fx  <- getFixity x
               d   <- return $ FunDef (getRange fits) fits fx ConcreteDef termCheck HasTypeSig x cs
               return $ d : ds1

            -- case: clauses match more than one sigs (ambiguity)
            l -> throwError $ AmbiguousFunClauses lhs (map fst l) -- "ambiguous function clause; cannot assign it uniquely to one type signature"
    niceFunClause _ _ _ = __IMPOSSIBLE__

    niceTypeSig :: TerminationCheck -> Declaration -> [Declaration] -> Nice [NiceDeclaration]
    niceTypeSig termCheck d@(TypeSig rel x t) ds = do
      fx <- getFixity x
      -- register x as lone type signature, to recognize clauses later
      addLoneSig (FunName termCheck) x
      ds <- nice ds
      return $ FunSig (getRange d) fx PublicAccess rel termCheck x t : ds
    niceTypeSig _ _ _ = __IMPOSSIBLE__

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

    dataOrRec mkDef mkSig niceD r x tel mt mcs = do
      mds <- traverse niceD mcs
      f   <- getFixity x
      return $
         [mkSig (fuseRange x t) f PublicAccess x tel t | Just t <- [mt] ] ++
         [mkDef (getRange x) f ConcreteDef x (concatMap dropType tel) ds | Just ds <- [mds] ]
      where
        dropType (DomainFull (TypedBindings r (Arg h rel TNoBind{}))) =
          [DomainFree h rel $ mkBoundName_ $ noName r]
        dropType (DomainFull (TypedBindings r (Arg h rel (TBind _ xs _)))) =
          map (DomainFree h rel) xs
        dropType b@DomainFree{} = [b]

    -- Translate axioms
    niceAxioms :: [TypeSignature] -> Nice [NiceDeclaration]
    niceAxioms ds = mapM niceAxiom ds

    niceAxiom :: TypeSignature -> Nice NiceDeclaration
    niceAxiom d@(TypeSig rel x t) = do
      fx <- getFixity x
      return $ Axiom (getRange d) fx PublicAccess rel x t
    niceAxiom d@(Field x argt) = do
      fx <- getFixity x
      return $ NiceField (getRange d) fx PublicAccess ConcreteDef x argt
    niceAxiom _ = __IMPOSSIBLE__

    toPrim :: NiceDeclaration -> NiceDeclaration
    toPrim (Axiom r f a rel x t) = PrimitiveFunction r f a ConcreteDef x t
    toPrim _                     = __IMPOSSIBLE__

    -- Create a function definition.
    -- If no type signature was supplied, we create one with a meta variable.
    mkFunDef rel termCheck x mt ds0 = do
      cs <- mkClauses x $ expandEllipsis ds0
      f  <- getFixity x
      let hasSig = maybe (NoTypeSig PublicAccess) (const HasTypeSig) mt
      return $
        maybe [] (\ t -> [ FunSig (fuseRange x t) f PublicAccess rel termCheck x t ]) mt ++
        [ FunDef (getRange ds0) ds0 f ConcreteDef termCheck hasSig x cs ]

{- OLD
    -- Create a function definition.
    -- If no type signature was supplied, we create one with a meta variable.
    mkFunDef rel termCheck x mt ds0 = do
      cs <- mkClauses x $ expandEllipsis ds0
      f  <- getFixity x
      return [ FunSig (fuseRange x t) f PublicAccess rel termCheck x t
             , FunDef (getRange ds0) ds0 f ConcreteDef termCheck x cs ]
        where
          t = case mt of
                Just t  -> t
                Nothing -> underscore (getRange x)

    underscore r = Underscore r Nothing
-}

    expandEllipsis :: [Declaration] -> [Declaration]
    expandEllipsis [] = []
    expandEllipsis (d@(FunClause Ellipsis{} _ _) : ds) =
      d : expandEllipsis ds
    expandEllipsis (d@(FunClause lhs@(LHS p ps _ _) _ _) : ds) =
      d : expand p ps ds
      where
        expand _ _ [] = []
        expand p ps (FunClause (Ellipsis _ ps' eqs []) rhs wh : ds) =
          FunClause (LHS p (ps ++ ps') eqs []) rhs wh : expand p ps ds
        expand p ps (FunClause (Ellipsis _ ps' eqs es) rhs wh : ds) =
          FunClause (LHS p (ps ++ ps') eqs es) rhs wh : expand p (ps ++ ps') ds
        expand p ps (d@(FunClause (LHS _ _ _ []) _ _) : ds) =
          d : expand p ps ds
        expand _ _ (d@(FunClause (LHS p ps _ (_ : _)) _ _) : ds) =
          d : expand p ps ds
        expand _ _ (_ : ds) = __IMPOSSIBLE__
    expandEllipsis (_ : ds) = __IMPOSSIBLE__


    -- Turn function clauses into nice function clauses.
    mkClauses :: Name -> [Declaration] -> Nice [Clause]
    mkClauses _ [] = return []
    mkClauses x (FunClause lhs@(LHS _ _ _ []) rhs wh : cs) =
      (Clause x lhs rhs wh [] :) <$> mkClauses x cs
    mkClauses x (FunClause lhs@(LHS _ ps _ es) rhs wh : cs) = do
      when (null with) $ throwError $ MissingWithClauses x
      wcs <- mkClauses x with
      (Clause x lhs rhs wh wcs :) <$> mkClauses x cs'
      where
        (with, cs') = span subClause cs

        -- A clause is a subclause if the number of with-patterns is
        -- greater or equal to the current number of with-patterns plus the
        -- number of with arguments.
        subClause (FunClause (LHS _ ps' _ _) _ _)      =
          length ps' >= length ps + length es
        subClause (FunClause (Ellipsis _ ps' _ _) _ _) = True
        subClause _                                  = __IMPOSSIBLE__
    mkClauses x (FunClause lhs@Ellipsis{} rhs wh : cs) =
      (Clause x lhs rhs wh [] :) <$> mkClauses x cs   -- Will result in an error later.
    mkClauses _ _ = __IMPOSSIBLE__

    -- for finding clauses for a type sig in mutual blocks
    couldBeFunClauseOf :: Maybe Fixity' -> Name -> Declaration -> Bool
    couldBeFunClauseOf mFixity x (FunClause Ellipsis{} _ _) = True
    couldBeFunClauseOf mFixity x (FunClause (LHS p _ _ _) _ _) =
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
      case (mhead pns, mFixity) of
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

    -- @isFunClauseOf@ is for non-mutual blocks where clauses must follow the
    -- type sig immediately
    isFunClauseOf :: Name -> Declaration -> Bool
    isFunClauseOf x (FunClause Ellipsis{} _ _) = True
    isFunClauseOf x (FunClause (LHS p _ _ _) _ _) =
     -- p is the whole left hand side, excluding "with" patterns and clauses
      case removeSingletonRawAppP p of
        IdentP (QName q)    -> x == q  -- lhs is just an identifier
        _                   -> True
            -- more complicated lhss must come with type signatures, so we just assume
            -- it's part of the current definition
    isFunClauseOf _ _ = False

    removeSingletonRawAppP :: Pattern -> Pattern
    removeSingletonRawAppP (RawAppP _ [p]) = removeSingletonRawAppP p
    removeSingletonRawAppP p               = p

    -- Make an old style mutual block from a list of mutual declarations
    mkOldMutual :: Range -> [NiceDeclaration] -> Nice NiceDeclaration
    mkOldMutual r ds = do
        -- Check that there aren't any missing definitions
        checkLoneSigs loneNames
        -- Check that there are no declarations that aren't allowed in old style mutual blocks
        case [ d | (d, OtherDecl) <- zip ds $ map declKind ds ] of
          []  -> return ()
          (NiceFunClause _ _ _ _ (FunClause lhs _ _)):_ -> throwError $ MissingTypeSignature lhs
          d:_ -> throwError $ NotAllowedInMutual d
        return $ NiceMutual r True $ sigs ++ other  -- termCheck is adjusted later
      where
        -- Pull type signatures to the top
        (sigs, other) = partition isTypeSig ds
        isTypeSig d | LoneSig{} <- declKind d = True
        isTypeSig _ = False

        sigNames  = [ (k, x) | LoneSig k x <- map declKind ds ]
        defNames  = [ (k, x) | LoneDef k x <- map declKind ds ]
        -- compute the set difference with equality just on names
        loneNames = filter (\ (_, x) -> not (List.any (\ (_, x') -> x == x') defNames)) sigNames

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
        NiceMutual r termCheck ds        -> NiceMutual r termCheck <$> mapM mkAbstract ds
        FunDef r ds f a tc hs x cs       -> (\ a -> FunDef r ds f a tc hs x) <$> setAbstract a <*> mapM mkAbstractClause cs
        DataDef r f a x ps cs            -> (\ a -> DataDef r f a x ps)    <$> setAbstract a <*> mapM mkAbstract cs
        RecDef r f a x i c ps cs         -> (\ a -> RecDef r f a x i c ps) <$> setAbstract a <*> mapM mkAbstract cs
        NiceFunClause r p a termCheck d  -> (\ a -> NiceFunClause r p a termCheck d) <$> setAbstract a
        -- no effect on fields or primitives, the InAbstract field there is unused
        NiceField r f p _ x e            -> return $ NiceField r f p AbstractDef x e
        PrimitiveFunction r f p _ x e    -> return $ PrimitiveFunction r f p AbstractDef x e
        NiceModule{}                     -> return $ d
        NiceModuleMacro{}                -> return $ d
        Axiom{}                          -> return $ d
        NicePragma{}                     -> return $ d
        NiceOpen{}                       -> return $ d
        NiceImport{}                     -> return $ d
        FunSig{}                         -> return $ d
        NiceRecSig{}                     -> return $ d
        NiceDataSig{}                    -> return $ d
        NicePatternSyn{}                 -> return $ d

    setAbstract :: Updater IsAbstract
    setAbstract a = case a of
      AbstractDef -> return a
      ConcreteDef -> dirty $ AbstractDef

    mkAbstractClause :: Updater Clause
    mkAbstractClause (Clause x lhs rhs wh with) = do
        wh <- mkAbstractWhere wh
        Clause x lhs rhs wh <$> mapM mkAbstractClause with

    mkAbstractWhere :: Updater WhereClause
    mkAbstractWhere  NoWhere         = return $ NoWhere
    mkAbstractWhere (AnyWhere ds)    = dirty $ AnyWhere [Abstract noRange ds]
    mkAbstractWhere (SomeWhere m ds) = dirty $SomeWhere m [Abstract noRange ds]

{- OLD CODE
    abstractBlock _ [] = return []
    abstractBlock r ds
        -- hack to avoid failing on inherited abstract blocks in where clauses
      | r == noRange           = return $ map mkAbstract ds
      | all uselessAbstract ds = throwError $ UselessAbstract r
      | otherwise              = return $ map mkAbstract ds

    uselessAbstract d = case d of
      FunDef{}  -> False
      DataDef{} -> False
      RecDef{}  -> False
      _         -> True

    -- Make a declaration abstract
    mkAbstract d =
        case d of
            NiceField r f a _ x e            -> NiceField r f a AbstractDef x e
            PrimitiveFunction r f a _ x e    -> PrimitiveFunction r f a AbstractDef x e
            NiceMutual r termCheck ds        -> NiceMutual r termCheck (map mkAbstract ds)
            FunDef r ds f _ tc x cs          -> FunDef r ds f AbstractDef tc x (map mkAbstractClause cs)
            DataDef r f _ x ps cs            -> DataDef r f AbstractDef x ps $ map mkAbstract cs
            RecDef r f _ x i c ps cs         -> RecDef r f AbstractDef x i c ps $ map mkAbstract cs
            NiceFunClause r a _ termCheck d  -> NiceFunClause r a AbstractDef termCheck d
            NiceModule{}                     -> d
            NiceModuleMacro{}                -> d
            Axiom{}                          -> d
            NicePragma{}                     -> d
            NiceOpen{}                       -> d
            NiceImport{}                     -> d
            FunSig{}                         -> d
            NiceRecSig{}                     -> d
            NiceDataSig{}                    -> d
            NicePatternSyn{}                 -> d

    mkAbstractClause (Clause x lhs rhs wh with) =
        Clause x lhs rhs (mkAbstractWhere wh) (map mkAbstractClause with)

    mkAbstractWhere  NoWhere         = NoWhere
    mkAbstractWhere (AnyWhere ds)    = AnyWhere [Abstract noRange ds]
    mkAbstractWhere (SomeWhere m ds) = SomeWhere m [Abstract noRange ds]
-}
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
        Axiom r f p rel x e              -> (\ p -> Axiom r f p rel x e) <$> setPrivate p
        NiceField r f p a x e            -> (\ p -> NiceField r f p a x e) <$> setPrivate p
        PrimitiveFunction r f p a x e    -> (\ p -> PrimitiveFunction r f p a x e) <$> setPrivate p
        NiceMutual r termCheck ds        -> NiceMutual r termCheck <$> mapM mkPrivate ds
        NiceModule r p a x tel ds        -> (\ p -> NiceModule r p a x tel ds) <$> setPrivate p
        NiceModuleMacro r p x ma op is   -> (\ p -> NiceModuleMacro r p x ma op is) <$> setPrivate p
        FunSig r f p rel tc x e          -> (\ p -> FunSig r f p rel tc x e) <$> setPrivate p
        NiceRecSig r f p x ls t          -> (\ p -> NiceRecSig r f p x ls t) <$> setPrivate p
        NiceDataSig r f p x ls t         -> (\ p -> NiceDataSig r f p x ls t) <$> setPrivate p
        NiceFunClause r p a termCheck d  -> (\ p -> NiceFunClause r p a termCheck d) <$> setPrivate p
        FunDef r ds f a tc (NoTypeSig p) x cs -> (\ p -> FunDef r ds f a tc (NoTypeSig p) x) <$> setPrivate p <*> mapM mkPrivateClause cs
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
    mkPrivateClause (Clause x lhs rhs wh with) = do
        wh <- mkPrivateWhere wh
        Clause x lhs rhs wh <$> mapM mkPrivateClause with

    mkPrivateWhere :: Updater WhereClause
    mkPrivateWhere  NoWhere         = return $ NoWhere
    mkPrivateWhere (AnyWhere ds)    = dirty  $ AnyWhere [Private (getRange ds) ds]
    mkPrivateWhere (SomeWhere m ds) = dirty  $ SomeWhere m [Private (getRange ds) ds]

{- OLD CODE, with two functions (uselessPrivate, mkPrivate) to be maintained in sync.

    privateBlock _ [] = return []
    privateBlock r ds
      | all uselessPrivate ds = throwError $ UselessPrivate r
      | otherwise             = return $ map mkPrivate ds

    uselessPrivate d = case d of
      FunDef{}  -> True
      DataDef{} -> True
      RecDef{}  -> True
      _         -> False

    -- Make a declaration private
    mkPrivate d =
        case d of
            Axiom r f _ rel x e              -> Axiom r f PrivateAccess rel x e
            NiceField r f _ a x e            -> NiceField r f PrivateAccess a x e
            PrimitiveFunction r f _ a x e    -> PrimitiveFunction r f PrivateAccess a x e
            NiceMutual r termCheck ds        -> NiceMutual r termCheck (map mkPrivate ds)
            NiceModule r _ a x tel ds        -> NiceModule r PrivateAccess a x tel ds
            NiceModuleMacro r _ x ma op is   -> NiceModuleMacro r PrivateAccess x ma op is
            FunSig r f _ rel tc x e          -> FunSig r f PrivateAccess rel tc x e
            NiceRecSig r f _ x ls t          -> NiceRecSig r f PrivateAccess x ls t
            NiceDataSig r f _ x ls t         -> NiceDataSig r f PrivateAccess x ls t
            NiceFunClause r _ a termCheck d  -> NiceFunClause r PrivateAccess a termCheck d
            NicePragma _ _                   -> d
            NiceOpen _ _ _                   -> d
            NiceImport _ _ _ _ _             -> d
            FunDef{}                         -> d
            DataDef{}                        -> d
            RecDef{}                         -> d
            NicePatternSyn _ _ _ _ _         -> d

    mkPrivateClause (Clause x lhs rhs wh with) =
        Clause x lhs rhs (mkPrivateWhere wh) (map mkPrivateClause with)

    mkPrivateWhere  NoWhere         = NoWhere
    mkPrivateWhere (AnyWhere ds)    = AnyWhere [Private (getRange ds) ds]
    mkPrivateWhere (SomeWhere m ds) = SomeWhere m [Private (getRange ds) ds]
-}

-- | Add more fixities. Throw an exception for multiple fixity declarations.
plusFixities :: Map.Map Name Fixity' -> Map.Map Name Fixity' -> Nice (Map.Map Name Fixity')
plusFixities m1 m2
    | not (null isect) = throwError $ MultipleFixityDecls isect
    | otherwise = return $ Map.unionWithKey mergeFixites m1 m2
    where mergeFixites name (Fixity' f1 s1) (Fixity' f2 s2) = Fixity' f s
              where f | f1 == noFixity = f2
                      | f2 == noFixity = f1
                      | otherwise = __IMPOSSIBLE__
                    s | s1 == noNotation = s2
                      | s2 == noNotation = s1
                      | otherwise = __IMPOSSIBLE__
          isect = [decls x | (x,compat) <- Map.assocs (Map.intersectionWith compatible m1 m2), not compat]

          decls x = (x, map (Map.findWithDefault __IMPOSSIBLE__ x) [m1,m2])
                                -- cpp doesn't know about primes
          compatible (Fixity' f1 s1) (Fixity' f2 s2) = (f1 == noFixity || f2 == noFixity) &&
                                                       (s1 == noNotation || s2 == noNotation)

-- | Get the fixities from the current block. Doesn't go inside /any/ blocks.
--   The reason for this is that fixity declarations have to appear at the same
--   level (or possibly outside an abstract or mutual block) as its target
--   declaration.
fixities :: [Declaration] -> Nice (Map.Map Name Fixity')
fixities (d:ds) = case d of
  Syntax x syn   -> plusFixities (Map.singleton x (Fixity' noFixity syn)) =<< fixities ds
  Infix f xs     -> plusFixities (Map.fromList [ (x,Fixity' f noNotation) | x <- xs ]) =<< fixities ds
  Mutual _ ds'   -> fixities (ds' ++ ds)
  Abstract _ ds' -> fixities (ds' ++ ds)
  Private _ ds'  -> fixities (ds' ++ ds)
  _              -> fixities ds
fixities [] = return $ Map.empty


-- Andreas, 2012-04-07
-- The following function is only used twice, for building a Let, and for
-- printing an error message.
notSoNiceDeclaration :: NiceDeclaration -> Declaration
notSoNiceDeclaration d =
    case d of
      Axiom _ _ _ rel x e              -> TypeSig rel x e
      NiceField _ _ _ _ x argt         -> Field x argt
      PrimitiveFunction r _ _ _ x e    -> Primitive r [TypeSig Relevant x e]
      NiceMutual r _ ds                -> Mutual r $ map notSoNiceDeclaration ds
      NiceModule r _ _ x tel ds        -> Module r x tel ds
      NiceModuleMacro r _ x ma o dir   -> ModuleMacro r x ma o dir
      NiceOpen r x dir                 -> Open r x dir
      NiceImport r x as o dir          -> Import r x as o dir
      NicePragma _ p                   -> Pragma p
      NiceRecSig r _ _ x bs e          -> RecordSig r x bs e
      NiceDataSig r _ _ x bs e         -> DataSig r Inductive x bs e
      NiceFunClause _ _ _ _ d          -> d
      FunSig _ _ _ rel tc x e          -> TypeSig rel x e
      FunDef r [d] _ _ _ _ _ _         -> d
      FunDef r ds _ _ _ _ _ _          -> Mutual r ds -- Andreas, 2012-04-07 Hack!
      DataDef r _ _ x bs cs            -> Data r Inductive x bs Nothing $ map notSoNiceDeclaration cs
      RecDef r _ _ x i c bs ds         -> Record r x i (unThing <$> c) bs Nothing $ map notSoNiceDeclaration ds
        where unThing (ThingWithFixity c _) = c
      NicePatternSyn r _ n as p        -> PatternSyn r n as p

{-
-- Andreas, 2012-03-08 the following function is only used twice,
-- both just on a single declaration.
notSoNiceDeclarations :: [NiceDeclaration] -> [Declaration]
notSoNiceDeclarations = concatMap notNice
  where
    notNice d = case d of
      Axiom _ _ _ rel x e              -> [TypeSig rel x e]
      NiceField _ _ _ _ x argt         -> [Field x argt]
      PrimitiveFunction r _ _ _ x e    -> [Primitive r [TypeSig Relevant x e]]
      NiceMutual _ _ ds                -> concatMap notNice ds
      NiceModule r _ _ x tel ds        -> [Module r x tel ds]
      NiceModuleMacro r _ x ma o dir   -> [ModuleMacro r x ma o dir]
      NiceOpen r x dir                 -> [Open r x dir]
      NiceImport r x as o dir          -> [Import r x as o dir]
      NicePragma _ p                   -> [Pragma p]
      NiceRecSig r _ _ x bs e          -> [RecordSig r x bs e]
      NiceDataSig r _ _ x bs e         -> [DataSig r Inductive x bs e]
      FunSig _ _ _ rel tc x e          -> [TypeSig rel x e]
      FunDef _ ds _ _ _ _ _            -> ds
      DataDef r _ _ x bs cs            -> [Data r Inductive x bs Nothing $ concatMap notNice cs]
      RecDef r _ _ x c bs ds           -> [Record r x (unThing <$> c) bs Nothing $ concatMap notNice ds]
        where unThing (ThingWithFixity c _) = c
      NicePatternSyn r _ n as p        -> [PatternSyn r n as p]
-}
