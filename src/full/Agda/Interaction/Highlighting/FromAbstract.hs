-- | Extract highlighting syntax from abstract syntax.
--
-- Implements one big fold over abstract syntax.

-- {-# OPTIONS_GHC -fwarn-unused-imports #-}  -- Data.Semigroup is redundant in later GHC versions
{-# OPTIONS_GHC -fwarn-unused-binds   #-}

module Agda.Interaction.Highlighting.FromAbstract
  ( Level(..)
  , runHighlighter
  , NameKinds
  ) where

import Prelude hiding (null)

import Control.Applicative
import Control.Monad         ( (<=<), filterM )
import Control.Monad.Reader
  ( MonadReader(..), asks, ReaderT, runReaderT )
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import qualified Data.HashMap.Strict as HMap
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Semigroup       ( Semigroup(..) )          -- for ghc 8.0
import           Data.Void            ( Void )

import           Agda.Interaction.Highlighting.Precise hiding ( singleton )
import qualified Agda.Interaction.Highlighting.Precise as H
import           Agda.Interaction.Highlighting.Range   ( rToR )  -- Range is ambiguous

import           Agda.Syntax.Abstract                ( IsProjP(..) )
import qualified Agda.Syntax.Abstract      as A
import           Agda.Syntax.Common        as Common
import           Agda.Syntax.Concrete                ( FieldAssignment'(..) )
import qualified Agda.Syntax.Concrete.Name as C
import           Agda.Syntax.Info                    ( ModuleInfo(..) )
import qualified Agda.Syntax.Internal      as I
import           Agda.Syntax.Literal
import qualified Agda.Syntax.Position      as P
import           Agda.Syntax.Position                ( Range, HasRange, getRange, noRange )
import           Agda.Syntax.Scope.Base
  ( AbstractName(..), AnonymousNumber(..), IsAnonymous(..)
  , ResolvedName(..), exactConName
  )

import Agda.TypeChecking.Monad
  hiding (ModuleInfo, MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as TCM

import           Agda.Utils.FileName
import           Agda.Utils.Function
import           Agda.Utils.Functor
import           Agda.Utils.Impossible
import           Agda.Utils.List                     ( initLast1 )
import           Agda.Utils.List1                    ( List1 )
import qualified Agda.Utils.List1          as List1
import           Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict   as Strict
import           Agda.Utils.Monad
import           Agda.Utils.Pretty
import           Agda.Utils.Singleton

-- | Highlighting levels.

data Level
  = Full
    -- ^ Full highlighting. Should only be used after typechecking has
    --   completed successfully.
  | Partial
    -- ^ Highlighting without disambiguation of overloaded
    --   constructors.

-- Entry point:
-- | Create highlighting info for some piece of syntax.
runHighlighter ::
  Hilite a =>
  SourceToModule -> NameKinds -> Level -> a ->
  TCM HighlightingInfoBuilder
runHighlighter modMap kinds level x =
  runReaderT (hilite x) $
  HiliteEnv
    { hleNameKinds = kinds
    , hleModMap    = modMap
    , hleLevel     = level
    }

-- | Environment of the highlighter.
data HiliteEnv = HiliteEnv
  { hleNameKinds :: NameKinds
      -- ^ A partial function mapping names to 'NameKind's.
  , hleModMap    :: SourceToModule
      -- ^ Maps source file paths to module names.
  , hleLevel :: Level
      -- ^ The highlighting level.
  }

-- | A partial function mapping names to 'NameKind's.
type NameKinds = A.QName -> Maybe NameKind

-- | Highlighting monad.
type HiliteM = ReaderT HiliteEnv TCM

-- | Highlighter.

type Hiliter = HiliteM HighlightingInfoBuilder

instance Monoid Hiliter where
  mempty  = pure mempty
  mappend = (<>)

-- | Traversal to extract highlighting information.

class Hilite a where
  hilite :: a -> Hiliter

  default hilite :: (Foldable t, Hilite b, t b ~ a) => a -> Hiliter
  hilite = foldMap hilite

-- * Generic instances
---------------------------------------------------------------------------

instance Hilite a => Hilite [a]
instance Hilite a => Hilite (List1 a)
instance Hilite a => Hilite (Maybe a)
instance Hilite a => Hilite (WithHiding a)

instance Hilite Void where
  hilite _ = mempty

instance (Hilite a, Hilite b) => Hilite (Either a b) where
  hilite = either hilite hilite

instance (Hilite a, Hilite b) => Hilite (a, b) where
  hilite (a, b) = hilite a <> hilite b

-- * Major syntactic categories
---------------------------------------------------------------------------

-- | Reengineered from the old Geniplate-implemented highlighting extraction.
-- This was the old procedure:
--
-- Traversal over declaration in abstract syntax that collects the
-- following hiliting information:
--
-- [1. @constructorInfo@ (highest prio)]
-- 2. @theRest@ (medium prio)
-- 3. @nameInfo@ (lowest prio)
--
-- @nameInfo@:
--   "All names mentioned in the syntax tree (not bound variables)."
-- For each possibly ambiguous name (QName and AmbiguousQName)
-- that not isExtendedLambdaName,
-- do @hiliteAmbiguous@ (used to be called@generate@).
--
-- @constructorInfo@ (only when highlighting level == Full):
--   "After the code has been type checked more information may be
--   available for overloaded constructors, and
--   generateConstructorInfo takes advantage of this information.
--   Note, however, that highlighting for overloaded constructors is
--   included also in nameInfo."
-- This is not computed by recursion over the abstract syntax,
-- but gets the constructor names stDisambiguatedNames
-- that fall within the bounds of the current declaration.
--
-- @theRest@:
--   Bound variables, dotted patterns, record fields, module names,
--   the "as" and "to" symbols and some other things.
--
-- Here is a table what @theRest@ used to collect:
--
-- ---------------------------------------------------------------------
-- | A.Expr
-- ---------------------------------------------------------------------
-- | getVarAndField (Expr) | A.Var                       | bound
-- | getVarAndField        | A.Rec(Update)               | field
-- | getExpr        (Expr) | A.PatternSyn                | patsyn
-- | getExpr               | A.Macro                     | macro
-- ---------------------------------------------------------------------
-- | A.LetBinding
-- ---------------------------------------------------------------------
-- | getLet                | A.LetBind                   | bound
-- | getLet                | A.LetDeclaredVariable       | bound
-- ---------------------------------------------------------------------
-- | A.LamBinding
-- ---------------------------------------------------------------------
-- | getLam                | A.Binder under A.DomainFree | bound
-- | getTyped              | A.Binder under A.TBind      | bound
-- ---------------------------------------------------------------------
-- | A.Pattern'
-- ---------------------------------------------------------------------
-- | getPattern(Syn)       | A.VarP                      | bound
-- | getPattern(Syn)       | A.AsP                       | bound
-- | getPattern(Syn)       | A.DotP (not isProjP)        | DottedPattern
-- | getPattern(Syn)       | A.RecP                      | field
-- | getPattern(Syn)       | A.PatternSynP               | patsyn
-- ---------------------------------------------------------------------
-- | A.Declaration
-- ---------------------------------------------------------------------
-- | getFieldDecl          | A.Field under A.RecDef      | field
-- | getPatSynArgs         | A.PatternSynDef             | bound
-- | getPragma             | A.BuiltinPragma...          | keyword
-- ---------------------------------------------------------------------
-- | A.NamedArg (polymorphism not supported in geniplate)
-- ---------------------------------------------------------------------
-- | getNamedArg           | NamedArg a                  | nameOf
-- | getNamedArgE          | NamedArg Exp                | nameOf
-- | getNamedArgP          | NamedArg Pattern            | nameOf
-- | getNamedArgB          | NamedArg BindName           | nameOf
-- | getNamedArgL          | NamedArg LHSCore            | nameOf
--
-- | getModuleName         | A.MName                     | mod
-- | getModuleInfo         | ModuleInfo                  | asName, (range of as,to)
-- | getQuantityAttr       | Common.Quantity             | Symbol (if range)

instance Hilite A.RecordDirectives where
  hilite (RecordDirectives _ _ _ c) = hilite c

instance Hilite A.Declaration where
  hilite = \case
      A.Axiom _ax _di ai _occ x e            -> hl ai <> hl x <> hl e
      A.Generalize _names _di ai x e         -> hl ai <> hl x <> hl e
      A.Field _di x e                        -> hlField x <> hl e
      A.Primitive _di x e                    -> hl x <> hl e
      A.Mutual _mi ds                        -> hl ds
      A.Section _r x tel ds                  -> hl x <> hl tel <> hl ds
      A.Apply mi x a _ci dir                 -> hl mi <> hl x <> hl a <> hl dir
      A.Import mi x dir                      -> hl mi <> hl x <> hl dir
      A.Open mi x dir                        -> hl mi <> hl x <> hl dir
      A.FunDef _di x _delayed cs             -> hl x <> hl cs
      A.DataSig _di x tel e                  -> hl x <> hl tel <> hl e
      A.DataDef _di x _uc pars cs            -> hl x <> hl pars <> hl cs
      A.RecSig _di x tel e                   -> hl x <> hl tel <> hl e
      A.RecDef _di x _uc dir bs e ds         -> hl x <> hl dir <> hl bs <> hl e <> hl ds
      A.PatternSynDef x xs p                 -> hl x <> hl xs <> hl p
      A.UnquoteDecl _mi _di xs e             -> hl xs <> hl e
      A.UnquoteDef _di xs e                  -> hl xs <> hl e
      A.ScopedDecl s ds                      -> hl ds
      A.Pragma _r pragma                     -> hl pragma
    where
    hl      a = hilite a
    hlField x = hiliteAName x True (nameAsp Field)

instance Hilite A.Pragma where
  hilite = \case
    A.OptionsPragma _strings     -> mempty
    A.BuiltinPragma b x          -> singleAspect Keyword b <> hilite x
    A.BuiltinNoDefPragma b k x   -> singleAspect Keyword b <> hiliteQName (Just $ kindOfNameToNameKind k) x
    A.CompilePragma b x _foreign -> singleAspect Keyword b <> hilite x
    A.RewritePragma r xs         -> singleAspect Keyword r <> hilite xs
    A.StaticPragma x             -> hilite x
    A.EtaPragma x                -> hilite x
    A.InjectivePragma x          -> hilite x
    A.InlinePragma _inline x     -> hilite x
    A.DisplayPragma x ps e       -> hilite x <> hilite ps <> hilite e

instance Hilite A.Expr where
  hilite = \case
      A.Var x                       -> hl $ A.BindName x        -- bound variable like binder
      A.Def' q _                    -> hiliteQName Nothing q
      A.Proj _o qs                  -> hiliteAmbiguousQName Nothing qs  -- Issue #4604: not: hiliteProjection qs
                                         -- Names from @open R r@ should not be highlighted as projections
      A.Con qs                      -> hiliteAmbiguousQName Nothing qs  -- TODO? Con aspect
      A.PatternSyn qs               -> hilitePatternSynonym qs
      A.Macro q                     -> hiliteQName (Just Macro) q
      A.Lit _r l                    -> hl l
      A.QuestionMark _mi _ii        -> mempty
      A.Underscore _mi              -> mempty
      A.Dot _r e                    -> hl e                   -- TODO? Projection?
      A.App _r e es                 -> hl e <> hl es
      A.WithApp _r e es             -> hl e <> hl es
      A.Lam _r bs e                 -> hl bs <> hl e
      A.AbsurdLam _r _h             -> mempty
      A.ExtendedLam _r _di _e _q cs -> hl cs -- No hilighting of generated extended lambda name!
      A.Pi _r tel b                 -> hl tel <> hl b
      A.Generalized _qs e           -> hl e
      A.Fun _r a b                  -> hl a <> hl b
      A.Let _r bs e                 -> hl bs <> hl e
      A.ETel _tel                   -> mempty  -- Printing only construct
      A.Rec _r ass                  -> hl ass
      A.RecUpdate _r e ass          -> hl e <> hl ass
      A.ScopedExpr _ e              -> hl e
      A.Quote _r                    -> mempty
      A.QuoteTerm _r                -> mempty
      A.Unquote _r                  -> mempty
      A.DontCare e                  -> hl e
    where
    hl a = hilite a

instance (Hilite a, IsProjP a) => Hilite (A.Pattern' a) where
  hilite = \case
      A.VarP x               -> hl x
      A.ConP _i qs es        -> hiliteInductiveConstructor qs <> hl es
        -- No matching on coinductive constructors, thus, can determine NameKind here.
      A.ProjP _r _o qs       -> hiliteProjection qs
      A.DefP _r qs es        -> hl qs <> hl es
      A.WildP _r             -> mempty
      A.AsP _r x p           -> hl x <> hl p
      A.DotP r e             -> case isProjP e of
                                  Nothing       -> singleOtherAspect DottedPattern r <> hl e
                                  Just (_o, qs) -> hiliteProjection qs
      A.AbsurdP _r           -> mempty
      A.LitP _r l            -> hl l
      A.PatternSynP _r qs es -> hilitePatternSynonym qs <> hl es
      A.RecP _r ps           -> hl ps
      A.EqualP _r ps         -> hl ps
      A.WithP _ p            -> hl p
      A.AnnP _r a p          -> hl p

    where
    hl a = hilite a

instance Hilite Literal where
  hilite = \case
    LitNat{}                 -> mempty
    LitWord64{}              -> mempty
    LitFloat{}               -> mempty
    LitString{}              -> mempty
    LitChar{}                -> mempty
    LitQName x               -> hilite x
    LitMeta _fileName _id    -> mempty

-- * Minor syntactic categories
---------------------------------------------------------------------------

instance Hilite A.LHS where
  hilite (A.LHS _r lhs) = hilite lhs

instance (Hilite a, IsProjP a) => Hilite (A.LHSCore' a) where
  hilite = \case
    A.LHSHead q ps       -> hilite q   <> hilite ps
    A.LHSProj q lhs ps   -> hilite lhs <> hilite q   <> hilite ps -- TODO? Projection?
    A.LHSWith lhs wps ps -> hilite lhs <> hilite wps <> hilite ps

instance Hilite A.RHS where
  hilite = \case
      A.RHS e _ce                          -> hl e
      A.AbsurdRHS                          -> mempty
      A.WithRHS _q es cs                   -> hl es  <> hl cs  -- No highlighting for with-function-name!
      A.RewriteRHS eqs strippedPats rhs wh -> hl eqs <> hl strippedPats <> hl rhs <> hl wh
    where
    hl a = hilite a

instance (HasRange n, Hilite p, Hilite e) => Hilite (RewriteEqn' x n p e) where
  hilite = \case
    Rewrite es    -> hilite $ fmap snd es
    Invert _x pes -> hilite pes

instance Hilite a => Hilite (A.Clause' a) where
  hilite (A.Clause lhs strippedPats rhs wh _catchall) =
    hilite lhs <> hilite strippedPats <> hilite rhs <> hilite wh

instance Hilite A.ProblemEq where
  hilite (A.ProblemEq p _t _dom) = hilite p

instance Hilite A.WhereDeclarations where
  hilite (A.WhereDecls m _ ds) = hilite m <> hilite ds

instance Hilite A.GeneralizeTelescope where
  hilite (A.GeneralizeTel _gen tel) = hilite tel

instance Hilite A.DataDefParams where
  hilite (A.DataDefParams _gen pars) = hilite pars

instance Hilite A.ModuleApplication where
  hilite = \case
    A.SectionApp tel x es    -> hilite tel <> hilite x <> hilite es
    A.RecordModuleInstance x -> hilite x

instance Hilite A.LetBinding where
  hilite = \case
      A.LetBind    _r ai x t e     -> hl ai <> hl x <> hl t <> hl e
      A.LetPatBind _r p e          -> hl p  <> hl e
      A.LetApply   mi x es _ci dir -> hl mi <> hl x <> hl es <> hl dir
      A.LetOpen    mi x dir        -> hl mi <> hl x <> hl dir
      A.LetDeclaredVariable x      -> hl x
    where
    hl x = hilite x

instance Hilite A.TypedBinding where
  hilite = \case
    A.TBind _r tac binds e -> hilite tac <> hilite binds <> hilite e
    A.TLet _r binds        -> hilite binds

instance Hilite A.LamBinding where
  hilite = \case
    A.DomainFree tac binds -> hilite tac <> hilite binds
    A.DomainFull bind      -> hilite bind

instance Hilite a => Hilite (A.Binder' a) where
  hilite (A.Binder p x) = hilite p <> hilite x

instance Hilite A.BindName where
  hilite (A.BindName x) = hiliteBound x

instance Hilite a => Hilite (FieldAssignment' a) where
  hilite (FieldAssignment x e) =
    hiliteCName [] x noRange Nothing (nameAsp Field) <> hilite e

instance (Hilite a, HasRange n) => Hilite (Named n a) where
  hilite (Named mn e)
    =  maybe mempty (singleAspect $ Name (Just Argument) False) mn
    <> hilite e

instance Hilite a => Hilite (Arg a) where
  hilite (Arg ai e) = hilite ai <> hilite e

instance Hilite ArgInfo where
  hilite (ArgInfo _hiding modality _origin _fv _a) = hilite modality

instance Hilite Modality where
  hilite (Modality _relevance quantity _cohesion) = hilite quantity

-- | If the 'Quantity' attribute comes with a 'Range', highlight the
-- corresponding attribute as 'Symbol'.
instance Hilite Quantity where
  hilite = singleAspect Symbol

instance Hilite ModuleInfo where
  hilite (ModuleInfo _r rAsTo asName _open _impDir)
    =  singleAspect Symbol rAsTo            -- TODO: 'to' already covered by A.ImportDirective
    <> maybe mempty hiliteAsName asName
    -- <> hilite impDir                     -- Should be covered by A.ImportDirective
    where
    hiliteAsName :: C.Name -> Hiliter
    hiliteAsName n =
      hiliteCName [] n noRange Nothing $ nameAsp (Module Common.Bound)

instance (Hilite m, Hilite n, Hilite (RenamingTo m), Hilite (RenamingTo n))
       => Hilite (ImportDirective' m n) where
  hilite (ImportDirective _r using hiding renamings publicRange) =
    hilite using <> hilite hiding <> foldMap hiliteRenaming renamings
    where
    public = maybe False (const True) publicRange

    hiliteRenaming (Renaming from to _fixity rangeKwTo) =
         hilite from
      <> singleAspect Symbol rangeKwTo
           -- Currently, the "to" is already highlited by rAsTo above.
           -- TODO: remove the "to" ranges from rAsTo.
      <> hilite (RenamingTo to public)

instance (Hilite m, Hilite n) => Hilite (Using' m n) where
  hilite = \case
    UseEverything -> mempty
    Using using   -> hilite using

instance (Hilite m, Hilite n) => Hilite (ImportedName' m n) where
  hilite = \case
    ImportedModule m -> hilite m
    ImportedName   n -> hilite n

-- * Highlighting of names
---------------------------------------------------------------------------

instance Hilite DisambiguatedName where
  hilite (DisambiguatedName k x) = hiliteQName (Just k) x

instance Hilite ResolvedName where
  hilite = \case
    VarName           x _bindSrc -> hiliteBound x
    DefinedName  _acc x _suffix  -> hilite $ anameName x
    FieldName         xs         -> hiliteProjection $ A.AmbQ $ fmap anameName xs
    ConstructorName i xs         -> hiliteAmbiguousQName k $ A.AmbQ $ fmap anameName xs
      where k = kindOfNameToNameKind <$> exactConName i
    PatternSynResName xs         -> hilitePatternSynonym $ A.AmbQ $ fmap anameName xs
    UnknownName                  -> mempty

instance Hilite A.QName where
  hilite = hiliteQName Nothing

instance Hilite A.AmbiguousQName where
  hilite = hiliteAmbiguousQName Nothing

instance Hilite A.ModuleName where
  -- For top level modules, we set the binding site to the beginning of the file
  -- so that clicking on an imported module will jump to the beginning of the file
  -- which defines this module.
  hilite    (A.MName [])       = mempty
  hilite m'@(A.MName (n : ns)) = do
    modMap <- asks hleModMap
    access <- accessM m
    bound  <- lift $
              -- Module names from other modules are not bound.
              fromMaybe NotBound . HMap.lookup m' <$>
              useTC stBoundModuleNames
    hiliteCName
      ms
      (A.nameConcrete m)
      noRange
      (mR modMap access)
      (nameAsp $ Module bound)
    where
    (ms, m) = initLast1 n ns

    mR modMap access = Just
      ( applyWhen isTopLevelModule P.beginningOfFile $
        A.nameBindingSite m
      , access
      , Nothing
      )
      where
      isTopLevelModule =
        case mapMaybe
               ((Strict.toLazy . P.srcFile) <=<
                (P.rStart . A.nameBindingSite))
               (n : ns) of
          []    -> False
          f : _ ->
            Map.lookup f modMap ==
            Just (C.toTopLevelModuleName $ A.mnameToConcrete m')

  -- Andreas, 2020-09-29, issue #4952.
-- The target of a @renaming@ clause needs to be highlighted in a special way.
data RenamingTo a = RenamingTo
  { _renamingTo :: !a
    -- ^ The target.
  , _renamingToPublic :: !Bool
    -- ^ Is the @renaming@ clause part of an @open@ @public@
    -- statement?
  }

instance Hilite (RenamingTo A.QName) where
  -- Andreas, 2020-09-29, issue #4952.
  -- Do not include the bindingSite, because the HTML backed turns it into garbage.
  hilite (RenamingTo q _) = do
    kind <- asks hleNameKinds <&> ($ q)
    hiliteAName q False $ nameAsp' kind

instance Hilite (RenamingTo A.ModuleName) where
  -- Andreas, 2020-09-29, issue #4952.
  -- Do not include the bindingSite, because the HTML backed turns it into garbage.
  hilite (RenamingTo (A.MName ns) public) = flip foldMap ns $ \ n ->
    hiliteCName [] (A.nameConcrete n) noRange Nothing $
      nameAsp $ Module $ if public then NotBound else Common.Bound

instance (Hilite (RenamingTo m), Hilite (RenamingTo n))
       => Hilite (RenamingTo (ImportedName' m n)) where
  hilite (RenamingTo x public) = case x of
    ImportedModule m -> hilite (RenamingTo m public)
    ImportedName   n -> hilite (RenamingTo n public)

hiliteQName
  :: Maybe NameKind   -- ^ Is 'NameKind' already known from the context?
  -> A.QName
  -> Hiliter
hiliteQName mkind q
  | isExtendedLambdaName q = mempty
  | isAbsurdLambdaName   q = mempty
  | otherwise = do
      kind <- ifJust mkind (pure . Just) {-else-} $ asks hleNameKinds <&> ($ q)
      hiliteAName q True $ nameAsp' kind

-- | Takes the first 'NameKind'.  Binding site only included if unique.
hiliteAmbiguousQName
  :: Maybe NameKind   -- ^ Is 'NameKind' already known from the context?
  -> A.AmbiguousQName
  -> Hiliter
hiliteAmbiguousQName mkind (A.AmbQ qs) = do
  kind <- ifJust mkind (pure . Just) {-else-} $ do
    kinds <- asks hleNameKinds
    pure $ listToMaybe $ List1.catMaybes $ fmap kinds qs
      -- Ulf, 2014-06-03: [issue1064] It's better to pick the first rather
      -- than doing no highlighting if there's an ambiguity between an
      -- inductive and coinductive constructor.
  flip foldMap qs $ \ q ->
    hiliteAName q include $ nameAsp' kind
  where
  include = List1.allEqual $ fmap bindingSite qs

hiliteBound :: A.Name -> Hiliter
hiliteBound x =
  hiliteCName [] (A.nameConcrete x) noRange
    (Just (A.nameBindingSite x, PrivateAccess UserWritten, Nothing))
    (nameAsp H.Bound)

hiliteInductiveConstructor :: A.AmbiguousQName -> Hiliter
hiliteInductiveConstructor = hiliteAmbiguousQName $ Just $ Constructor Inductive

hilitePatternSynonym :: A.AmbiguousQName -> Hiliter
hilitePatternSynonym = hiliteInductiveConstructor  -- There are no coinductive pattern synonyms!?

hiliteProjection :: A.AmbiguousQName -> Hiliter
hiliteProjection = hiliteAmbiguousQName (Just Field)

-- | Information about constructors.

data ConstructorInfo
  = DataConstructor
    -- ^ The constructor is a data constructor or a pattern synonym.
  | RecordConstructor A.QName
    -- ^ The constructor is a record constructor. The name is the
    -- record type to which the constructor belongs.
  | Unknown
    -- ^ None of the choices above are applicable, perhaps because the
    -- record type of a record constructor could not be obtained.

-- This was Highlighting.Generate.nameToFile:
-- | Converts names to suitable 'File's.
hiliteCName
  :: [A.Name]
     -- ^ The name qualifier (may be empty).
  -> C.Name     -- ^ The base name.
  -> Range
     -- ^ The 'Range' of the name in its fixity declaration (if any).
  -> Maybe (Range, Access, Maybe ConstructorInfo)
     -- ^ The definition site of the name (if any), along with
     --   information about whether the name was declared as public or
     --   private, and, if the name is a constructor, some
     --   'ConstructorInfo'.
  -> (Bool -> Aspects)
     -- ^ Meta information to be associated with the name.
     --   The argument is 'True' iff the name is an operator.
  -> Hiliter
hiliteCName ms x fr mR asp = do
  fileName <- lift getCurrentPath
  -- We don't care if we get any funny ranges.
  if all (== Strict.Just fileName) fileNames then do
    defSite <- runMaybeT mFilePos
    return $
      frFile defSite <>
      H.singleton (rToR rs) (aspects { definitionSite = defSite })
   else
    return mempty
  where
  xs        = map A.nameConcrete ms
  aspects   = asp $ C.isOperator x
  fileNames = mapMaybe (fmap P.srcFile . P.rStart . getRange) (x : xs)
  frFile    = \defSite ->
                 H.singleton (rToR fr)
                   (aspects { definitionSite = notHere <$> defSite })
  rs        = getRange (x : xs)

  -- The fixity declaration should not get a symbolic anchor.
  notHere d = d { defSiteHere = False }

  mFilePos :: MaybeT HiliteM DefinitionSite
  mFilePos = do
    (r, access, conInfo) <- MaybeT $ return mR
    P.Pn { P.srcFile = Strict.Just f, P.posPos = p } <-
      MaybeT $ return $ P.rStart r
    modMap <- lift $ asks hleModMap
    mod <- MaybeT $ return $ Map.lookup f modMap
    -- Andreas, 2017-06-16, Issue #2604: Symbolic anchors.
    -- We drop the file name part from the qualifiers, since
    -- this is contained in the html file name already.
    -- We want to get anchors of the form:
    -- @<a name="TopLevelModule.html#LocalModule.NestedModule.identifier">@
    let qualifiers = drop (length $ C.moduleNameParts mod) ms
        -- Symbolic anchors are not created for bound variables.
        local = maybe True isLocalAspect (aspect aspects)
        -- Symbolic anchors are not created for constructors without
        -- ConstructorInfo.
        (con, skipCon) = case conInfo of
          Nothing                    -> (False, False)
          Just Unknown               -> (True,  True)
          Just DataConstructor       -> (True,  False)
          Just (RecordConstructor _) -> (True,  False)
    -- Symbolic anchors are not created if one of the "qualifiers"
    -- is an underscore that does not correspond to an 'Anonymous'
    -- module.
    badUnderscore <- lift $ anyM qualifiers $ \n ->
      and2M (return $ C.isNoName n) (not <$> isAnonymousModuleName n)
    let -- Finally symbolic anchors are not created for underscores.
        skip = local || skipCon || badUnderscore || C.isNoName x
    anchor <-
      if skip then return Nothing else lift $ do
        qualifiers <- case access of
          PrivateAccess _ -> return qualifiers
          PublicAccess    ->
            -- Anonymous module names are not included in the anchors
            -- of public names.
            filterM (\n -> not <$> isAnonymousModuleName n) qualifiers
        qualifiers <-
          concat <$>
          mapM (\q -> (++ ".") <$> showQualifier q) qualifiers
        return $ Just $
          (-- A different name space is used for module names, so
           -- different symbolic anchors are generated.
           if isModuleName (aspect aspects)
           then "{mod}" else "") ++
          (-- A different name space is used for constructors, which
           -- can be overloaded.
           if con then "{con}" else "") ++
          qualifiers ++
          (-- For record constructors the prefix ends with the record
           -- type of the constructor.
           if con
           then case conInfo of
                  Nothing                    -> __IMPOSSIBLE__
                  Just Unknown               -> __IMPOSSIBLE__
                  Just DataConstructor       -> ""
                  Just (RecordConstructor m) ->
                    prettyShow (A.qnameName m) ++ "."
           else "") ++
          prettyShow (C.QName x)
    return $ DefinitionSite
      { defSiteModule = mod
      , defSitePos    = fromIntegral p
        -- Is our current position the definition site?
      , defSiteHere   = r == getRange x
      , defSiteAnchor = anchor
      }

  -- Is the name a bound variable or similar? If in doubt, yes.
  isLocalAspect :: Aspect -> Bool
  isLocalAspect = \case
    Name (Just kind) _ -> isLocal kind
    _ -> True
  isLocal :: NameKind -> Bool
  isLocal = \case
    H.Bound             -> True
    Generalizable       -> False
    Argument            -> True
    Constructor{}       -> False
    Datatype            -> False
    Field               -> False
    Function            -> False
    Module Common.Bound -> True
    Module NotBound     -> False
    Postulate           -> False
    Primitive           -> False
    Record              -> False
    Macro               -> False

  -- Is the thing (known to be) a module name?

  isModuleName :: Maybe Aspect -> Bool
  isModuleName = \case
    Just (Name (Just kind) _) -> case kind of
      H.Bound       -> False
      Generalizable -> False
      Argument      -> False
      Constructor _ -> False
      Datatype      -> False
      Field         -> False
      Function      -> False
      Module _      -> True
      Postulate     -> False
      Primitive     -> False
      Record        -> False
      Macro         -> False
    _ -> __IMPOSSIBLE__

  isAnonymousModuleName :: A.Name -> HiliteM Bool
  isAnonymousModuleName n = do
    anon <- isAnonymousM n
    return $ case anon of
      Anonymous n  -> True
      NotAnonymous -> False

  showQualifier :: A.Name -> HiliteM String
  showQualifier n = do
    anon <- isAnonymousM n
    return $ case anon of
      Anonymous (AnonymousNumber n) -> show n
      NotAnonymous                  -> prettyShow n

-- | Is some thing known to be a constructor?

isConstructor :: Maybe Aspect -> Bool
isConstructor = \case
  Just (Name (Just kind) _) -> case kind of
    H.Bound       -> False
    Generalizable -> False
    Argument      -> False
    Constructor _ -> True
    Datatype      -> False
    Field         -> False
    Function      -> False
    Module _      -> False
    Postulate     -> False
    Primitive     -> False
    Record        -> False
    Macro         -> False
  _ -> False

-- | Does the name refer to an 'Anonymous' module, and in that case,
-- what is the module's 'AnonymousNumber'?

isAnonymousM :: A.Name -> HiliteM IsAnonymous
isAnonymousM n = do
  anon <- useTC stAnonymousNumbers
  return $ case HMap.lookup n anon of
    Nothing -> NotAnonymous
    Just n  -> Anonymous n

-- | Was the name declared as public or private?

accessM :: A.Name -> HiliteM Access
accessM n = lift $ do
  acc <- useTC stAccess
  return $ case HMap.lookup n acc of
    Just acc -> acc
    Nothing  -> PublicAccess
      -- Names from other modules that the user wrote in the
      -- current module must be public.

-- This was Highlighting.Generate.nameToFileA:
-- | A variant of 'hiliteCName' for qualified abstract names.
hiliteAName
  :: A.QName
     -- ^ The name.
  -> Bool
     -- ^ Should the binding site be included in the file?
  -> (Bool -> Aspects)
     -- ^ Meta information to be associated with the name.
     -- ^ The argument is 'True' iff the name is an operator.
  -> Hiliter
hiliteAName x include asp = do
  fileName <- lift getCurrentPath
  access   <- accessM (A.qnameName x)
  let aspects = asp (A.isOperator x)
      isCon   = isConstructor (aspect aspects)
  dataOrRecMod <- if not isCon then return Nothing else do
    level <- asks hleLevel
    case level of
      Partial -> return (Just Unknown)
      Full    -> do
        info <- lift $ getConstInfo' x
        case info of
          -- At the time of writing one can get Left something for
          -- pattern synonyms. TODO: Can this not happen for record
          -- constructors? That assumption is made below.
          Left _ -> do
            kind <- ($ x) <$> asks hleNameKinds
            case kind of
              Just (Constructor _) -> return $ Just DataConstructor
              _                    ->
                __IMPOSSIBLE_VERBOSE__ $
                prettyShow x ++ ": " ++ show kind
          Right info -> return $ case theDef info of
            TCM.Constructor
              { conSrcCon = I.ConHead { I.conDataRecord = dr }
              , conData   = t
              } ->
              case dr of
                I.IsData     -> Just DataConstructor
                I.IsRecord _ -> Just (RecordConstructor t)
            _ -> __IMPOSSIBLE__
  hiliteCName (qualifier x)
              (concreteBase x)
              (rangeOfFixityDeclaration fileName)
              (if include
               then Just (bindingSite x, access, dataOrRecMod)
               else Nothing)
              asp
    <> (notationFile fileName)
  where
  -- TODO: Currently we highlight fixity and syntax declarations by
  -- producing highlighting something like once per occurrence of the
  -- related name(s) in the file of the declaration (and we explicitly
  -- avoid doing this for other files). Perhaps it would be better to
  -- only produce this highlighting once.

  rangeOfFixityDeclaration fileName =
    if P.rangeFile r == Strict.Just fileName
    then r else noRange
    where
    r = theNameRange $ A.nameFixity $ A.qnameName x

  notationFile fileName = pure $
    if P.rangeFile (getRange notation) == Strict.Just fileName
    then mconcat $ map genPartFile notation
    else mempty
    where
    notation = theNotation $ A.nameFixity $ A.qnameName x

    boundAspect = nameAsp H.Bound False

    genPartFile (VarPart r i)  = several [rToR r, rToR $ getRange i] boundAspect
    genPartFile (HolePart r i) = several [rToR r, rToR $ getRange i] boundAspect
    genPartFile WildPart{}     = mempty
    genPartFile (IdPart x)     = H.singleton (rToR $ getRange x) (asp False)

-- * Short auxiliary functions.
---------------------------------------------------------------------------

singleAspect :: HasRange a => Aspect -> a -> Hiliter
singleAspect a x = pure $ H.singleton (rToR $ getRange x) $ parserBased { aspect = Just a }

singleOtherAspect :: HasRange a => OtherAspect -> a -> Hiliter
singleOtherAspect a x = pure $ H.singleton (rToR $ getRange x) $ parserBased { otherAspects = singleton a }

nameAsp' :: Maybe NameKind -> Bool -> Aspects
nameAsp' k isOp = parserBased { aspect = Just $ Name k isOp }

nameAsp :: NameKind -> Bool -> Aspects
nameAsp = nameAsp' . Just

concreteBase :: A.QName -> C.Name
concreteBase = A.nameConcrete . A.qnameName

qualifier :: A.QName -> [A.Name]
qualifier = A.mnameToList . A.qnameModule

bindingSite :: A.QName -> Range
bindingSite = A.nameBindingSite . A.qnameName
