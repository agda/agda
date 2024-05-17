
module Agda.TypeChecking.Pretty
    ( module Agda.TypeChecking.Pretty
    , module Data.Semigroup -- This re-export can be removed once <GHC-8.4 is dropped.
    , module Reexport
    ) where

import Prelude hiding ( null )

import Control.Applicative  (liftA2)
import Control.Monad
import Control.Monad.Except

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.String    ()
import Data.Semigroup (Semigroup((<>)))
import qualified Data.Foldable as Fold

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.ReflectedToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import qualified Agda.Syntax.Translation.AbstractToConcrete as Reexport (MonadAbsToCon)
import qualified Agda.Syntax.Translation.ReflectedToAbstract as R
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract.Pretty as AP
import Agda.Syntax.Concrete.Pretty (bracesAndSemicolons, prettyHiding)
import qualified Agda.Syntax.Concrete.Pretty as CP
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Scope.Base  (AbstractName(..))
import Agda.Syntax.Scope.Monad (withContextPrecedence)
import Agda.Syntax.TopLevelModuleName

import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.DiscrimTree.Types
import Agda.TypeChecking.Substitute

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Trie
import Agda.Utils.Permutation ( Permutation )
import Agda.Syntax.Common.Pretty      ( Pretty, prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import qualified Agda.Utils.Maybe.Strict as S
import Agda.Utils.Size        ( natSize )

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
---------------------------------------------------------------------------

type Doc = P.Doc

comma, colon, equals :: Applicative m => m Doc
comma  = pure P.comma
colon  = pure P.colon
equals = pure P.equals

{-# INLINE pretty #-}
pretty :: (Applicative m, P.Pretty a) => a -> m Doc
pretty x = pure $ P.pretty x

{-# INLINE prettyA #-}
prettyA :: (ToConcrete a, P.Pretty (ConOfAbs a), MonadAbsToCon m) => a -> m Doc
prettyA x = AP.prettyA x

{-# INLINE prettyAs #-}
prettyAs :: (ToConcrete a, ConOfAbs a ~ [ce], P.Pretty ce, MonadAbsToCon m) => a -> m Doc
prettyAs x = AP.prettyAs x

{-# INLINE text #-}
text :: Applicative m => String -> m Doc
text s = pure $ P.text s

multiLineText :: Applicative m => String -> m Doc
multiLineText s = pure $ P.multiLineText s

pwords :: Applicative m => String -> [m Doc]
pwords s = map pure $ P.pwords s

fwords :: Applicative m => String -> m Doc
fwords s = pure $ P.fwords s

sep, fsep, hsep, hcat, vcat :: (Applicative m, Foldable t) => t (m Doc) -> m Doc
sep ds  = P.sep  <$> sequenceA (Fold.toList ds)
fsep ds = P.fsep <$> sequenceA (Fold.toList ds)
hsep ds = P.hsep <$> sequenceA (Fold.toList ds)
hcat ds = P.hcat <$> sequenceA (Fold.toList ds)
vcat ds = P.vcat <$> sequenceA (Fold.toList ds)

hang :: Applicative m => m Doc -> Int -> m Doc -> m Doc
hang p n q = P.hang <$> p <*> pure n <*> q

infixl 6 <+>, <?>
infixl 5 $$, $+$

($$), ($+$), (<+>), (<?>) :: Applicative m => m Doc -> m Doc -> m Doc
d1 $$ d2  = (P.$$) <$> d1 <*> d2
d1 $+$ d2 = (P.$+$) <$> d1 <*> d2
d1 <+> d2 = (P.<+>) <$> d1 <*> d2
d1 <?> d2 = (P.<?>) <$> d1 <*> d2

nest :: Functor m => Int -> m Doc -> m Doc
nest n d   = P.nest n <$> d

braces, dbraces, brackets, parens, parensNonEmpty
  , doubleQuotes, quotes :: Functor m => m Doc -> m Doc
braces d   = P.braces <$> d
dbraces d  = CP.dbraces <$> d
brackets d = P.brackets <$> d
parens d   = P.parens <$> d
parensNonEmpty d = P.parensNonEmpty <$> d
doubleQuotes   d = P.doubleQuotes   <$> d
quotes         d = P.quotes         <$> d

pshow :: (Applicative m, Show a) => a -> m Doc
pshow = pure . P.pshow

-- | Comma-separated list in brackets.
prettyList :: (Applicative m, Semigroup (m Doc), Foldable t) => t (m Doc) -> m Doc
prettyList ds = P.pretty <$> sequenceA (Fold.toList ds)

-- | 'prettyList' without the brackets.
prettyList_ :: (Applicative m, Semigroup (m Doc), Foldable t) => t (m Doc) -> m Doc
prettyList_ ds = fsep $ punctuate comma ds

{-# INLINABLE punctuate #-}
punctuate :: (Applicative m, Semigroup (m Doc), Foldable t) => m Doc -> t (m Doc) -> [m Doc]
punctuate d ts
  | null ds   = []
  | otherwise = zipWith (<>) ds (replicate n d ++ [pure empty])
  where
    ds = Fold.toList ts
    n  = length ds - 1

superscript :: Applicative m => Int -> m Doc
superscript = pretty . reverse . go where
  digit = ("⁰¹²³⁴⁵⁶⁷⁸⁹" !!)
  go k
    | k <= 9    = [digit k]
    | otherwise = digit (k `mod` 10):go (k `div` 10)

---------------------------------------------------------------------------
-- * The PrettyTCM class
---------------------------------------------------------------------------

type MonadPretty m = MonadAbsToCon m

-- This instance is to satify the constraints of superclass MonadPretty:
-- | This instance is more specific than a generic instance
-- @Semigroup a => Semigroup (TCM a)@.
instance {-# OVERLAPPING #-} Semigroup (TCM Doc)         where (<>) = liftA2 (<>)


class PrettyTCM a where
  prettyTCM :: MonadPretty m => a -> m Doc

-- | Pretty print with a given context precedence
prettyTCMCtx :: (PrettyTCM a, MonadPretty m) => Precedence -> a -> m Doc
prettyTCMCtx p = withContextPrecedence p . prettyTCM

instance {-# OVERLAPPING #-} PrettyTCM String where prettyTCM = text
instance PrettyTCM Bool                       where prettyTCM = pretty
instance PrettyTCM C.Name                     where prettyTCM = pretty
instance PrettyTCM C.QName                    where prettyTCM = pretty
instance PrettyTCM TopLevelModuleName         where prettyTCM = pretty
instance PrettyTCM Comparison                 where prettyTCM = pretty
instance PrettyTCM Literal                    where prettyTCM = pretty
instance PrettyTCM Nat                        where prettyTCM = pretty
instance PrettyTCM ProblemId                  where prettyTCM = pretty
instance PrettyTCM Range                      where prettyTCM = pretty
instance PrettyTCM CheckpointId               where prettyTCM = pretty
-- instance PrettyTCM Interval where prettyTCM = pretty
-- instance PrettyTCM Position where prettyTCM = pretty

{-# SPECIALIZE prettyTCM :: String             -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Bool               -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: C.Name             -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: C.QName            -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: TopLevelModuleName -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Comparison         -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Literal            -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Nat                -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: ProblemId          -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Range              -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: CheckpointId       -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Closure a) where
  prettyTCM cl = enterClosure cl prettyTCM

instance {-# OVERLAPPABLE #-} PrettyTCM a => PrettyTCM [a] where
  prettyTCM = prettyList . map prettyTCM

{-# SPECIALIZE prettyTCM :: PrettyTCM a => [a] -> TCM Doc #-}

instance {-# OVERLAPPABLE #-} PrettyTCM a => PrettyTCM (Maybe a) where
  prettyTCM = maybe empty prettyTCM

{-# SPECIALIZE prettyTCM :: PrettyTCM a => Maybe a -> TCM Doc #-}

instance (PrettyTCM a, PrettyTCM b) => PrettyTCM (a,b) where
  prettyTCM (a, b) = parens $ prettyTCM a <> comma <> prettyTCM b

{-# SPECIALIZE prettyTCM :: (PrettyTCM a, PrettyTCM b) => (a, b) -> TCM Doc #-}

instance (PrettyTCM a, PrettyTCM b, PrettyTCM c) => PrettyTCM (a,b,c) where
  prettyTCM (a, b, c) = parens $
    prettyTCM a <> comma <> prettyTCM b <> comma <> prettyTCM c

{-# SPECIALIZE prettyTCM :: (PrettyTCM a, PrettyTCM b, PrettyTCM c) => (a, b, c) -> TCM Doc #-}

instance PrettyTCM Term               where prettyTCM = prettyA <=< reify
instance PrettyTCM Type               where prettyTCM = prettyA <=< reify
instance PrettyTCM Sort               where prettyTCM = prettyA <=< reify
instance PrettyTCM DisplayTerm        where prettyTCM = prettyA <=< reify
instance PrettyTCM NamedClause        where prettyTCM = prettyA <=< reify
instance PrettyTCM (QNamed Clause)    where prettyTCM = prettyA <=< reify
instance PrettyTCM Level              where prettyTCM = prettyA <=< reify . Level
instance PrettyTCM (Named_ Term)      where prettyTCM = prettyA <=< reify
instance PrettyTCM (Arg Term)         where prettyTCM = prettyA <=< reify
instance PrettyTCM (Arg Type)         where prettyTCM = prettyA <=< reify
instance PrettyTCM (Arg Bool)         where prettyTCM = prettyA <=< reify
instance PrettyTCM (Arg String)       where prettyTCM = prettyA <=< reify
instance PrettyTCM (Arg A.Expr)       where prettyTCM = prettyA <=< reify
instance PrettyTCM (NamedArg A.Expr)  where prettyTCM = prettyA <=< reify
instance PrettyTCM (NamedArg Term)    where prettyTCM = prettyA <=< reify
instance PrettyTCM (Dom Type)         where prettyTCM = prettyA <=< reify
instance PrettyTCM ContextEntry       where prettyTCM = prettyA <=< reify
instance PrettyTCM Permutation        where prettyTCM = text . show
instance PrettyTCM Polarity           where prettyTCM = text . show
instance PrettyTCM IsForced           where prettyTCM = text . show

{-# SPECIALIZE prettyTCM :: Term              -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Type              -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Sort              -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: DisplayTerm       -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: NamedClause       -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (QNamed Clause)   -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Level             -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (Named_ Term)     -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (Arg Term)        -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (Arg Type)        -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (Arg Bool)        -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (Arg A.Expr)      -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (NamedArg A.Expr) -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (NamedArg Term)   -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: (Dom Type)        -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: ContextEntry      -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Permutation       -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: Polarity          -> TCM Doc #-}
{-# SPECIALIZE prettyTCM :: IsForced          -> TCM Doc #-}

prettyR
  :: (R.ToAbstract r, PrettyTCM (R.AbsOfRef r), MonadPretty m, MonadError TCErr m)
  => r -> m Doc
prettyR = prettyTCM <=< toAbstractWithoutImplicit

instance (Pretty a, PrettyTCM a, EndoSubst a) => PrettyTCM (Substitution' a) where
  prettyTCM IdS        = "idS"
  prettyTCM (Wk m IdS) = "wkS" <+> pretty m
  prettyTCM (EmptyS _) = "emptyS"
  prettyTCM rho = prettyTCM u <+> comma <+> prettyTCM rho1
    where
      (rho1, rho2) = splitS 1 rho
      u            = lookupS rho2 0

instance PrettyTCM Clause where
  prettyTCM cl = do
    x <- qualify_ <$> freshName_ ("<unnamedclause>" :: String)
    prettyTCM (QNamed x cl)
{-# SPECIALIZE prettyTCM :: Clause -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Judgement a) where
  prettyTCM (HasType a cmp t) = prettyTCM a <+> ":" <+> prettyTCM t
  prettyTCM (IsSort  a t) = "Sort" <+> prettyTCM a <+> ":" <+> prettyTCM t
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Judgement a -> TCM Doc #-}

instance PrettyTCM MetaId where
  prettyTCM x = do
    mn <- getMetaNameSuggestion x
    prettyTCM $ NamedMeta mn x
{-# SPECIALIZE prettyTCM :: MetaId -> TCM Doc #-}

instance PrettyTCM NamedMeta where
  prettyTCM (NamedMeta s m) = do
    current <- currentModuleNameHash
    prefix  <-
      if metaModule m == current
      then return empty
      else do
        modName <- BiMap.invLookup (metaModule m) <$>
                   useR stTopLevelModuleNames
        return $ case modName of
          Nothing      -> __IMPOSSIBLE__
          Just modName -> pretty modName <> text "."
    let inBetween = case s of
          ""  -> text "_"
          "_" -> text "_"
          s   -> text $ "_" ++ s ++ "_"
    prefix <> inBetween <> text (show (metaId m))
{-# SPECIALIZE prettyTCM :: NamedMeta -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Blocked a) where
  prettyTCM (Blocked x a) = ("[" <+> prettyTCM a <+> "]") <> text (P.prettyShow x)
  prettyTCM (NotBlocked _ x) = prettyTCM x
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Blocked a -> TCM Doc #-}

instance (PrettyTCM k, PrettyTCM v) => PrettyTCM (Map k v) where
  prettyTCM m = "Map" <> braces (sep $ punctuate comma
    [ hang (prettyTCM k <+> "=") 2 (prettyTCM v) | (k, v) <- Map.toList m ])
{-# SPECIALIZE prettyTCM :: (PrettyTCM k, PrettyTCM v) => Map k v -> TCM Doc  #-}

-- instance {-# OVERLAPPING #-} PrettyTCM ArgName where
--   prettyTCM = text . P.prettyShow

-- instance (Reify a e, ToConcrete e c, P.Pretty c, PrettyTCM a) => PrettyTCM (Elim' a) where
instance PrettyTCM Elim where
  prettyTCM (IApply x y v) = "I$" <+> prettyTCM v
  prettyTCM (Apply v) = "$" <+> prettyTCM v
  prettyTCM (Proj _ f)= "." <> prettyTCM f
{-# SPECIALIZE prettyTCM :: Elim -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (MaybeReduced a) where
  prettyTCM = prettyTCM . ignoreReduced
{-# SPECIALIZE prettyTCM :: PrettyTCM a => MaybeReduced a -> TCM Doc #-}

instance PrettyTCM EqualityView where
  prettyTCM v = prettyTCM $ equalityUnview v
{-# SPECIALIZE prettyTCM :: EqualityView -> TCM Doc #-}

instance PrettyTCM A.Expr where
  prettyTCM = prettyA; {-# INLINE prettyTCM #-}

instance PrettyTCM A.TypedBinding where
  prettyTCM = prettyA; {-# INLINE prettyTCM #-}

instance PrettyTCM A.Pattern where
  prettyTCM = prettyA; {-# INLINE prettyTCM #-}

instance PrettyTCM Relevance where
  prettyTCM = pretty; {-# INLINE prettyTCM #-}

instance PrettyTCM Quantity where
  prettyTCM = pretty; {-# INLINE prettyTCM #-}

instance PrettyTCM Erased where
  prettyTCM = pretty; {-# INLINE prettyTCM #-}

instance PrettyTCM Modality where
  prettyTCM mod = hsep
    [ prettyTCM (getQuantity mod)
    , prettyTCM (getRelevance mod)
    ]
{-# SPECIALIZE prettyTCM :: Modality -> TCM Doc #-}

instance PrettyTCM Blocker where
  prettyTCM (UnblockOnAll us) = "all" <> parens (fsep $ punctuate "," $ map prettyTCM $ Set.toList us)
  prettyTCM (UnblockOnAny us) = "any" <> parens (fsep $ punctuate "," $ map prettyTCM $ Set.toList us)
  prettyTCM (UnblockOnMeta m) = prettyTCM m
  prettyTCM (UnblockOnProblem p) = "problem" <+> pretty p
  prettyTCM (UnblockOnDef q) = "definition" <+> pretty q
{-# SPECIALIZE prettyTCM :: Blocker -> TCM Doc #-}

instance PrettyTCM CompareAs where
  prettyTCM (AsTermsOf a) = ":" <+> prettyTCMCtx TopCtx a
  prettyTCM AsSizes       = ":" <+> do prettyTCM =<< sizeType
  prettyTCM AsTypes       = empty
{-# SPECIALIZE prettyTCM :: CompareAs -> TCM Doc #-}

instance PrettyTCM TypeCheckingProblem where
  prettyTCM (CheckExpr cmp e a) =
    sep [ prettyA e <+> ":?", prettyTCM a ]
  prettyTCM (CheckArgs _ _ _ es t0 t1 _) =
    sep [ parens $ "_ :" <+> prettyTCM t0
        , nest 2 $ prettyList $ map prettyA es
        , nest 2 $ ":?" <+> prettyTCM t1 ]
  prettyTCM (CheckProjAppToKnownPrincipalArg cmp e _ _ _ t _ _ _ _) = prettyTCM (CheckExpr cmp e t)
  prettyTCM (CheckLambda cmp (Arg ai (xs, mt)) e t) =
    sep [ pure CP.lambda <+>
          (CP.prettyRelevance ai .
           CP.prettyHiding ai (if isNothing mt && natSize xs == 1 then id
                               else P.parens) <$> do
            fsep $
              map prettyTCM (List1.toList xs) ++
              caseMaybe mt [] (\ a -> [":", prettyTCM a])) <+>
          pure CP.arrow <+>
          prettyTCM e <+>
          ":?"
        , prettyTCM t
        ]
  prettyTCM (DoQuoteTerm _ v _) = do
    e <- reify v
    prettyTCM (A.App A.defaultAppInfo_ (A.QuoteTerm A.exprNoRange) (defaultNamedArg e))
{-# SPECIALIZE prettyTCM :: TypeCheckingProblem -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (WithHiding a) where
  prettyTCM (WithHiding h a) = CP.prettyHiding h id <$> prettyTCM a
{-# SPECIALIZE prettyTCM :: PrettyTCM a => WithHiding a -> TCM Doc #-}

instance PrettyTCM Name where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x
{-# SPECIALIZE prettyTCM :: Name -> TCM Doc #-}

instance PrettyTCM QName where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x
{-# SPECIALIZE prettyTCM :: Name -> TCM Doc #-}

instance PrettyTCM ModuleName where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x
{-# SPECIALIZE prettyTCM :: ModuleName -> TCM Doc #-}

instance PrettyTCM AbstractName where
  prettyTCM = prettyTCM . anameName
{-# SPECIALIZE prettyTCM :: AbstractName -> TCM Doc #-}

instance PrettyTCM ConHead where
  prettyTCM = prettyTCM . conName
{-# SPECIALIZE prettyTCM :: ConHead -> TCM Doc #-}

instance PrettyTCM Telescope where
  prettyTCM tel = P.fsep . map P.pretty <$> do
      tel <- reify tel
      runAbsToCon $ bindToConcrete tel return
{-# SPECIALIZE prettyTCM :: Telescope -> TCM Doc #-}

newtype PrettyContext = PrettyContext Context

instance PrettyTCM PrettyContext where
  prettyTCM (PrettyContext ctx) = prettyTCM $ contextToTel ctx -- TODO: include let bindings?
{-# SPECIALIZE prettyTCM :: PrettyContext -> TCM Doc #-}

instance PrettyTCM DBPatVar where
  prettyTCM = prettyTCM . var . dbPatVarIndex
{-# SPECIALIZE prettyTCM :: DBPatVar -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Pattern' a) where
  prettyTCM :: forall m. MonadPretty m => Pattern' a -> m Doc
  prettyTCM (IApplyP _ _ _ x)    = prettyTCM x
  prettyTCM (VarP _ x)    = prettyTCM x
  prettyTCM (DotP _ t)    = ".(" <> prettyTCM t <> ")"
  prettyTCM (DefP o q ps) = parens $
        prettyTCM q <+> fsep (map (prettyTCM . namedArg) ps)
  prettyTCM (ConP c i ps) = -- (if b then braces else parens) $ prTy $
        parens $
        prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
      where
        -- NONE OF THESE BINDINGS IS USED AT THE MOMENT:
        b = conPRecord i && patOrigin (conPInfo i) /= PatOCon
        showRec :: m Doc -- Defined, but currently not used
        showRec = sep
          [ "record"
          , bracesAndSemicolons <$> zipWithM showField (conFields c) ps
          ]
        showField :: Arg QName -> NamedArg (Pattern' a) -> m Doc -- NB:: Defined but not used
        showField (Arg ai x) p =
          sep [ prettyTCM (A.qnameName x) <+> "=" , nest 2 $ prettyTCM $ namedArg p ]
        showCon :: m Doc -- NB:: Defined but not used
        showCon = parens $ prTy $ prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
        prTy d = caseMaybe (conPType i) d $ \ t -> d  <+> ":" <+> prettyTCM t
  prettyTCM (LitP _ l)    = text (P.prettyShow l)
  prettyTCM (ProjP _ q)   = text ("." ++ P.prettyShow q)
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Pattern' a -> TCM Doc #-}

{-# SPECIALIZE prettyTCMPatterns :: [NamedArg DeBruijnPattern] -> TCM [Doc] #-}
-- | Proper pretty printing of patterns:
prettyTCMPatterns :: MonadPretty m => [NamedArg DeBruijnPattern] -> m [Doc]
prettyTCMPatterns = mapM prettyA <=< reifyPatterns

{-# SPECIALIZE prettyTCMPatternList :: [NamedArg DeBruijnPattern] -> TCM Doc #-}
prettyTCMPatternList :: MonadPretty m => [NamedArg DeBruijnPattern] -> m Doc
prettyTCMPatternList = prettyList . map prettyA <=< reifyPatterns

instance PrettyTCM (Elim' DisplayTerm) where
  prettyTCM (IApply x y v) = "$" <+> prettyTCM v
  prettyTCM (Apply v) = "$" <+> prettyTCM (unArg v)
  prettyTCM (Proj _ f)= "." <> prettyTCM f
{-# SPECIALIZE prettyTCM :: Elim' DisplayTerm -> TCM Doc #-}

instance PrettyTCM NLPat where
  prettyTCM (PVar x bvs) = prettyTCM (Var x (map (Apply . fmap var) bvs))
  prettyTCM (PDef f es) = parens $
    prettyTCM f <+> fsep (map prettyTCM es)
  prettyTCM (PLam i u)  = parens $ fsep
    [ "λ"
    , prettyHiding i id <$> text (absName u)
    , "→"
    , addContext (absName u) $ prettyTCM $ absBody u
    ]
  prettyTCM (PPi a b)   = parens $ fsep
    [ prettyHiding a P.parens <$> fsep [ text $ absName b, ":", prettyTCM $ unDom a ]
    , "→"
    , addContext (absName b) $ prettyTCM $ unAbs b
    ]
  prettyTCM (PSort s)        = prettyTCM s
  prettyTCM (PBoundVar i []) = prettyTCM (var i)
  prettyTCM (PBoundVar i es) = parens $ prettyTCM (var i) <+> fsep (map prettyTCM es)
  prettyTCM (PTerm t)   = "." <> parens (prettyTCM t)
{-# SPECIALIZE prettyTCM :: NLPat -> TCM Doc #-}

instance PrettyTCM NLPType where
  prettyTCM (NLPType s a) = prettyTCM a
{-# SPECIALIZE prettyTCM :: NLPType -> TCM Doc #-}

instance PrettyTCM NLPSort where
  prettyTCM = \case
    PUniv u l -> parens $ text (showUniv u) <+> prettyTCM l
      -- Andreas, 2023-05-11, preserving Jesper's printing hack for now...
    PInf u n  -> prettyTCM (Inf u n :: Sort)
    PSizeUniv -> prettyTCM (SizeUniv :: Sort)
    PLockUniv -> prettyTCM (LockUniv :: Sort)
    PLevelUniv -> prettyTCM (LevelUniv :: Sort)
    PIntervalUniv -> prettyTCM (IntervalUniv :: Sort)
{-# SPECIALIZE prettyTCM :: NLPSort -> TCM Doc #-}

instance PrettyTCM (Elim' NLPat) where
  prettyTCM (IApply x y v) = prettyTCM v
  prettyTCM (Apply v) = prettyHiding v id <$> prettyTCM (unArg v)
  prettyTCM (Proj _ f)= "." <> prettyTCM f
{-# SPECIALIZE prettyTCM :: Elim' NLPat -> TCM Doc #-}

instance PrettyTCM (Type' NLPat) where
  prettyTCM = prettyTCM . unEl
{-# SPECIALIZE prettyTCM :: Type' NLPat -> TCM Doc #-}

instance PrettyTCM RewriteRule where
  prettyTCM (RewriteRule q gamma f ps rhs b c) = fsep
    [ prettyTCM q
    , prettyTCM gamma <+> " |- "
    , addContext gamma $ sep
      [ prettyTCM (PDef f ps)
      , " --> "
      , prettyTCM rhs
      , " : "
      , prettyTCM b
      ]
    ]
{-# SPECIALIZE prettyTCM :: RewriteRule -> TCM Doc #-}

instance PrettyTCM Occurrence where
  prettyTCM occ  = text $ "-[" ++ prettyShow occ ++ "]->"
{-# SPECIALIZE prettyTCM :: Occurrence -> TCM Doc #-}

-- | Pairing something with a node (for printing only).
data WithNode n a = WithNode n a

-- | Pretty-print something paired with a (printable) node.
-- | This intermediate typeclass exists to avoid UndecidableInstances.
class PrettyTCMWithNode a where
  prettyTCMWithNode :: (PrettyTCM n, MonadPretty m) => WithNode n a -> m Doc

instance PrettyTCMWithNode Occurrence where
  prettyTCMWithNode (WithNode n o) = prettyTCM o <+> prettyTCM n

instance (PrettyTCM n, PrettyTCMWithNode e) => PrettyTCM (Graph n e) where
  prettyTCM g = vcat $ map pr $ Map.assocs $ Graph.graph g
    where
      pr (n, es) = sep
        [ prettyTCM n
        , nest 2 $ vcat $ map (prettyTCMWithNode . uncurry WithNode) $ Map.assocs es
        ]
{-# SPECIALIZE prettyTCM :: (PrettyTCM n, PrettyTCMWithNode e) => (Graph n e) -> TCM Doc #-}

instance PrettyTCM SplitTag where
  prettyTCM (SplitCon c)  = prettyTCM c
  prettyTCM (SplitLit l)  = prettyTCM l
  prettyTCM SplitCatchall = return underscore
{-# SPECIALIZE prettyTCM :: SplitTag -> TCM Doc #-}

instance PrettyTCM Candidate where
  prettyTCM c = case candidateKind c of
    (GlobalCandidate q) -> prettyTCM q
    LocalCandidate      -> prettyTCM $ candidateTerm c
{-# SPECIALIZE prettyTCM :: Candidate -> TCM Doc #-}

instance PrettyTCM Key where
  prettyTCM = \case
    RigidK q a -> prettyTCM q <> superscript a
    LocalK i a -> "@" <> pretty i <> superscript a
    PiK        -> "Pi"
    ConstK     -> "Const"
    SortK      -> "Sort"
    FlexK      -> "_"

{-# SPECIALIZE prettyTCM :: Key -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Set.Set a) where
  prettyTCM = braces . prettyList_ . map prettyTCM . Set.toList

instance PrettyTCM a => PrettyTCM (DiscrimTree a) where
  prettyTCM = vcat . go "  " where
    go ind EmptyDT     = ["fail"]
    go ind (DoneDT it) = ["done" <+> prettyTCM it]
    go ind (CaseDT var branches fallthrough) =
      ["case" <+> prettyTCM var <+> "of"]
      ++ concatMap (\(k, v) -> abduct ind (prettyTCM k <> " →") v) (Map.toList branches)
      ++ (guard (not (null fallthrough)) >> abduct ind ("* →") fallthrough)

    abduct ind f v | (l:ls) <- go ind v = ((ind <> f) <+> l):map (ind <>) ls
    abduct ind _ _ = __IMPOSSIBLE__
