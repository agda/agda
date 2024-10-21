-- Each function here should either have an INLINE or a SPECIALIZE pragma.
--
module Agda.TypeChecking.Pretty
    ( module Agda.TypeChecking.Pretty
    , module Reexport
    ) where

import Prelude hiding ( null )

import Control.Applicative  (liftA2)
import Control.Monad
import Control.Monad.Except

import qualified Data.Foldable as Fold
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Data.String    ()
import Data.Semigroup (Semigroup((<>)))
import Data.Text      (Text)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( Pretty, prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
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
import qualified Agda.Utils.Maybe.Strict as S
import Agda.Utils.Size ( Sized, natSize )

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
---------------------------------------------------------------------------

type Doc = P.Doc

comma, colon, equals :: Applicative m => m Doc
comma  = pure P.comma        ; {-# INLINE comma  #-}
colon  = pure P.colon        ; {-# INLINE colon  #-}
equals = pure P.equals       ; {-# INLINE equals #-}

{-# INLINE pretty #-}
pretty :: (Applicative m, P.Pretty a) => a -> m Doc
pretty = pure . P.pretty

{-# INLINE prettyA #-}
prettyA :: (ToConcrete a, P.Pretty (ConOfAbs a), MonadAbsToCon m) => a -> m Doc
prettyA = AP.prettyA

{-# INLINE prettyAs #-}
-- Triggers error: [GHC-69441] RULE left-hand side too complicated to desugar: ...
-- {-# SPECIALIZE prettyAs :: (ToConcrete a, ConOfAbs a ~ [ce], P.Pretty ce) => a -> TCM Doc #-}
prettyAs :: (ToConcrete a, ConOfAbs a ~ [ce], P.Pretty ce, MonadAbsToCon m) => a -> m Doc
prettyAs = AP.prettyAs

fwords, text, multiLineText :: Applicative m => String -> m Doc
fwords        = pure . P.fwords        ; {-# INLINE fwords        #-}
text          = pure . P.text          ; {-# INLINE text          #-}
multiLineText = pure . P.multiLineText ; {-# INLINE multiLineText #-}

{-# INLINE pwords #-}
pwords :: Applicative m => String -> [m Doc]
pwords = map pure . P.pwords

sep, fsep, hsep, hcat, vcat, vsep :: (Applicative m, Foldable t) => t (m Doc) -> m Doc
sep  = fmap P.sep  . sequenceAFoldable  ; {-# SPECIALIZE NOINLINE sep  :: [TCM Doc] -> TCM Doc #-} ; {-# SPECIALIZE NOINLINE sep  :: List1 (TCM Doc) -> TCM Doc #-}
fsep = fmap P.fsep . sequenceAFoldable  ; {-# SPECIALIZE NOINLINE fsep :: [TCM Doc] -> TCM Doc #-} ; {-# SPECIALIZE NOINLINE fsep :: List1 (TCM Doc) -> TCM Doc #-}
hsep = fmap P.hsep . sequenceAFoldable  ; {-# SPECIALIZE NOINLINE hsep :: [TCM Doc] -> TCM Doc #-} ; {-# SPECIALIZE NOINLINE hsep :: List1 (TCM Doc) -> TCM Doc #-}
hcat = fmap P.hcat . sequenceAFoldable  ; {-# SPECIALIZE NOINLINE hcat :: [TCM Doc] -> TCM Doc #-} ; {-# SPECIALIZE NOINLINE hcat :: List1 (TCM Doc) -> TCM Doc #-}
vcat = fmap P.vcat . sequenceAFoldable  ; {-# SPECIALIZE NOINLINE vcat :: [TCM Doc] -> TCM Doc #-} ; {-# SPECIALIZE NOINLINE vcat :: List1 (TCM Doc) -> TCM Doc #-}
vsep = fmap P.vsep . sequenceAFoldable  ; {-# SPECIALIZE NOINLINE vsep :: [TCM Doc] -> TCM Doc #-} ; {-# SPECIALIZE NOINLINE vsep :: List1 (TCM Doc) -> TCM Doc #-}

{-# INLINE sequenceAFoldable #-}
-- | @sequenceAFoldable == sequenceA . Fold.toList@
sequenceAFoldable :: (Applicative m, Foldable t) => t (m a) -> m [a]
sequenceAFoldable = Fold.foldr (liftA2 (:)) (pure [])

{-# INLINE hang #-}
hang :: Applicative m => m Doc -> Int -> m Doc -> m Doc
hang p n q = P.hang <$> p <*> pure n <*> q

infixl 6 <+>, <?>
infixl 5 $$, $+$

($$), ($+$), (<+>), (<?>) :: Applicative m => m Doc -> m Doc -> m Doc
($$ ) = liftA2 (P.$$)   ; {-# INLINE ($$)  #-}
($+$) = liftA2 (P.$+$)  ; {-# INLINE ($+$) #-}
(<+>) = liftA2 (P.<+>)  ; {-# INLINE (<+>) #-}
(<?>) = liftA2 (P.<?>)  ; {-# INLINE (<?>) #-}

nest :: Functor m => Int -> m Doc -> m Doc
nest = fmap . P.nest    ; {-# INLINE nest  #-}

braces, dbraces, brackets, parens, parensNonEmpty
  , doubleQuotes, quotes :: Functor m => m Doc -> m Doc
braces         = fmap P.braces         ; {-# INLINE braces         #-}
dbraces        = fmap CP.dbraces       ; {-# INLINE dbraces        #-}
brackets       = fmap P.brackets       ; {-# INLINE brackets       #-}
parens         = fmap P.parens         ; {-# INLINE parens         #-}
parensNonEmpty = fmap P.parensNonEmpty ; {-# INLINE parensNonEmpty #-}
doubleQuotes   = fmap P.doubleQuotes   ; {-# INLINE doubleQuotes   #-}
quotes         = fmap P.quotes         ; {-# INLINE quotes         #-}

pshow :: (Applicative m, Show a) => a -> m Doc
pshow = pure . P.pshow                 ; {-# INLINE pshow          #-}

pluralS :: (Functor m, Sized a) => a -> m Doc -> m Doc
pluralS = fmap . P.pluralS             ; {-# INLINE pluralS        #-}

-- | Comma-separated list in brackets.
{-# INLINE prettyList #-}
prettyList :: (Applicative m, Foldable t) => t (m Doc) -> m Doc
prettyList = fmap P.pretty . sequenceAFoldable

-- | 'prettyList' without the brackets.
{-# SPECIALIZE prettyList_ :: [TCM Doc]       -> TCM Doc #-}
{-# SPECIALIZE prettyList_ :: List1 (TCM Doc) -> TCM Doc #-}
prettyList_ :: (Applicative m, Semigroup (m Doc), Foldable t) => t (m Doc) -> m Doc
prettyList_ = fsep . punctuate comma

{-# INLINABLE punctuate #-}
{-# SPECIALIZE punctuate :: TCM Doc -> [TCM Doc] -> [TCM Doc] #-}
{-# SPECIALIZE punctuate :: TCM Doc -> List1 (TCM Doc) -> [TCM Doc] #-}
punctuate :: (Applicative m, Semigroup (m Doc), Foldable t) => m Doc -> t (m Doc) -> [m Doc]
punctuate d ts
  | null ds   = []
  | otherwise = zipWith (<>) ds (replicate n d ++ [pure empty])
  where
    ds = Fold.toList ts
    n  = length ds - 1

{-# SPECIALIZE superscript :: Int -> TCM Doc #-}
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
instance {-# OVERLAPPING #-} Semigroup (TCM Doc) where
  (<>) = liftA2 (<>) ; {-# INLINE (<>) #-}

class PrettyTCM a where
  prettyTCM :: MonadPretty m => a -> m Doc

-- | Pretty print with a given context precedence
prettyTCMCtx :: (PrettyTCM a, MonadPretty m) => Precedence -> a -> m Doc
prettyTCMCtx p = withContextPrecedence p . prettyTCM

instance {-# OVERLAPPING #-} PrettyTCM String where prettyTCM = text   ; {-# INLINE prettyTCM #-}
instance PrettyTCM Text                       where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Bool                       where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM C.Name                     where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM C.QName                    where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM C.ImportedName             where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM C.LHS                      where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM TopLevelModuleName         where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Comparison                 where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Literal                    where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Nat                        where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM ProblemId                  where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Range                      where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM CheckpointId               where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM InteractionId              where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Relevance                  where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Quantity                   where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM Erased                     where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM ModalPolarity              where prettyTCM = pretty ; {-# INLINE prettyTCM #-}
instance PrettyTCM PolarityModality           where prettyTCM = pretty ; {-# INLINE prettyTCM #-}

instance PrettyTCM A.Expr                     where prettyTCM = prettyA; {-# INLINE prettyTCM #-}
instance PrettyTCM A.Pattern                  where prettyTCM = prettyA; {-# INLINE prettyTCM #-}
instance PrettyTCM A.TypedBinding             where prettyTCM = prettyA; {-# INLINE prettyTCM #-}

instance PrettyTCM Term               where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: Term              -> TCM Doc #-}
instance PrettyTCM Type               where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: Type              -> TCM Doc #-}
instance PrettyTCM Sort               where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: Sort              -> TCM Doc #-}
instance PrettyTCM DisplayTerm        where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: DisplayTerm       -> TCM Doc #-}
instance PrettyTCM NamedClause        where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: NamedClause       -> TCM Doc #-}
instance PrettyTCM (QNamed Clause)    where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (QNamed Clause)   -> TCM Doc #-}
instance PrettyTCM Level              where prettyTCM = prettyA <=< reify . Level ; {-# SPECIALIZE prettyTCM :: Level             -> TCM Doc #-}
instance PrettyTCM (Named_ Term)      where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Named_ Term)     -> TCM Doc #-}
instance PrettyTCM (Arg Term)         where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Arg Term)        -> TCM Doc #-}
instance PrettyTCM (Arg Type)         where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Arg Type)        -> TCM Doc #-}
instance PrettyTCM (Arg Bool)         where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Arg Bool)        -> TCM Doc #-}
instance PrettyTCM (Arg String)       where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Arg String)      -> TCM Doc #-}
instance PrettyTCM (Arg A.Expr)       where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Arg A.Expr)      -> TCM Doc #-}
instance PrettyTCM (NamedArg A.Expr)  where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (NamedArg A.Expr) -> TCM Doc #-}
instance PrettyTCM (NamedArg Term)    where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (NamedArg Term)   -> TCM Doc #-}
instance PrettyTCM (Dom Type)         where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: (Dom Type)        -> TCM Doc #-}
instance PrettyTCM ContextEntry       where prettyTCM = prettyA <=< reify         ; {-# SPECIALIZE prettyTCM :: ContextEntry      -> TCM Doc #-}

instance PrettyTCM Permutation        where prettyTCM = text . show               ; {-# SPECIALIZE prettyTCM :: Permutation       -> TCM Doc #-}
instance PrettyTCM Polarity           where prettyTCM = text . show               ; {-# SPECIALIZE prettyTCM :: Polarity          -> TCM Doc #-}
instance PrettyTCM IsForced           where prettyTCM = text . show               ; {-# SPECIALIZE prettyTCM :: IsForced          -> TCM Doc #-}

instance PrettyTCM Name         where prettyTCM = fmap P.pretty . abstractToConcrete_ ; {-# SPECIALIZE prettyTCM :: Name          -> TCM Doc #-}
instance PrettyTCM QName        where prettyTCM = fmap P.pretty . abstractToConcrete_ ; {-# SPECIALIZE prettyTCM :: QName         -> TCM Doc #-}
instance PrettyTCM ModuleName   where prettyTCM = fmap P.pretty . abstractToConcrete_ ; {-# SPECIALIZE prettyTCM :: ModuleName    -> TCM Doc #-}

instance PrettyTCM AbstractName where prettyTCM = prettyTCM . anameName           ; {-# SPECIALIZE prettyTCM :: AbstractName -> TCM Doc #-}
instance PrettyTCM ConHead      where prettyTCM = prettyTCM . conName             ; {-# SPECIALIZE prettyTCM :: ConHead      -> TCM Doc #-}
instance PrettyTCM DBPatVar     where prettyTCM = prettyTCM . var . dbPatVarIndex ; {-# SPECIALIZE prettyTCM :: DBPatVar     -> TCM Doc #-}
instance PrettyTCM EqualityView where prettyTCM = prettyTCM . equalityUnview      ; {-# SPECIALIZE prettyTCM :: EqualityView -> TCM Doc #-}

-- Functors

instance (PrettyTCM a, Subst a) => PrettyTCM (Abs a) where
  prettyTCM a = underAbstraction_ a prettyTCM
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Abs a -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Closure a) where
  prettyTCM cl = enterClosure cl prettyTCM
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Closure a -> TCM Doc #-}

instance {-# OVERLAPPABLE #-} PrettyTCM a => PrettyTCM [a] where
  prettyTCM = prettyList . map prettyTCM
{-# SPECIALIZE prettyTCM :: PrettyTCM a => [a] -> TCM Doc #-}

instance {-# OVERLAPPABLE #-} PrettyTCM a => PrettyTCM (List1 a) where
  prettyTCM = prettyList . fmap prettyTCM
{-# SPECIALIZE prettyTCM :: PrettyTCM a => [a] -> TCM Doc #-}

instance {-# OVERLAPPABLE #-} PrettyTCM a => PrettyTCM (Maybe a) where
  prettyTCM = maybe empty prettyTCM
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Maybe a -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (Set a) where
  prettyTCM = braces . prettyList_ . map prettyTCM . Set.toList
{-# SPECIALIZE prettyTCM :: PrettyTCM a => Set a -> TCM Doc #-}

instance (PrettyTCM a, PrettyTCM b) => PrettyTCM (a,b) where
  prettyTCM (a, b) = parens $ prettyTCM a <> comma <> prettyTCM b
{-# SPECIALIZE prettyTCM :: (PrettyTCM a, PrettyTCM b) => (a, b) -> TCM Doc #-}

instance (PrettyTCM a, PrettyTCM b, PrettyTCM c) => PrettyTCM (a,b,c) where
  prettyTCM (a, b, c) = parens $
    prettyTCM a <> comma <> prettyTCM b <> comma <> prettyTCM c
{-# SPECIALIZE prettyTCM :: (PrettyTCM a, PrettyTCM b, PrettyTCM c) => (a, b, c) -> TCM Doc #-}

instance PrettyTCM a => PrettyTCM (MaybeReduced a) where
  prettyTCM = prettyTCM . ignoreReduced
{-# SPECIALIZE prettyTCM :: PrettyTCM a => MaybeReduced a -> TCM Doc #-}

instance (Pretty a, PrettyTCM a, EndoSubst a) => PrettyTCM (Substitution' a) where
  prettyTCM IdS        = "idS"
  prettyTCM (Wk m IdS) = "wkS" <+> pretty m
  prettyTCM (EmptyS _) = "emptyS"
  prettyTCM rho = prettyTCM u <+> comma <+> prettyTCM rho1
    where
      (rho1, rho2) = splitS 1 rho
      u            = lookupS rho2 0
{-# SPECIALIZE prettyTCM :: (Pretty a, PrettyTCM a, EndoSubst a) => Substitution' a -> TCM Doc #-}

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

instance PrettyTCM Modality where
  prettyTCM mod = hsep
    [ prettyTCM (getQuantity mod)
    , prettyTCM (getRelevance mod)
    , prettyTCM (getModalPolarity mod)
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

instance PrettyTCM Telescope where
  prettyTCM tel = P.fsep . map P.pretty <$> do
      abstractToConcreteTelescope =<< reify tel
{-# SPECIALIZE prettyTCM :: Telescope -> TCM Doc #-}

newtype PrettyContext = PrettyContext Context

instance PrettyTCM PrettyContext where
  prettyTCM (PrettyContext ctx) = prettyTCM $ telFromList' nameToArgName $ reverse ctx
{-# SPECIALIZE prettyTCM :: PrettyContext -> TCM Doc #-}

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

-- | For unquote.
{-# SPECIALIZE prettyR :: (R.ToAbstract r, PrettyTCM (R.AbsOfRef r)) => r -> TCM Doc #-}
prettyR :: (R.ToAbstract r, PrettyTCM (R.AbsOfRef r), MonadPretty m, MonadError TCErr m) => r -> m Doc
prettyR = prettyTCM <=< toAbstractWithoutImplicit

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
{-# SPECIALIZE NOINLINE prettyTCM :: (PrettyTCM n, PrettyTCMWithNode e) => (Graph n e) -> TCM Doc #-}

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
{-# SPECIALIZE prettyTCM :: PrettyTCM a => DiscrimTree a -> TCM Doc #-}
