{-# LANGUAGE UndecidableInstances #-}

module Agda.TypeChecking.Pretty
    ( module Agda.TypeChecking.Pretty
    -- This re-export can be removed once <GHC-8.4 is dropped.
    , module Data.Semigroup
    ) where

import Prelude hiding ( null )

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.String
import Data.Semigroup (Semigroup((<>)))

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.ReflectedToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import qualified Agda.Syntax.Translation.ReflectedToAbstract as R
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract.Pretty as AP
import Agda.Syntax.Concrete.Pretty (bracesAndSemicolons)
import qualified Agda.Syntax.Concrete.Pretty as CP
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Scope.Base  (AbstractName(..))
import Agda.Syntax.Scope.Monad (withContextPrecedence)

import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Substitute

import Agda.Utils.Except
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Permutation (Permutation)
import Agda.Utils.Pretty (Pretty, prettyShow)
import qualified Agda.Utils.Pretty as P

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
---------------------------------------------------------------------------

type Doc = P.Doc

comma, colon, equals :: Monad m => m Doc
comma  = return P.comma
colon  = return P.colon
equals = return P.equals

pretty :: (Monad m, P.Pretty a) => a -> m Doc
pretty x = return $ P.pretty x

prettyA :: (P.Pretty c, ToConcrete a c, MonadAbsToCon m) => a -> m Doc
prettyA x = AP.prettyA x

prettyAs :: (P.Pretty c, ToConcrete a [c], MonadAbsToCon m) => a -> m Doc
prettyAs x = AP.prettyAs x

text :: Monad m => String -> m Doc
text s = return $ P.text s

multiLineText :: Monad m => String -> m Doc
multiLineText s = return $ P.multiLineText s

pwords :: Monad m => String -> [m Doc]
pwords s = map return $ P.pwords s

fwords :: Monad m => String -> m Doc
fwords s = return $ P.fwords s

sep, fsep, hsep, hcat, vcat :: Monad m => [m Doc] -> m Doc
sep ds  = P.sep <$> sequence ds
fsep ds = P.fsep <$> sequence ds
hsep ds = P.hsep <$> sequence ds
hcat ds = P.hcat <$> sequence ds
vcat ds = P.vcat <$> sequence ds

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
prettyList :: (Monad m, Semigroup (m Doc)) => [m Doc] -> m Doc
prettyList ds = P.pretty <$> sequence ds

-- | 'prettyList' without the brackets.
prettyList_ :: (Monad m, Semigroup (m Doc)) => [m Doc] -> m Doc
prettyList_ ds = fsep $ punctuate comma ds

punctuate :: (Applicative m, Semigroup (m Doc)) => m Doc -> [m Doc] -> [m Doc]
punctuate _ [] = []
punctuate d ds = zipWith (<>) ds (replicate n d ++ [pure empty])
  where
    n = length ds - 1

---------------------------------------------------------------------------
-- * The PrettyTCM class
---------------------------------------------------------------------------

type MonadPretty m =
  ( MonadReify m
  , MonadAbsToCon m
  , IsString (m Doc)
  , Null (m Doc)
  , Semigroup (m Doc)
  )

class PrettyTCM a where
  prettyTCM :: MonadPretty m => a -> m Doc

-- | Pretty print with a given context precedence
prettyTCMCtx :: (PrettyTCM a, MonadPretty m) => Precedence -> a -> m Doc
prettyTCMCtx p = withContextPrecedence p . prettyTCM

instance PrettyTCM Bool        where prettyTCM = pretty
instance PrettyTCM C.Name      where prettyTCM = pretty
instance PrettyTCM C.QName     where prettyTCM = pretty
instance PrettyTCM Comparison  where prettyTCM = pretty
instance PrettyTCM Literal     where prettyTCM = pretty
instance PrettyTCM Nat         where prettyTCM = pretty
instance PrettyTCM ProblemId   where prettyTCM = pretty
instance PrettyTCM Range       where prettyTCM = pretty
instance PrettyTCM CheckpointId where prettyTCM = pretty
-- instance PrettyTCM Interval where prettyTCM = pretty
-- instance PrettyTCM Position where prettyTCM = pretty

instance PrettyTCM a => PrettyTCM (Closure a) where
  prettyTCM cl = enterClosure cl prettyTCM

instance PrettyTCM a => PrettyTCM [a] where
  prettyTCM = prettyList . map prettyTCM

instance (PrettyTCM a, PrettyTCM b) => PrettyTCM (a,b) where
  prettyTCM (a, b) = parens $ prettyTCM a <> comma <> prettyTCM b

instance (PrettyTCM a, PrettyTCM b, PrettyTCM c) => PrettyTCM (a,b,c) where
  prettyTCM (a, b, c) = parens $
    prettyTCM a <> comma <> prettyTCM b <> comma <> prettyTCM c

instance PrettyTCM Term         where prettyTCM = prettyA <=< reify
instance PrettyTCM Type         where prettyTCM = prettyA <=< reify
instance PrettyTCM Sort         where prettyTCM = prettyA <=< reify
instance PrettyTCM DisplayTerm  where prettyTCM = prettyA <=< reify
instance PrettyTCM NamedClause  where prettyTCM = prettyA <=< reify
instance PrettyTCM (QNamed Clause) where prettyTCM = prettyA <=< reify
instance PrettyTCM Level        where prettyTCM = prettyA <=< reify . Level
instance PrettyTCM Permutation  where prettyTCM = text . show
instance PrettyTCM Polarity     where prettyTCM = text . show
instance PrettyTCM IsForced     where prettyTCM = text . show

prettyR
  :: (R.ToAbstract r a, PrettyTCM a, MonadPretty m, MonadError TCErr m)
  => r -> m Doc
prettyR = prettyTCM <=< toAbstractWithoutImplicit

instance (Pretty a, PrettyTCM a, Subst a a) => PrettyTCM (Substitution' a) where
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

instance PrettyTCM a => PrettyTCM (Judgement a) where
  prettyTCM (HasType a cmp t) = prettyTCM a <+> ":" <+> prettyTCM t
  prettyTCM (IsSort  a t) = "Sort" <+> prettyTCM a <+> ":" <+> prettyTCM t

instance PrettyTCM MetaId where
  prettyTCM x = do
    mn <- getMetaNameSuggestion x
    pretty $ NamedMeta mn x

instance PrettyTCM a => PrettyTCM (Blocked a) where
  prettyTCM (Blocked x a) = ("[" <+> prettyTCM a <+> "]") <> text (P.prettyShow x)
  prettyTCM (NotBlocked _ x) = prettyTCM x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Named_ a) where
  prettyTCM x = prettyA =<< reify x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Arg a) where
  prettyTCM x = prettyA =<< reify x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Dom a) where
  prettyTCM x = prettyA =<< reify x

instance (PrettyTCM k, PrettyTCM v) => PrettyTCM (Map k v) where
  prettyTCM m = "Map" <> braces (sep $ punctuate comma
    [ hang (prettyTCM k <+> "=") 2 (prettyTCM v) | (k, v) <- Map.toList m ])

instance {-# OVERLAPPING #-} PrettyTCM ArgName where
  prettyTCM = text . P.prettyShow

-- instance (Reify a e, ToConcrete e c, P.Pretty c, PrettyTCM a) => PrettyTCM (Elim' a) where
instance PrettyTCM Elim where
  prettyTCM (IApply x y v) = "I$" <+> prettyTCM v
  prettyTCM (Apply v) = "$" <+> prettyTCM v
  prettyTCM (Proj _ f)= "." <> prettyTCM f

instance PrettyTCM a => PrettyTCM (MaybeReduced a) where
  prettyTCM = prettyTCM . ignoreReduced

instance PrettyTCM EqualityView where
  prettyTCM v = prettyTCM $ equalityUnview v

instance PrettyTCM A.Expr where
  prettyTCM = prettyA

instance PrettyTCM A.TypedBinding where
  prettyTCM = prettyA

instance PrettyTCM Relevance where
  prettyTCM = pretty

instance PrettyTCM Quantity where
  prettyTCM = pretty

instance PrettyTCM Modality where
  prettyTCM mod = hsep
    [ prettyTCM (getQuantity mod)
    , prettyTCM (getRelevance mod)
    ]

instance PrettyTCM ProblemConstraint where
  prettyTCM (PConstr pids c) = prettyTCM c <?> prPids (Set.toList pids)
    where
      prPids []    = empty
      prPids [pid] = parens $ "problem" <+> prettyTCM pid
      prPids pids  = parens $ "problems" <+> fsep (punctuate "," $ map prettyTCM pids)

instance PrettyTCM Constraint where
    prettyTCM c = case c of
        ValueCmp cmp ty s t -> prettyCmp (prettyTCM cmp) s t <?> prettyTCM ty
        ValueCmpOnFace cmp p ty s t ->
            sep [ prettyTCM p <+> "|"
                , prettyCmp (prettyTCM cmp) s t ]
            <?> (":" <+> prettyTCMCtx TopCtx ty)
        ElimCmp cmps fs t v us vs -> prettyCmp "~~" us vs   <?> (":" <+> prettyTCMCtx TopCtx t)
        LevelCmp cmp a b         -> prettyCmp (prettyTCM cmp) a b
        TelCmp a b cmp tela telb -> prettyCmp (prettyTCM cmp) tela telb
        SortCmp cmp s1 s2        -> prettyCmp (prettyTCM cmp) s1 s2
        Guarded c pid            -> prettyTCM c <?> parens ("blocked by problem" <+> prettyTCM pid)
        UnBlock m   -> do
            -- BlockedConst t <- mvInstantiation <$> lookupMeta m
            mi <- mvInstantiation <$> lookupMeta m
            case mi of
              BlockedConst t -> prettyCmp ":=" m t
              PostponedTypeCheckingProblem cl _ -> enterClosure cl $ \p ->
                prettyCmp ":=" m p
              Open{}  -> __IMPOSSIBLE__
              OpenInstance{} -> __IMPOSSIBLE__
              InstV{} -> empty
              -- Andreas, 2017-01-11, issue #2637:
              -- The size solver instantiates some metas with infinity
              -- without cleaning up the UnBlock constraints.
              -- Thus, this case is not IMPOSSIBLE.
              --
              -- InstV args t -> do
              --   reportS "impossible" 10
              --     [ "UnBlock meta " ++ show m ++ " surprisingly has InstV instantiation:"
              --     , show m ++ show args ++ " := " ++ show t
              --     ]
              --   __IMPOSSIBLE__
        FindInstance m mb mcands -> do
            t <- getMetaType m
            sep [ "Resolve instance argument" <+> blk
                    <?> prettyCmp ":" m t
                , cands
                ]
          where
            blk = case mb of
                    Nothing -> empty
                    Just b  -> parens $ "blocked on" <+> pretty b
            cands =
              case mcands of
                Nothing -> "No candidates yet"
                Just cnds ->
                  hang "Candidates" 2 $ vcat
                    [ hang (overlap c <+> prettyTCM c <+> ":") 2 $
                            prettyTCM (candidateType c) | c <- cnds ]
              where overlap c | candidateOverlappable c = "overlap"
                              | otherwise               = empty
        IsEmpty r t ->
            "Is empty:" <?> prettyTCMCtx TopCtx t
        CheckSizeLtSat t ->
            "Is not empty type of sizes:" <?> prettyTCMCtx TopCtx t
        CheckFunDef d i q cs -> do
            t <- defType <$> getConstInfo q
            "Check definition of" <+> prettyTCM q <+> ":" <+> prettyTCM t
        HasBiggerSort a -> "Has bigger sort:" <+> prettyTCM a
        HasPTSRule a b -> "Has PTS rule:" <+> case b of
          NoAbs _ b -> prettyTCM (a,b)
          Abs x b   -> "(" <> (prettyTCM a <+> "," <+> addContext x (prettyTCM b)) <> ")"
        UnquoteTactic _ v _ _ -> do
          e <- reify v
          prettyTCM (A.App A.defaultAppInfo_ (A.Unquote A.exprNoRange) (defaultNamedArg e))
        CheckMetaInst x -> do
          m <- lookupMeta x
          case mvJudgement m of
            HasType{ jMetaType = t } -> prettyTCM x <+> ":" <+> prettyTCM t
            IsSort{} -> prettyTCM x <+> "is a sort"

      where
        prettyCmp
          :: (PrettyTCM a, PrettyTCM b, MonadPretty m)
          => m Doc -> a -> b -> m Doc
        prettyCmp cmp x y = prettyTCMCtx TopCtx x <?> (cmp <+> prettyTCMCtx TopCtx y)

instance PrettyTCM CompareAs where
  prettyTCM (AsTermsOf a) = ":" <+> prettyTCMCtx TopCtx a
  prettyTCM AsSizes       = ":" <+> do prettyTCM =<< sizeType
  prettyTCM AsTypes       = empty

instance PrettyTCM TypeCheckingProblem where
  prettyTCM (CheckExpr cmp e a) =
    sep [ prettyA e <+> ":?", prettyTCM a ]
  prettyTCM (CheckArgs _ _ es t0 t1 _) =
    sep [ parens $ "_ :" <+> prettyTCM t0
        , nest 2 $ prettyList $ map prettyA es
        , nest 2 $ ":?" <+> prettyTCM t1 ]
  prettyTCM (CheckProjAppToKnownPrincipalArg cmp e _ _ _ t _ _ _) = prettyTCM (CheckExpr cmp e t)
  prettyTCM (CheckLambda cmp (Arg ai (xs, mt)) e t) =
    sep [ return CP.lambda <+>
          (CP.prettyRelevance ai .
           CP.prettyHiding ai (if isNothing mt && length xs == 1 then id
                               else P.parens) <$> do
            fsep $
              map prettyTCM xs ++
              caseMaybe mt [] (\ a -> [":", prettyTCM a])) <+>
          return CP.arrow <+>
          prettyTCM e <+>
          ":?"
        , prettyTCM t
        ]
  prettyTCM (DoQuoteTerm _ v _) = do
    e <- reify v
    prettyTCM (A.App A.defaultAppInfo_ (A.QuoteTerm A.exprNoRange) (defaultNamedArg e))

instance PrettyTCM a => PrettyTCM (WithHiding a) where
  prettyTCM (WithHiding h a) = CP.prettyHiding h id <$> prettyTCM a

instance PrettyTCM Name where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x

instance PrettyTCM QName where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x

instance PrettyTCM ModuleName where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x

instance PrettyTCM AbstractName where
  prettyTCM = prettyTCM . anameName

instance PrettyTCM ConHead where
  prettyTCM = prettyTCM . conName

instance PrettyTCM Telescope where
  prettyTCM tel = P.fsep . map P.pretty <$> (do
      tel <- reify tel
      runAbsToCon $ bindToConcrete tel return
    )

newtype PrettyContext = PrettyContext Context

instance PrettyTCM PrettyContext where
  prettyTCM (PrettyContext ctx) = prettyTCM $ telFromList' nameToArgName $ reverse ctx

instance PrettyTCM DBPatVar where
  prettyTCM = prettyTCM . var . dbPatVarIndex

instance PrettyTCM a => PrettyTCM (Pattern' a) where
  prettyTCM (IApplyP _ _ _ x)    = prettyTCM x
  prettyTCM (VarP _ x)    = prettyTCM x
  prettyTCM (DotP _ t)    = ".(" <> prettyTCM t <> ")"
  prettyTCM (DefP o q ps) = parens $
        prettyTCM q <+> fsep (map (prettyTCM . namedArg) ps)
  prettyTCM (ConP c i ps) = (if b then braces else parens) $ prTy $
        prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
        where
        b = conPRecord i && patOrigin (conPInfo i) /= PatOCon
        showRec :: MonadPretty m => m Doc -- Defined, but currently not used
        showRec = sep
          [ "record"
          , bracesAndSemicolons <$> zipWithM showField (conFields c) ps
          ]
        showField :: MonadPretty m => Arg QName -> NamedArg (Pattern' a) -> m Doc -- NB:: Defined but not used
        showField (Arg ai x) p =
          sep [ prettyTCM (A.qnameName x) <+> "=" , nest 2 $ prettyTCM $ namedArg p ]
        showCon :: MonadPretty m => m Doc -- NB:: Defined but not used
        showCon = parens $ prTy $ prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
        prTy d = d -- caseMaybe (conPType i) d $ \ t -> d  <+> ":" <+> prettyTCM t
  prettyTCM (LitP _ l)    = text (P.prettyShow l)
  prettyTCM (ProjP _ q)   = text ("." ++ P.prettyShow q)

-- | Proper pretty printing of patterns:
prettyTCMPatterns :: MonadPretty m => [NamedArg DeBruijnPattern] -> m [Doc]
prettyTCMPatterns = mapM prettyA <=< reifyPatterns

prettyTCMPatternList :: MonadPretty m => [NamedArg DeBruijnPattern] -> m Doc
prettyTCMPatternList = prettyList . map prettyA <=< reifyPatterns

instance PrettyTCM (Elim' DisplayTerm) where
  prettyTCM (IApply x y v) = "$" <+> prettyTCM v
  prettyTCM (Apply v) = "$" <+> prettyTCM (unArg v)
  prettyTCM (Proj _ f)= "." <> prettyTCM f

instance PrettyTCM NLPat where
  prettyTCM (PVar x bvs) = prettyTCM (Var x (map (Apply . fmap var) bvs))
  prettyTCM (PDef f es) = parens $
    prettyTCM f <+> fsep (map prettyTCM es)
  prettyTCM (PLam i u)  = parens $
    text ("λ " ++ absName u ++ " →") <+>
    addContext (absName u) (prettyTCM $ absBody u)
  prettyTCM (PPi a b)   = parens $
    text ("(" ++ absName b ++ " :") <+> (prettyTCM (unDom a) <> ") →") <+>
    addContext (absName b) (prettyTCM $ unAbs b)
  prettyTCM (PSort s)        = prettyTCM s
  prettyTCM (PBoundVar i []) = prettyTCM (var i)
  prettyTCM (PBoundVar i es) = parens $ prettyTCM (var i) <+> fsep (map prettyTCM es)
  prettyTCM (PTerm t)   = "." <> parens (prettyTCM t)

instance PrettyTCM NLPType where
  prettyTCM (NLPType s a) = prettyTCM a

instance PrettyTCM NLPSort where
  prettyTCM = \case
    PType l   -> parens $ "Set" <+> prettyTCM l
    PProp l   -> parens $ "Prop" <+> prettyTCM l
    PInf      -> prettyTCM (Inf :: Sort)
    PSizeUniv -> prettyTCM (SizeUniv :: Sort)

instance PrettyTCM (Elim' NLPat) where
  prettyTCM (IApply x y v) = prettyTCM v
  prettyTCM (Apply v) = prettyTCM (unArg v)
  prettyTCM (Proj _ f)= "." <> prettyTCM f

instance PrettyTCM (Type' NLPat) where
  prettyTCM = prettyTCM . unEl

instance PrettyTCM RewriteRule where
  prettyTCM (RewriteRule q gamma f ps rhs b) = fsep
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

instance PrettyTCM Occurrence where
  prettyTCM occ  = text $ "-[" ++ prettyShow occ ++ "]->"

-- | Pairing something with a node (for printing only).
data WithNode n a = WithNode n a

instance PrettyTCM n => PrettyTCM (WithNode n Occurrence) where
  prettyTCM (WithNode n o) = prettyTCM o <+> prettyTCM n

instance (PrettyTCM n, PrettyTCM (WithNode n e)) => PrettyTCM (Graph n e) where
  prettyTCM g = vcat $ map pr $ Map.assocs $ Graph.graph g
    where
      pr (n, es) = sep
        [ prettyTCM n
        , nest 2 $ vcat $ map (prettyTCM . uncurry WithNode) $ Map.assocs es
        ]

instance PrettyTCM SplitTag where
  prettyTCM (SplitCon c)  = prettyTCM c
  prettyTCM (SplitLit l)  = prettyTCM l
  prettyTCM SplitCatchall = return underscore

instance PrettyTCM Candidate where
  prettyTCM c = case candidateKind c of
    (GlobalCandidate q) -> prettyTCM q
    LocalCandidate      -> prettyTCM $ candidateTerm c
