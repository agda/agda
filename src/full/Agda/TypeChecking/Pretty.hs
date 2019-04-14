{-# LANGUAGE CPP                  #-}
{-# LANGUAGE UndecidableInstances #-}

-- To define <>, we need to add with GHC >= 8.4
--
--   import Prelude hiding ((<>))
--
-- but using that gives warnings and doesn't silence -Wsemigroup in
-- some versions of GHC.
#if __GLASGOW_HASKELL__ >= 800 && __GLASGOW_HASKELL__ < 804
{-# OPTIONS_GHC -Wno-semigroup #-}
#endif

module Agda.TypeChecking.Pretty where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), null )
#else
import Prelude hiding ( null )
#endif

import Control.Applicative hiding (empty)
import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.ReflectedToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import qualified Agda.Syntax.Translation.ReflectedToAbstract as R
import qualified Agda.Syntax.Reflected as R
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Reflected as R
import qualified Agda.Syntax.Abstract.Pretty as AP
import Agda.Syntax.Concrete.Pretty (bracesAndSemicolons)
import qualified Agda.Syntax.Concrete.Pretty as CP
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Scope.Monad (withContextPrecedence)

import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (equalityUnview)
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Substitute

import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Permutation (Permutation)
import Agda.Utils.Pretty (Pretty, prettyShow)
import qualified Agda.Utils.Pretty as P

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
---------------------------------------------------------------------------

type Doc = P.Doc

comma, colon, equals :: TCM Doc
comma  = return P.comma
colon  = return P.colon
equals = return P.equals

pretty :: P.Pretty a => a -> TCM Doc
pretty x = return $ P.pretty x

prettyA :: (P.Pretty c, ToConcrete a c) => a -> TCM Doc
prettyA x = AP.prettyA x

prettyAs :: (P.Pretty c, ToConcrete a [c]) => a -> TCM Doc
prettyAs x = AP.prettyAs x

text :: String -> TCM Doc
text s = return $ P.text s

multiLineText :: String -> TCM Doc
multiLineText s = return $ P.multiLineText s

pwords :: String -> [TCM Doc]
pwords s = map return $ P.pwords s

fwords :: String -> TCM Doc
fwords s = return $ P.fwords s

sep, fsep, hsep, hcat, vcat :: [TCM Doc] -> TCM Doc
sep ds  = P.sep <$> sequence ds
fsep ds = P.fsep <$> sequence ds
hsep ds = P.hsep <$> sequence ds
hcat ds = P.hcat <$> sequence ds
vcat ds = P.vcat <$> sequence ds

hang :: TCM Doc -> Int -> TCM Doc -> TCM Doc
hang p n q = P.hang <$> p <*> pure n <*> q

infixl 6 <>, <+>, <?>
infixl 5 $$, $+$

($$), ($+$), (<>), (<+>), (<?>) :: TCM Doc -> TCM Doc -> TCM Doc
d1 $$ d2  = (P.$$) <$> d1 <*> d2
d1 $+$ d2 = (P.$+$) <$> d1 <*> d2
d1 <> d2  = (P.<>) <$> d1 <*> d2
d1 <+> d2 = (P.<+>) <$> d1 <*> d2
d1 <?> d2 = (P.<?>) <$> d1 <*> d2

nest :: Int -> TCM Doc -> TCM Doc
nest n d   = P.nest n <$> d

braces, dbraces, brackets, parens :: TCM Doc -> TCM Doc
braces d   = P.braces <$> d
dbraces d  = CP.dbraces <$> d
brackets d = P.brackets <$> d
parens d   = P.parens <$> d

pshow :: Show a => a -> TCM Doc
pshow = pure . P.pshow

-- | Comma-separated list in brackets.
prettyList :: [TCM Doc] -> TCM Doc
prettyList ds = P.pretty <$> sequence ds

-- | 'prettyList' without the brackets.
prettyList_ :: [TCM Doc] -> TCM Doc
prettyList_ ds = fsep $ punctuate comma ds

punctuate :: TCM Doc -> [TCM Doc] -> [TCM Doc]
punctuate _ [] = []
punctuate d ds = zipWith (<>) ds (replicate n d ++ [empty])
  where
    n = length ds - 1

---------------------------------------------------------------------------
-- * The PrettyTCM class
---------------------------------------------------------------------------

class PrettyTCM a where
  prettyTCM :: a -> TCM Doc

-- | Pretty print with a given context precedence
prettyTCMCtx :: PrettyTCM a => Precedence -> a -> TCM Doc
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
instance PrettyTCM R.Term       where prettyTCM = prettyA <=< toAbstractWithoutImplicit


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
  prettyTCM (HasType a t) = prettyTCM a <+> ":" <+> prettyTCM t
  prettyTCM (IsSort  a t) = "Sort" <+> prettyTCM a <+> ":" <+> prettyTCM t

instance PrettyTCM MetaId where
  prettyTCM x = do
    mn <- getMetaNameSuggestion x
    pretty $ NamedMeta mn x

instance PrettyTCM a => PrettyTCM (Blocked a) where
  prettyTCM (Blocked x a) = "[" <+> prettyTCM a <+> "]" <> text (P.prettyShow x)
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
  prettyTCM Irrelevant = "."
  prettyTCM NonStrict  = ".."
  prettyTCM Relevant   = empty

instance PrettyTCM ProblemConstraint where
  prettyTCM (PConstr pids c)
    | Set.null pids = prettyTCM c
    | otherwise     = prettyList (map prettyTCM $ Set.toList pids) <+> prettyTCM c

instance PrettyTCM Constraint where
    prettyTCM c = case c of
        ValueCmp cmp ty s t      -> prettyCmp (prettyTCM cmp) s t <?> (":" <+> prettyTCMCtx TopCtx ty)
        ValueCmpOnFace cmp p ty s t ->
            sep [ prettyTCM p <+> "|"
                , prettyCmp (prettyTCM cmp) s t ]
            <?> (":" <+> prettyTCMCtx TopCtx ty)
        ElimCmp cmps fs t v us vs -> prettyCmp "~~" us vs   <?> (":" <+> prettyTCMCtx TopCtx t)
        LevelCmp cmp a b         -> prettyCmp (prettyTCM cmp) a b
        TypeCmp cmp a b          -> prettyCmp (prettyTCM cmp) a b
        TelCmp a b cmp tela telb -> prettyCmp (prettyTCM cmp) tela telb
        SortCmp cmp s1 s2        -> prettyCmp (prettyTCM cmp) s1 s2
        Guarded c pid            -> prettyTCM c <?> (brackets $ "blocked on problem" <+> prettyTCM pid)
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
              --   reportSLn "impossible" 10 $ unlines
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
                  hang "Candidates" 2 $
                    vcat [ hang (overlap c <+> prettyTCM (candidateTerm c) <+> ":") 2 $
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
          Abs x b   -> "(" <> prettyTCM a <+> "," <+> addContext x (prettyTCM b) <> ")"
        UnquoteTactic _ v _ _ -> do
          e <- reify v
          prettyTCM (A.App A.defaultAppInfo_ (A.Unquote A.exprNoRange) (defaultNamedArg e))

      where
        prettyCmp :: (PrettyTCM a, PrettyTCM b) => TCM Doc -> a -> b -> TCM Doc
        prettyCmp cmp x y = prettyTCMCtx TopCtx x <?> (cmp <+> prettyTCMCtx TopCtx y)


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
        b = maybe False (/= PatOCon) $ conPRecord i
        showRec :: TCM Doc
        showRec = sep
          [ "record"
          , bracesAndSemicolons <$> zipWithM showField (conFields c) ps
          ]
        showField (Arg ai x) p =
          sep [ prettyTCM (A.qnameName x) <+> "=" , nest 2 $ prettyTCM $ namedArg p ]
        showCon = parens $ prTy $ prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
        prTy d = d -- caseMaybe (conPType i) d $ \ t -> d  <+> ":" <+> prettyTCM t
  prettyTCM (LitP l)      = text (P.prettyShow l)
  prettyTCM (ProjP _ q)   = text ("." ++ P.prettyShow q)

-- | Proper pretty printing of patterns:
prettyTCMPatterns :: [NamedArg DeBruijnPattern] -> TCM [Doc]
prettyTCMPatterns = mapM prettyA <=< reifyPatterns

prettyTCMPatternList :: [NamedArg DeBruijnPattern] -> TCM Doc
prettyTCMPatternList = prettyList . map prettyA <=< reifyPatterns

instance PrettyTCM (Elim' DisplayTerm) where
  prettyTCM (IApply x y v) = "$" <+> prettyTCM v
  prettyTCM (Apply v) = "$" <+> prettyTCM (unArg v)
  prettyTCM (Proj _ f)= "." <> prettyTCM f

instance PrettyTCM NLPat where
  prettyTCM (PVar x bvs) = prettyTCM (Var x (map (Apply . fmap var) bvs))
  prettyTCM (PWild)     = text $ "_"
  prettyTCM (PDef f es) = parens $
    prettyTCM f <+> fsep (map prettyTCM es)
  prettyTCM (PLam i u)  = parens $
    text ("λ " ++ absName u ++ " →") <+>
    (addContext (absName u) $ prettyTCM $ absBody u)
  prettyTCM (PPi a b)   = parens $
    text ("(" ++ absName b ++ " :") <+> prettyTCM (unDom a) <> ") →" <+>
    (addContext (absName b) $ prettyTCM $ unAbs b)
  prettyTCM (PBoundVar i []) = prettyTCM (var i)
  prettyTCM (PBoundVar i es) = parens $ prettyTCM (var i) <+> fsep (map prettyTCM es)
  prettyTCM (PTerm t)   = "." <> parens (prettyTCM t)

instance PrettyTCM NLPType where
  prettyTCM (NLPType PWild a) = prettyTCM a
  prettyTCM (NLPType l     a) = "{" <> prettyTCM l <> "}" <> prettyTCM a

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
