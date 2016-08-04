{-# LANGUAGE CPP                  #-}
{-# LANGUAGE UndecidableInstances #-}

-- To define <>, we will probably need to add:
--import Prelude hiding ((<>))
-- but using that now gives warnings and doesn't silence -Wsemigroup
#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-semigroup    #-}
#endif
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif


module Agda.TypeChecking.Pretty where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Control.Monad

import qualified Data.Map as Map
import Data.Maybe

import Agda.Syntax.Position
import Agda.Syntax.Common
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

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (equalityUnview)
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Substitute

import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Permutation (Permutation)
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

($$), ($+$), (<>), (<+>) :: TCM Doc -> TCM Doc -> TCM Doc
d1 $$ d2  = (P.$$) <$> d1 <*> d2
d1 $+$ d2 = (P.$+$) <$> d1 <*> d2
d1 <> d2  = (P.<>) <$> d1 <*> d2
d1 <+> d2 = (P.<+>) <$> d1 <*> d2

nest :: Int -> TCM Doc -> TCM Doc
nest n d   = P.nest n <$> d

braces, dbraces, brackets, parens :: TCM Doc -> TCM Doc
braces d   = P.braces <$> d
dbraces d  = CP.dbraces <$> d
brackets d = P.brackets <$> d
parens d   = P.parens <$> d

-- | Comma-separated list in brackets.
prettyList :: [TCM Doc] -> TCM Doc
prettyList ds = brackets $ fsep $ punctuate comma ds

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

instance PrettyTCM Bool        where prettyTCM = pretty
instance PrettyTCM C.Name      where prettyTCM = pretty
instance PrettyTCM C.QName     where prettyTCM = pretty
instance PrettyTCM Comparison  where prettyTCM = pretty
instance PrettyTCM Literal     where prettyTCM = pretty
instance PrettyTCM Nat         where prettyTCM = pretty
instance PrettyTCM ProblemId   where prettyTCM = pretty
instance PrettyTCM Range       where prettyTCM = pretty
-- instance PrettyTCM Interval where prettyTCM = pretty
-- instance PrettyTCM Position where prettyTCM = pretty

instance PrettyTCM a => PrettyTCM (Closure a) where
  prettyTCM cl = enterClosure cl prettyTCM

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} PrettyTCM a => PrettyTCM [a] where
#else
instance PrettyTCM a => PrettyTCM [a] where
#endif
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
instance PrettyTCM R.Term       where prettyTCM = prettyA <=< toAbstractWithoutImplicit

instance (Show a, PrettyTCM a, Subst a a) => PrettyTCM (Substitution' a) where
  prettyTCM IdS        = text "idS"
  prettyTCM (Wk m IdS) = text "wkS" <+> pretty m
  prettyTCM EmptyS     = text "emptyS"
  prettyTCM rho = prettyTCM u <+> comma <+> prettyTCM rho1
    where
      (rho1, rho2) = splitS 1 rho
      u            = lookupS rho2 0

instance PrettyTCM Clause where
  prettyTCM cl = do
    x <- qualify_ <$> freshName_ "<unnamedclause>"
    prettyTCM (QNamed x cl)

instance PrettyTCM a => PrettyTCM (Judgement a) where
  prettyTCM (HasType a t) = prettyTCM a <+> text ":" <+> prettyTCM t
  prettyTCM (IsSort  a t) = text "Sort" <+> prettyTCM a <+> text ":" <+> prettyTCM t

instance PrettyTCM MetaId where
  prettyTCM x = do
    mn <- getMetaNameSuggestion x
    pretty $ NamedMeta mn x

instance PrettyTCM a => PrettyTCM (Blocked a) where
  prettyTCM (Blocked x a) = text "[" <+> prettyTCM a <+> text "]" <> text (show x)
  prettyTCM (NotBlocked _ x) = prettyTCM x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Named_ a) where
  prettyTCM x = prettyA =<< reify x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Arg a) where
  prettyTCM x = prettyA =<< reify x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Dom a) where
  prettyTCM x = prettyA =<< reify x

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} PrettyTCM ArgName where
#else
instance PrettyTCM ArgName where
#endif
  prettyTCM = text . show

-- instance (Reify a e, ToConcrete e c, P.Pretty c, PrettyTCM a) => PrettyTCM (Elim' a) where
instance PrettyTCM Elim where
  prettyTCM (Apply v) = text "$" <+> prettyTCM v
  prettyTCM (Proj _ f)= text "." <> prettyTCM f

instance PrettyTCM a => PrettyTCM (MaybeReduced a) where
  prettyTCM = prettyTCM . ignoreReduced

instance PrettyTCM EqualityView where
  prettyTCM v = prettyTCM $ equalityUnview v

instance PrettyTCM A.Expr where
  prettyTCM = prettyA

instance PrettyTCM Relevance where
  prettyTCM Irrelevant = text "."
  prettyTCM NonStrict  = text ".."
  prettyTCM Relevant   = empty
  prettyTCM Forced{}   = empty
  prettyTCM UnusedArg  = empty

instance PrettyTCM ProblemConstraint where
  prettyTCM (PConstr pid c) = prettyList (map prettyTCM pid) <+> prettyTCM c

instance PrettyTCM Constraint where
    prettyTCM c = case c of
        ValueCmp cmp ty s t ->
            sep [ sep [ prettyTCM s
                      , prettyTCM cmp <+> prettyTCM t
                      ]
                , nest 2 $ text ":" <+> prettyTCM ty
                ]
        ElimCmp cmps t v us vs ->
          sep [ sep [ prettyTCM us
                    , nest 2 $ text "~~" <+> prettyTCM vs
                    ]
              , text ":" <+> prettyTCM t ]
        LevelCmp cmp a b ->
            sep [ prettyTCM a
                , prettyTCM cmp <+> prettyTCM b
                ]
        TypeCmp cmp a b ->
            sep [ prettyTCM a
                , prettyTCM cmp <+> prettyTCM b
                ]
        TelCmp a b cmp tela telb ->
            sep [ prettyTCM tela
                , prettyTCM cmp <+> prettyTCM telb
                ]
        SortCmp cmp s1 s2 ->
            sep [ prettyTCM s1
                , prettyTCM cmp <+> prettyTCM s2
                ]
        Guarded c pid ->
            sep [ prettyTCM c
                , nest 2 $ brackets $ text "blocked on problem" <+> prettyTCM pid
                ]
        UnBlock m   -> do
            -- BlockedConst t <- mvInstantiation <$> lookupMeta m
            mi <- mvInstantiation <$> lookupMeta m
            case mi of
              BlockedConst t ->
                sep [ pretty m <+> text ":="
                    , nest 2 $ prettyTCM t
                    ]
              PostponedTypeCheckingProblem cl _ -> enterClosure cl $ \p ->
                sep [ pretty m <+> text ":="
                    , nest 2 $ prettyTCM p ]
              Open{}  -> __IMPOSSIBLE__
              OpenIFS{}  -> __IMPOSSIBLE__
              InstV{} -> __IMPOSSIBLE__
        FindInScope m mb Nothing -> do
            t <- getMetaType m
            sep [ text "Find in scope" <+> pretty m
                  <+> maybe (text ":") (\ b -> text "blocked on" <+> pretty b <+> text ":") mb
                , prettyTCM t
                , text " (no candidate for now)"
                ]
        FindInScope m mb (Just cands) -> do
            t <- getMetaType m
            sep [ text "Find in scope" <+> pretty m
                  <+> maybe (text ":") (\ b -> text "blocked on" <+> pretty b <+> text ":") mb
                , nest 2 $ prettyTCM t
                , sep $ flip map cands $ \cand ->
                           prettyTCM (candidateTerm cand) <+> text ": " <+> prettyTCM (candidateType cand)
                ]
        IsEmpty r t ->
            sep [ text "Is empty:", nest 2 $ prettyTCM t ]
        CheckSizeLtSat t ->
            sep [ text "Is not empty type of sizes:", nest 2 $ prettyTCM t ]

instance PrettyTCM TypeCheckingProblem where
  prettyTCM (CheckExpr e a) =
    sep [ prettyA e <+> text ":?", prettyTCM a ]
  prettyTCM (CheckArgs _ _ es t0 t1 _) =
    sep [ parens $ text "_ :" <+> prettyTCM t0
        , nest 2 $ prettyList $ map prettyA es
        , nest 2 $ text ":?" <+> prettyTCM t1 ]
  prettyTCM (CheckLambda (Arg ai (xs, mt)) e t) =
    sep [ return CP.lambda <+>
          (CP.prettyRelevance ai .
           CP.prettyHiding ai (if isNothing mt && length xs == 1 then id
                               else P.parens) <$> do
            fsep $
              map prettyTCM xs ++
              caseMaybe mt [] (\ a -> [text ":", prettyTCM a])) <+>
          return CP.arrow <+>
          prettyTCM e <+>
          text ":?"
        , prettyTCM t
        ]
  prettyTCM (UnquoteTactic v _ _) = do
    e <- reify v
    let noInfo = A.exprNoRange
    prettyTCM (A.App noInfo (A.Unquote noInfo) (defaultNamedArg e))

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
      runAbsToCon $ bindToConcrete tel (return . concat)
    )

newtype PrettyContext = PrettyContext Context

instance PrettyTCM PrettyContext where
  prettyTCM (PrettyContext ctx) = P.fsep . reverse <$> pr (map ctxEntry ctx)
    where
    pr :: [Dom (Name, Type)] -> TCM [P.Doc]
    pr []                            = return []
    pr (Dom info (x,t) : ctx) = escapeContext 1 $ do
      -- TODO guilhem: show colors
      d <- CP.prettyRelevance info . CP.prettyHiding info P.parens <$> do
             prettyTCM x <+> text ":" <+> prettyTCM t
      (d :) <$> pr ctx

instance PrettyTCM Context where
  prettyTCM = prettyTCM . PrettyContext

instance PrettyTCM CtxId where
  prettyTCM (CtxId x) = prettyTCM x

instance PrettyTCM DBPatVar where
  prettyTCM = prettyTCM . var . dbPatVarIndex

instance PrettyTCM a => PrettyTCM (Pattern' a) where
  prettyTCM (VarP x)      = prettyTCM x
  prettyTCM (DotP t)      = text ".(" <> prettyTCM t <> text ")"
  prettyTCM (ConP c i ps) = (if b then braces else parens) $ prTy $
        prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
        where
        b = maybe False (/= ConPCon) $ conPRecord i
        showRec :: TCM Doc
        showRec = sep
          [ text "record"
          , bracesAndSemicolons <$> zipWithM showField (conFields c) ps
          ]
        showField x p =
          sep [ prettyTCM (A.qnameName x) <+> text "=" , nest 2 $ prettyTCM $ namedArg p ]
        showCon = parens $ prTy $ prettyTCM c <+> fsep (map (prettyTCM . namedArg) ps)
        prTy d = d -- caseMaybe (conPType i) d $ \ t -> d  <+> text ":" <+> prettyTCM t
  prettyTCM (LitP l)      = text (show l)
  prettyTCM (ProjP _ q)   = text ("." ++ show q)

instance PrettyTCM (Elim' DisplayTerm) where
  prettyTCM (Apply v) = text "$" <+> prettyTCM (unArg v)
  prettyTCM (Proj _ f)= text "." <> prettyTCM f

raisePatVars :: Int -> NLPat -> NLPat
raisePatVars k (PVar id x bvs) = PVar id (k+x) bvs
raisePatVars k (PWild)     = PWild
raisePatVars k (PDef f es) = PDef f $ (fmap . fmap) (raisePatVars k) es
raisePatVars k (PLam i u)  = PLam i $ fmap (raisePatVars k) u
raisePatVars k (PPi a b)   = PPi ((fmap . fmap) (raisePatVars k) a) ((fmap . fmap) (raisePatVars k) b)
raisePatVars k (PPlusLevel i u) = PPlusLevel i $ raisePatVars k u
raisePatVars k (PBoundVar i es) = PBoundVar i $ (fmap . fmap) (raisePatVars k) es
raisePatVars k (PTerm t)   = PTerm t

instance PrettyTCM NLPat where
  prettyTCM (PVar id x bvs) = prettyTCM (Var x (map (Apply . fmap var) bvs))
  prettyTCM (PWild)     = text $ "_"
  prettyTCM (PDef f es) = parens $
    prettyTCM f <+> fsep (map prettyTCM es)
  prettyTCM (PLam i u)  = text ("λ " ++ absName u ++ " →") <+>
                          (addContext (absName u) $ prettyTCM (raisePatVars 1 $ absBody u))
  prettyTCM (PPi a b)   = text "Π" <+> prettyTCM (unDom a) <+>
                          (addContext (absName b) $ prettyTCM (fmap (raisePatVars 1) $ unAbs b))
  prettyTCM (PPlusLevel i u) = text (show i ++ " + ") <> prettyTCM u
  prettyTCM (PBoundVar i es) = parens $ prettyTCM (var i) <+> fsep (map prettyTCM es)
  prettyTCM (PTerm t)   = text "." <> parens (prettyTCM t)

instance PrettyTCM (Elim' NLPat) where
  prettyTCM (Apply v) = text "$" <+> prettyTCM (unArg v)
  prettyTCM (Proj _ f)= text "." <> prettyTCM f

instance PrettyTCM (Type' NLPat) where
  prettyTCM = prettyTCM . unEl

instance PrettyTCM RewriteRule where
  prettyTCM (RewriteRule q gamma f ps rhs b) = sep
    [ prettyTCM q <+> text " rule "
    , prettyTCM gamma <+> text " |- "
    , addContext gamma $ hsep
      [ prettyTCM (PDef f ps)
      , text " --> "
      , prettyTCM rhs
      , text " : "
      , prettyTCM b
      ]
    ]

instance PrettyTCM Occurrence where
  prettyTCM GuardPos  = text "-[g+]->"
  prettyTCM StrictPos = text "-[++]->"
  prettyTCM JustPos   = text "-[+]->"
  prettyTCM JustNeg   = text "-[-]->"
  prettyTCM Mixed     = text "-[*]->"
  prettyTCM Unused    = text "-[ ]->"

-- | Pairing something with a node (for printing only).
data WithNode n a = WithNode n a

instance PrettyTCM n => PrettyTCM (WithNode n Occurrence) where
  prettyTCM (WithNode n o) = prettyTCM o <+> prettyTCM n

instance (PrettyTCM n, PrettyTCM (WithNode n e)) => PrettyTCM (Graph n n e) where
  prettyTCM g = vcat $ map pr $ Map.assocs $ Graph.graph g
    where
      pr (n, es) = sep
        [ prettyTCM n
        , nest 2 $ vcat $ map (prettyTCM . uncurry WithNode) $ Map.assocs es
        ]
