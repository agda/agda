{-# LANGUAGE CPP, TupleSections, DeriveFunctor, StandaloneDeriving, ScopedTypeVariables, TypeSynonymInstances, FlexibleContexts  #-}
-- {-# LANGUAGE DeriveFunctor, DeriveTraversable  #-}
module Agda.Syntax.Abstract.Copatterns (translateCopatternClauses) where

import Control.Applicative
import Control.Monad
import Control.Monad.Writer

import Data.Function
import Data.List

-- import Data.Traversable

import Agda.Syntax.Abstract
import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Info
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (TypeError(..), Call(..), typeError,
                                     TCErr(..), TCErr'(..))
import Agda.Utils.List
import Agda.Utils.Tuple

#include "../../undefined.h"
import Agda.Utils.Impossible

{- Andreas 2012-04-07

   Translating copatterns into record expressions

This is a preliminary solution until we have proper copattern type
checking and evaluation.

Example:

  record Stream (A : Set) : Set where
    field
      head : A
      tail : Stream A
  open Stream

  alternate : Stream Nat
  (      head alternate ) = zero
  (head (tail alternate)) = suc zero
  (tail (tail alternate)) = alternate

is translated into

  alternate = record
    { head = zero
    ; tail = record
      { head = suc zero
      ; tail = alternate
      }
    }

How to translate:
- group clauses into those with same LHSCore and same withpatterns

-}

translateCopatternClauses :: [Clause] -> ScopeM [Clause]
translateCopatternClauses cs = if all noCopats cs then return cs else do
  pcs :: [ProjPath Clause] <- mapM clauseToPath cs
  let cps :: [(Clause, [ProjPath Expr])]
      cps = groupClauses pcs
{-
      cps = map ((theContent . head) /\ map (fmap (rhsExpr . clauseRHS))) $
              groupBy ((==) `on` clauseLHS . theContent) pcs
-}
  ces <- mapM (mapSndM pathToRecord) $
    map (id -*- sortBy (compare `on` thePath)) cps
  return $ map (\ (c, e) -> c { clauseRHS = RHS e }) ces
  where
    noCopats Clause{ clauseLHS = LHS _ LHSHead{} _ } = True
    noCopats _                                       = False
    rhsExpr (RHS e) = e
    rhsExpr _       = __IMPOSSIBLE__

-- | A sequence of decisions @b@ leading to a head @a@.
data Path a b = Path
  { thePath    :: [a] -- ^ the list of choices
  , theContent :: b
  } deriving (Functor)  -- NB: this means @Path a@ is a functor for any @a@
type ProjPath = Path QName

groupClauses :: [ProjPath Clause] -> [(Clause, [ProjPath Expr])]
groupClauses [] = []
groupClauses (pc@(Path p c) : pcs) = (c, Path p (rhs c) : grp) : groupClauses rest
  where
    (grp, rest) = collect pcs
    collect l = case l of
      [] -> ([], [])
      (Path p' c' : pcs) -> case alpha (clauseLHS c') (clauseLHS c) of
         Nothing  -> ([], l)
         Just rho -> let (grp, rest) = collect pcs
                     in  (Path p' (rename (flip lookup rho) (rhs c')) : grp, rest)
    rhs             = rhsExpr . clauseRHS
    rhsExpr (RHS e) = e
    rhsExpr _       = __IMPOSSIBLE__

clauseToPath :: Clause -> ScopeM (ProjPath Clause)
clauseToPath (Clause (LHS i lhs wps) (RHS e) []) =
  fmap (\ lhs -> Clause (LHS i lhs wps) (RHS e) []) <$> lhsToPath lhs
clauseToPath (Clause lhs (RHS e) (_:_)) = typeError $ NotImplemented $ "copattern clauses with where declarations"
clauseToPath (Clause lhs _ wheredecls) = typeError $ NotImplemented $ "copattern clauses with absurd, with or rewrite right hand side"

-- TODO: use accumulator
lhsToPath :: LHSCore -> ScopeM (ProjPath LHSCore)
lhsToPath lhs@LHSHead{} = return $ Path [] lhs
lhsToPath (LHSProj f [] lhs []) = do
  Path p lhs <- lhsToPath $ namedThing $ unArg lhs
  return $ Path (p ++ [f]) lhs
lhsToPath (LHSProj f _ lhs _) = typeError $ NotImplemented $ "copatterns which are not simple sequences of projections"

-- | Expects a sorted list.
pathToRecord :: [ProjPath Expr] -> ScopeM Expr
pathToRecord []          = __IMPOSSIBLE__
pathToRecord [Path [] e] = return e
pathToRecord pps =
  case pathHeads pps of
    Nothing  -> typeError $ GenericError $ "overlapping copattern clauses"
    Just pps -> do
      let l :: [(QName, [ProjPath Expr])]
          l =  map ((fst . head) /\ map snd) $ groupOn fst pps
      pes <- mapM (mapSndM pathToRecord) l
      let ei = ExprRange $ getRange $ map fst pes
      return $ Rec ei $ map ((C.unqualify . qnameToConcrete) -*- id) pes

pathSplit :: Path a b -> Maybe (a, Path a b)
pathSplit (Path []     b) = Nothing
pathSplit (Path (a:as) b) = Just (a, Path as b)

pathHeads :: [Path a b] -> Maybe [(a, Path a b)]
pathHeads = mapM pathSplit


-- * Alpha conversion

type NameMap = [(Name,Name)]

class Rename e where
  rename :: (Name -> Maybe Name) -> e -> e

instance Rename Expr where
  rename rho e =
    case e of
      Var x                 -> Var $ maybe x id (rho x)
      Def f                 -> e
      Con c                 -> e
      Lit l                 -> e
      QuestionMark i        -> e
      Underscore i          -> e
      App i e es            -> App i (rename rho e) (rename rho es)
      WithApp i e es        -> WithApp i (rename rho e) (rename rho es)
      Lam i lb e            -> Lam i (rename rho lb) (rename rho e)
      AbsurdLam{}           -> e
      ExtendedLam i i' n cs -> ExtendedLam i i' n (rename rho cs)
      Pi i tel e            -> Pi i (rename rho tel) (rename rho e)
      Fun i a e             -> Fun i (rename rho a) (rename rho e)
      Set{}                 -> e
      Prop{}                -> e
      Let i bs e            -> Let i (rename rho bs) (rename rho e)
      ETel tel              -> ETel (rename rho tel)
      Rec i fes             -> Rec i $ map (id -*- rename rho) fes
      RecUpdate i e fes     -> RecUpdate i (rename rho e) $ map (id -*- rename rho) fes
      ScopedExpr i e        -> ScopedExpr i (rename rho e)
      QuoteGoal i n e       -> QuoteGoal i n (rename rho e)
      Quote i               -> e
      QuoteTerm i           -> e
      Unquote i             -> e
      DontCare e            -> DontCare (rename rho e)
      PatternSyn n          -> e

instance Rename LetBinding where
  rename rho e =
      case e of
        LetBind i r n e e' -> LetBind i r n (rename rho e) (rename rho e')
        LetApply{}         -> e
        LetOpen{}          -> e

instance Rename LamBinding where
  rename rho e =
      case e of
        DomainFree{} -> e
        DomainFull tb -> DomainFull (rename rho tb)

instance Rename TypedBindings where
  rename rho (TypedBindings r tb) = TypedBindings r (rename rho tb)

instance Rename TypedBinding where
  rename rho (TBind r ns e) = TBind r ns (rename rho e)
  rename rho (TNoBind    e) = TNoBind (rename rho e)

instance Rename Clause where
  rename rho (Clause lhs rhs wheredecls) =
    Clause (rename rho lhs) (rename rho rhs) (rename rho wheredecls)

instance Rename RHS where
  rename rho e = case e of
      RHS e                 -> RHS (rename rho e)
      AbsurdRHS             -> e
      WithRHS n es cs       -> WithRHS n (rename rho es) (rename rho cs)
      RewriteRHS ns es r ds -> RewriteRHS ns (rename rho es) (rename rho r) (rename rho ds)

instance Rename LHS where
  rename rho (LHS i core ps) = LHS i (rename rho core) (rename rho ps)

instance Rename LHSCore where
  rename rho = fmap (rename rho) -- only rename in dot patterns
{-
  rename rho = ren where
    ren e = case e of
      LHSHead f ps           -> LHSHead f (ren ps)
      LHSProj d ps1 core ps2 -> LHSProj d (ren ps1) (ren core) (ren ps2)
-}

instance Rename Pattern where
  rename rho = fmap (rename rho) -- only rename in dot patterns

instance Rename Declaration where
  rename rho d = __IMPOSSIBLE__

instance Rename a => Rename (Arg a) where
  rename rho = fmap (rename rho)

instance Rename a => Rename (Named n a) where
  rename rho = fmap (rename rho)

instance Rename a => Rename [a] where
  rename rho = map (rename rho)




-- | Alpha-Equivalence of patterns, ignoring dot patterns
class Alpha t where
  alpha :: t -> t -> Maybe NameMap
  alpha t t' = fmap snd $ runWriterT $ alpha' t t'

  alpha' :: t -> t -> WriterT NameMap Maybe ()
  alpha' t t' = WriterT $ fmap ((),) $ alpha t t'

instance Alpha (Pattern' e) where
  alpha' p p' =
    case (p,p') of
      ((VarP x)             , (VarP x')             ) -> tell1 (x, x')
      ((ConP _ x ps)        , (ConP _ x' ps')       ) -> guard (x == x') >> alpha' ps ps'
      ((DefP _ x ps)        , (DefP _ x' ps')       ) -> guard (x == x') >> alpha' ps ps'
      ((WildP _)            , (WildP _)             ) -> return ()
      ((AsP _ x p)          , (AsP _ x' p')         ) -> tell1 (x, x') >> alpha' p p'
      ((DotP _ _)           , (DotP _ _)            ) -> return ()
      (AbsurdP{}            , AbsurdP{}             ) -> return ()
      ((LitP l)             , (LitP l')             ) -> guard (l == l')
      (ImplicitP{}          , ImplicitP{}           ) -> return ()
      ((PatternSynP _ x ps) , (PatternSynP _ x' ps')) -> guard (x == x') >> alpha' ps ps'
      (_                    , _                     ) -> fail "not alpha equivalent"

tell1 :: (MonadWriter [a] m) => a -> m ()
tell1 a = tell [a]

deriving instance Eq AmbiguousQName

instance Alpha (LHSCore' e) where
  alpha' (LHSHead f ps) (LHSHead f' ps') = guard (f == f') >> alpha' ps ps'
  alpha' (LHSProj d ps1 lhs ps2) (LHSProj d' ps1' lhs' ps2') =
     guard (d == d') >> alpha' ps1 ps1' >> alpha' lhs lhs' >> alpha' ps2 ps2'
  alpha' _ _ = fail "not alpha equivalent"

instance Alpha LHS where
  alpha' (LHS _ core wps) (LHS _ core' wps') = alpha' core core' >> alpha' wps wps'

instance Alpha a => Alpha (Arg a) where
  alpha' a a' = alpha' (unArg a) (unArg a')

instance (Eq n, Alpha a) => Alpha (Named n a) where
  alpha' a a' = guard (nameOf a == nameOf a') >> alpha' (namedThing a) (namedThing a')

instance Alpha a => Alpha [a] where
  alpha' l l' = guard (length l == length l') >> zipWithM_ alpha' l l'

-- | Literal equality of patterns, ignoring dot patterns
instance Eq (Pattern' e) where
  p == p' =
    case (p,p') of
      ((VarP x)             , (VarP x')             ) -> x === x'
      ((ConP _ x ps)        , (ConP _ x' ps')       ) -> x == x' && ps == ps'
      ((DefP _ x ps)        , (DefP _ x' ps')       ) -> x == x' && ps == ps'
      ((WildP _)            , (WildP _)             ) -> True
      ((AsP _ x p)          , (AsP _ x' p')         ) -> x === x' && p == p'
      ((DotP _ _)           , (DotP _ _)            ) -> True
      (AbsurdP{}            , AbsurdP{}             ) -> True
      ((LitP l)             , (LitP l')             ) -> l == l'
      (ImplicitP{}          , ImplicitP{}           ) -> True
      ((PatternSynP _ x ps) , (PatternSynP _ x' ps')) -> x == x' && ps == ps'
      (_                    , _                     ) -> False
    where (A.Name _ (C.Name _ x) _ _) === (A.Name _ (C.Name _ x') _ _) = True
          (A.Name _ C.NoName{}   _ _) === (A.Name _ C.NoName{}    _ _) = True
          _                           === _                            = False

deriving instance Eq (LHSCore' e)

instance Eq LHS where
  (LHS _ core wps) == (LHS _ core' wps') = core == core' && wps == wps'

