
module Agda.Syntax.Abstract.Copatterns (translateCopatternClauses) where

import Prelude hiding (mapM)

import Control.Monad hiding (mapM)
import Control.Monad.Writer hiding (mapM)

import Data.Function
import Data.List

import Data.Traversable as T

import Agda.Syntax.Abstract
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Concrete (FieldAssignment'(..))
import Agda.Syntax.Info
import Agda.Syntax.Position
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (TypeError(..), typeError)
import Agda.Utils.Either
import Agda.Utils.Maybe
import Agda.Utils.Tuple

import Agda.Utils.Impossible

{- Andreas 2012-04-07, 2012-05-08

   Translating copatterns into record expressions

This is a preliminary solution until we have proper copattern type
checking and evaluation.

Example 1:

  record Stream (A : Set) : Set where
    field
      head : A
      tail : Stream A
  open Stream

  alternate : Stream Nat
  (      head alternate ) = zero
  (head (tail alternate)) = suc zero
  (tail (tail alternate)) = alternate

with pathes

  Path [head]      zero
  Path [tail,head] (suc zero)
  Path [tail,tail] alternate

is translated into

  alternate = record
    { head = zero
    ; tail = record
      { head = suc zero
      ; tail = alternate
      }
    }

Example 2:

  record State (S A : Set) : Set where
    constructor state
    field
      runState : S → A × S
  open State

  record Monad (M : Set → Set) : Set1 where
    constructor monad
    field
      return : {A : Set}   → A → M A
      _>>=_  : {A B : Set} → M A → (A → M B) → M B
  open Monad

  stateMonad : {S : Set} → Monad (State S)
  runState (return stateMonad a  ) s  = a , s
  runState (_>>=_  stateMonad m k) s₀ =
    let as₁ = runState m s₀
    in  runState (k (proj₁ as₁)) (proj₂ as₁)

with pathes

  Path [(return,[a]  ), (runstate,[s ])] (a,s)
  Path [(_>>=_, [m,k]), (runstate,[s₀])] (let...)

is translated to

  stateMonad = record
    { return = λ a → record { runState = λ s → a , s }
    ; _>>=_  = λ m k → record { runState = λ s₀ →
        let as₁ = runState m s₀
        in  runState (k (proj₁ as₁)) (proj₂ as₁)
    }

Example 3:

  swap3 : {A B C X : Set} → (X → A) × ((X → B) × C) → (X → C) × (X → (B × A))
  fst (swap3 t) x       = snd (snd t)
  fst (snd (swap3 t) y) = fst (snd t) y
  snd (snd (swap3 t) z) = fst t z

with pathes

  Path [(fst,[x])]            (snd (snd t))
  Path [(snd,[y]), (fst,[])]  (fst (snd t) y)
  Path [(snd,[z]), (snd,[])]  (fst t z)

ist translated to

  swap3 t = record
    { fst = λ x → snd (snd t)
    ; snd = λ y → record
      { fst = fst (snd t) y
      ; snd = (fst t z){z := y}
      }
    }

How to translate:
- group clauses into those with same LHSCore and same withpatterns

-}

translateCopatternClauses :: [Clause] -> ScopeM (Delayed, [Clause])
translateCopatternClauses cs = if all noCopats cs then return (NotDelayed, cs) else (Delayed,) <$> do
  pcs :: [ProjPath Clause] <- mapM clauseToPath cs
  let cps :: [(Clause, [ProjPath Expr])]
      cps = groupClauses pcs
  ces <- mapM (mapSndM pathToRecord) $
    map (mapSnd $ sortBy (compare `on` thePath)) cps
  return $ map (\ (c, e) -> c { clauseRHS = RHS e Nothing }) ces  -- TODO: preserve C.Expr
  where
    noCopats Clause{ clauseLHS = LHS _ LHSHead{} } = True
    noCopats _                                     = False

-- | A sequence of decisions @b@ leading to a head @a@.
data Path a b = Path
  { thePath    :: [a] -- ^ the list of choices
  , theContent :: b
  } deriving (Functor)  -- NB: this means @Path a@ is a functor for any @a@

mapContent :: (b -> c) -> Path a b -> Path a c
mapContent f (Path p c) = Path p (f c)

data ProjEntry = ProjEntry
  { projPE :: AmbiguousQName
  , patsPE :: [NamedArg Name] -- ^ currently we only support variable patterns
  } deriving (Eq, Ord)

type ProjPath = Path ProjEntry

instance HasRange ProjEntry where
  getRange (ProjEntry p ps) = getRange (p,ps)

-- | This is a n^2 grouping algorithm which uses only alpha-equality
groupClauses :: [ProjPath Clause] -> [(Clause, [ProjPath Expr])]
groupClauses [] = []
groupClauses (pc@(Path p c) : pcs) = (c, Path p (rhs c) : grp) : groupClauses rest
  where
    (grp, rest) = collect pcs
    -- Collect l splits l into pc's group and the remainder
    -- If the lhs of the next clause is alpha-equivalent to the current lhs
    -- then add the next clause to this group, performing the alpha-conversion
    collect (Path p' c' : pcs) | Just rho <- alpha (clauseLHS c') (clauseLHS c) =
      mapFst (Path p' (rename' rho (rhs c')) :) $ collect pcs
    -- we go through all the clauses, since they could be in random order...
    collect (pc : pcs) = mapSnd (pc :) $ collect pcs
    collect []         = ([], [])

    rhs             = rhsExpr . clauseRHS
    rhsExpr (RHS e _ ) = e  -- TODO: preserve C.Expr
    rhsExpr _       = __IMPOSSIBLE__

clauseToPath :: Clause -> ScopeM (ProjPath Clause)
clauseToPath (Clause (LHS i lhs) spats (RHS e c) wh@(WhereDecls _ []) catchall) =
  fmap (\ lhs -> Clause (LHS i lhs) spats (RHS e c) wh catchall) <$> lhsToPath [] lhs
clauseToPath (Clause lhs _ (RHS e _) (WhereDecls _ (_:_)) _) = typeError $ NotImplemented $ "copattern clauses with where declarations"
clauseToPath (Clause lhs _ _ wheredecls _) = typeError $ NotImplemented $ "copattern clauses with absurd, with or rewrite right hand side"

lhsToPath :: [ProjEntry] -> LHSCore -> ScopeM (ProjPath LHSCore)
lhsToPath acc lhs@LHSHead{}      = return $ Path acc lhs
lhsToPath acc (LHSWith h wps ps) = __IMPOSSIBLE__  -- TODO!
lhsToPath acc (LHSProj f lhs ps) = do
    let xs = fromMaybe __IMPOSSIBLE__ $ mapM (T.mapM (T.mapM fromVarP)) ps
    lhsToPath (ProjEntry f xs : acc) $ namedArg lhs
  where fromVarP :: Pattern -> Maybe Name
        fromVarP (VarP n) = Just $ unBind n
        fromVarP _        = Nothing

-- | Expects a sorted list.
pathToRecord :: [ProjPath Expr] -> ScopeM Expr
pathToRecord []          = __IMPOSSIBLE__
pathToRecord [Path [] e] = return e
pathToRecord pps =
  case pathHeads pps of
    Nothing  -> typeError $ GenericError $ "overlapping copattern clauses"
    Just pps -> do
      pes <- mapM (mapSndM pathToRecord) $ groupPathes pps
      let ei = ExprRange $ getRange $ map fst pes
      Rec ei <$> mapM abstractions pes

        where
          abstractions :: (ProjEntry, Expr) -> ScopeM RecordAssign
          abstractions (ProjEntry p xs, e) = Left . FieldAssignment (C.unqualify $ qnameToConcrete $ headAmbQ p) <$>
            foldr abstract (return e) xs

          abstract :: NamedArg Name -> ScopeM Expr -> ScopeM Expr
          abstract (Arg info (Named Nothing x)) me =
            Lam exprNoRange (DomainFree $ unnamedArg info $ BindName x) <$> me
          abstract (Arg _ (Named Just{} _)) me = typeError $ NotImplemented $
            "named arguments in projection patterns"

-- | Similar to 'groupClauses'.
groupPathes :: [(ProjEntry, ProjPath Expr)] -> [(ProjEntry, [ProjPath Expr])]
groupPathes [] = []
groupPathes ((pe@(ProjEntry p xs), path) : pps) = (pe, path : grp) : groupPathes rest
  -- Now group all following pps that have the same projection p
  -- We expect that they have alpha-equivalent xs
  where
    (grp, rest) = collect pps
    collect l@((ProjEntry p' xs', path) : pps) | p == p', Just rho <- alpha xs' xs =
      -- add the alpha-converted path to the group
      -- NOTE: because the path contains only projections and pattern vars
      -- we only alpha-convert the content (rhs Expr)
      -- When the path will contain dot patterns, we have to rename in them
      mapFst (mapContent (rename' rho) path :) $ collect pps
    collect l = ([], l) -- null or different projection: close group

pathHeads :: [Path a b] -> Maybe [(a, Path a b)]
pathHeads = mapM pathSplit

pathSplit :: Path a b -> Maybe (a, Path a b)
pathSplit (Path []     b) = Nothing
pathSplit (Path (a:as) b) = Just (a, Path as b)


-- * Alpha conversion

type NameMap = [(Name,Name)]

class Rename e where
  rename :: (Name -> Maybe Name) -> e -> e
  rename' :: NameMap -> e -> e
  rename' rho = rename (flip lookup rho)

-- | 'QName's are not renamed.
instance Rename QName where
  rename _ q = q

instance Rename Name where
  rename rho x = fromMaybe x (rho x)

instance Rename BindName where
  rename rho (BindName x) = BindName $ rename rho x

instance Rename Expr where
  rename rho e =
    case e of
      Var x                 -> Var (rename rho x)
      Def f                 -> e
      Proj{}                -> e
      Con c                 -> e
      Lit l                 -> e
      QuestionMark{}        -> e
      Underscore i          -> e
      Dot i e               -> Dot i (rename rho e)
      App i e es            -> App i (rename rho e) (rename rho es)
      WithApp i e es        -> WithApp i (rename rho e) (rename rho es)
      Lam i lb e            -> Lam i (rename rho lb) (rename rho e)
      AbsurdLam{}           -> e
      ExtendedLam i i' n cs -> ExtendedLam i i' n (rename rho cs)
      Pi i tel e            -> Pi i (rename rho tel) (rename rho e)
      Generalized s e       -> Generalized s (rename rho e)
      Fun i a e             -> Fun i (rename rho a) (rename rho e)
      Set{}                 -> e
      Prop{}                -> e
      Let i bs e            -> Let i (rename rho bs) (rename rho e)
      ETel tel              -> ETel (rename rho tel)
      Rec i fes             -> Rec i $ rename rho fes
      RecUpdate i e fes     -> RecUpdate i (rename rho e) (rename rho fes)
      ScopedExpr i e        -> ScopedExpr i (rename rho e)
      QuoteGoal i n e       -> QuoteGoal i n (rename rho e)
      QuoteContext i        -> e
      Quote i               -> e
      QuoteTerm i           -> e
      Unquote i             -> e
      Tactic i e xs ys      -> Tactic i (rename rho e) (rename rho xs) (rename rho ys)
      DontCare e            -> DontCare (rename rho e)
      PatternSyn{}          -> e
      Macro{}               -> e

instance Rename ModuleName where
  rename rho x = x

instance Rename a => Rename (FieldAssignment' a) where
  rename rho = fmap (rename rho)

instance Rename LetBinding where
  rename rho e =
      case e of
        LetBind i r n e e'    -> LetBind i r n (rename rho e) (rename rho e')
        LetPatBind i p e      -> LetPatBind i (rename rho p) (rename rho e)
        LetApply{}            -> e
        LetOpen{}             -> e
        LetDeclaredVariable x -> LetDeclaredVariable (rename rho x)

instance Rename LamBinding where
  rename rho e =
      case e of
        DomainFree{} -> e
        DomainFull tb -> DomainFull (rename rho tb)

instance Rename TypedBinding where
  rename rho (TBind r ns e) = TBind r ns (rename rho e)
  rename rho (TLet r lbs)   = TLet r (rename rho lbs)

instance Rename ProblemEq where
  rename rho (ProblemEq p v a) = ProblemEq (rename rho p) v a

instance Rename Clause where
  rename rho (Clause lhs spats rhs wheredecls catchall) =
    Clause (rename rho lhs) (rename rho spats) (rename rho rhs) (rename rho wheredecls) catchall

instance Rename RHS where
  rename rho e = case e of
      RHS e c               -> RHS (rename rho e) c
      AbsurdRHS             -> e
      WithRHS n es cs       -> WithRHS n (rename rho es) (rename rho cs)
      RewriteRHS nes spats r ds -> RewriteRHS (rename rho nes) (rename rho spats) (rename rho r) (rename rho ds)

instance Rename WhereDeclarations where
  rename rho (WhereDecls m ds) = WhereDecls m (rename rho ds)

instance Rename LHS where
  rename rho (LHS i core) = LHS i (rename rho core)

instance Rename LHSCore where
  rename rho = fmap (rename rho) -- only rename in dot patterns

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

instance (Rename a, Rename b) => Rename (Either a b) where
  rename rho = mapEither (rename rho) (rename rho)

instance (Rename a, Rename b) => Rename (a, b) where
  rename rho (a,b) = (rename rho a, rename rho b)


-- | Alpha-Equivalence of patterns, ignoring dot patterns
class Alpha t where
  alpha :: t -> t -> Maybe NameMap
  alpha t t' = fmap snd $ runWriterT $ alpha' t t'

  alpha' :: t -> t -> WriterT NameMap Maybe ()
  alpha' t t' = WriterT $ fmap ((),) $ alpha t t'

instance Alpha Name where
  alpha' x x' = tell1 (x, x')

instance Alpha (Pattern' e) where
  alpha' p p' =
    case (p,p') of
      ((VarP x)             , (VarP x')             ) -> tell1 (unBind x, unBind x')
      ((ConP _ x ps)        , (ConP _ x' ps')       ) -> guard (x == x') >> alpha' ps ps'
      ((DefP _ x ps)        , (DefP _ x' ps')       ) -> guard (x == x') >> alpha' ps ps'
      ((WildP _)            , (WildP _)             ) -> return ()
      ((AsP _ x p)          , (AsP _ x' p')         ) -> tell1 (unBind x, unBind x') >> alpha' p p'
      ((DotP _ _)           , (DotP _ _)            ) -> return ()
      (AbsurdP{}            , AbsurdP{}             ) -> return ()
      ((LitP l)             , (LitP l')             ) -> guard (l == l')
      ((PatternSynP _ x ps) , (PatternSynP _ x' ps')) -> guard (x == x') >> alpha' ps ps'
      (_                    , _                     ) -> fail "not alpha equivalent"

tell1 :: (MonadWriter [a] m) => a -> m ()
tell1 a = tell [a]

instance Alpha (LHSCore' e) where
  alpha' (LHSHead f ps) (LHSHead f' ps') = guard (f == f') >> alpha' ps ps'
  alpha' (LHSProj d lhs ps) (LHSProj d' lhs' ps') =
     guard (d == d') >> alpha' lhs lhs' >> alpha' ps ps'
  alpha' (LHSWith h wps ps) (LHSWith h' wps' ps') =
     alpha' h h' >> alpha' wps wps' >> alpha' ps ps'
  alpha' _ _ = fail "not alpha equivalent"

instance Alpha LHS where
  alpha' (LHS _ core) (LHS _ core') = alpha' core core'

instance Alpha a => Alpha (Arg a) where
  alpha' a a' = alpha' (unArg a) (unArg a')

instance (Eq n, Alpha a) => Alpha (Named n a) where
  alpha' a a' = guard (nameOf a == nameOf a') >> alpha' (namedThing a) (namedThing a')

instance Alpha a => Alpha [a] where
  alpha' l l' = guard (length l == length l') >> zipWithM_ alpha' l l'
