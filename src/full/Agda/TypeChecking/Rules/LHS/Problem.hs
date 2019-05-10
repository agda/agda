
module Agda.TypeChecking.Rules.LHS.Problem
       ( FlexibleVars , FlexibleVarKind(..) , FlexibleVar(..) , allFlexVars
       , FlexChoice(..) , ChooseFlex(..)
       , ProblemEq(..) , Problem(..) , problemEqs
       , problemRestPats, problemCont, problemInPats
       , AsBinding(..) , DotPattern(..) , AbsurdPattern(..)
       , LHSState(..) , lhsTel , lhsOutPat , lhsProblem , lhsTarget
       ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Data.Foldable ( Foldable )
import Data.Maybe ( fromMaybe )
import Data.Monoid ( Monoid, mempty, mappend, mconcat )
import Data.Semigroup ( Semigroup, (<>) )
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Abstract (ProblemEq(..))
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad (TCM)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import qualified Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.Pretty

import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size
import qualified Agda.Utils.Pretty as PP

type FlexibleVars   = [FlexibleVar Nat]

-- | When we encounter a flexible variable in the unifier, where did it come from?
--   The alternatives are ordered such that we will assign the higher one first,
--   i.e., first we try to assign a @DotFlex@, then...
data FlexibleVarKind
  = RecordFlex [FlexibleVarKind]
      -- ^ From a record pattern ('ConP').
      --   Saves the 'FlexibleVarKind' of its subpatterns.
  | ImplicitFlex -- ^ From a hidden formal argument or underscore ('WildP').
  | DotFlex      -- ^ From a dot pattern ('DotP').
  | OtherFlex    -- ^ From a non-record constructor or literal ('ConP' or 'LitP').
  deriving (Eq, Show)

-- | Flexible variables are equipped with information where they come from,
--   in order to make a choice which one to assign when two flexibles are unified.
data FlexibleVar a = FlexibleVar
  { flexHiding :: Hiding
  , flexOrigin :: Origin
  , flexKind   :: FlexibleVarKind
  , flexPos    :: Maybe Int
  , flexVar    :: a
  } deriving (Eq, Show, Functor, Foldable, Traversable)

instance LensHiding (FlexibleVar a) where
  getHiding     = flexHiding
  mapHiding f x = x { flexHiding = f (flexHiding x) }

instance LensOrigin (FlexibleVar a) where
  getOrigin     = flexOrigin
  mapOrigin f x = x { flexOrigin = f (flexOrigin x) }

-- UNUSED
-- defaultFlexibleVar :: a -> FlexibleVar a
-- defaultFlexibleVar a = FlexibleVar Hidden Inserted ImplicitFlex Nothing a

-- UNUSED
-- flexibleVarFromHiding :: Hiding -> a -> FlexibleVar a
-- flexibleVarFromHiding h a = FlexibleVar h ImplicitFlex Nothing a

allFlexVars :: Telescope -> FlexibleVars
allFlexVars tel = zipWith makeFlex (downFrom $ size tel) $ telToList tel
  where
    makeFlex i d = FlexibleVar (getHiding d) (getOrigin d) ImplicitFlex (Just i) i

data FlexChoice = ChooseLeft | ChooseRight | ChooseEither | ExpandBoth
  deriving (Eq, Show)

instance Semigroup FlexChoice where
  ExpandBoth   <> _            = ExpandBoth
  _            <> ExpandBoth   = ExpandBoth
  ChooseEither <> y            = y
  x            <> ChooseEither = x
  ChooseLeft   <> ChooseRight  = ExpandBoth -- If there's dot patterns on both sides,
  ChooseRight  <> ChooseLeft   = ExpandBoth -- we need to eta-expand
  ChooseLeft   <> ChooseLeft   = ChooseLeft
  ChooseRight  <> ChooseRight  = ChooseRight

instance Monoid FlexChoice where
  mempty  = ChooseEither
  mappend = (<>)

class ChooseFlex a where
  chooseFlex :: a -> a -> FlexChoice

instance ChooseFlex FlexibleVarKind where
  chooseFlex DotFlex         DotFlex         = ChooseEither
  chooseFlex DotFlex         _               = ChooseLeft
  chooseFlex _               DotFlex         = ChooseRight
  chooseFlex (RecordFlex xs) (RecordFlex ys) = chooseFlex xs ys
  chooseFlex (RecordFlex xs) y               = chooseFlex xs (repeat y)
  chooseFlex x               (RecordFlex ys) = chooseFlex (repeat x) ys
  chooseFlex ImplicitFlex    ImplicitFlex    = ChooseEither
  chooseFlex ImplicitFlex    _               = ChooseLeft
  chooseFlex _               ImplicitFlex    = ChooseRight
  chooseFlex OtherFlex       OtherFlex       = ChooseEither

instance ChooseFlex a => ChooseFlex [a] where
  chooseFlex xs ys = mconcat $ zipWith chooseFlex xs ys

instance ChooseFlex a => ChooseFlex (Maybe a) where
  chooseFlex Nothing Nothing = ChooseEither
  chooseFlex Nothing (Just y) = ChooseLeft
  chooseFlex (Just x) Nothing = ChooseRight
  chooseFlex (Just x) (Just y) = chooseFlex x y

instance ChooseFlex Hiding where
  chooseFlex Hidden     Hidden     = ChooseEither
  chooseFlex Hidden     _          = ChooseLeft
  chooseFlex _          Hidden     = ChooseRight
  chooseFlex Instance{} Instance{} = ChooseEither
  chooseFlex Instance{} _          = ChooseLeft
  chooseFlex _          Instance{} = ChooseRight
  chooseFlex _          _          = ChooseEither

instance ChooseFlex Origin where
  chooseFlex Inserted  Inserted  = ChooseEither
  chooseFlex Inserted  _         = ChooseLeft
  chooseFlex _         Inserted  = ChooseRight
  chooseFlex Reflected Reflected = ChooseEither
  chooseFlex Reflected _         = ChooseLeft
  chooseFlex _         Reflected = ChooseRight
  chooseFlex _         _         = ChooseEither

instance ChooseFlex Int where
  chooseFlex x y = case compare x y of
    LT -> ChooseLeft
    EQ -> ChooseEither
    GT -> ChooseRight

instance (ChooseFlex a) => ChooseFlex (FlexibleVar a) where
  chooseFlex (FlexibleVar h1 o1 f1 p1 i1) (FlexibleVar h2 o2 f2 p2 i2) =
    firstChoice [ chooseFlex f1 f2, chooseFlex o1 o2, chooseFlex h1 h2
                , chooseFlex p1 p2, chooseFlex i1 i2]
      where
        firstChoice :: [FlexChoice] -> FlexChoice
        firstChoice []                  = ChooseEither
        firstChoice (ChooseEither : xs) = firstChoice xs
        firstChoice (x            : _ ) = x

-- | The user patterns we still have to split on.
data Problem a = Problem
  { _problemEqs      :: [ProblemEq]
    -- ^ User patterns.
  , _problemRestPats :: [NamedArg A.Pattern]
    -- ^ List of user patterns which could not yet be typed.
    --   Example:
    --   @
    --      f : (b : Bool) -> if b then Nat else Nat -> Nat
    --      f true          = zero
    --      f false zero    = zero
    --      f false (suc n) = n
    --   @
    --   In this sitation, for clause 2, we construct an initial problem
    --   @
    --      problemEqs      = [false = b]
    --      problemRestPats = [zero]
    --   @
    --   As we instantiate @b@ to @false@, the 'targetType' reduces to
    --   @Nat -> Nat@ and we can move pattern @zero@ over to @problemEqs@.
  , _problemCont     :: LHSState a -> TCM a
  }
  deriving Show

problemEqs :: Lens' [ProblemEq] (Problem a)
problemEqs f p = f (_problemEqs p) <&> \x -> p {_problemEqs = x}

problemRestPats :: Lens' [NamedArg A.Pattern] (Problem a)
problemRestPats f p = f (_problemRestPats p) <&> \x -> p {_problemRestPats = x}

problemCont :: Lens' (LHSState a -> TCM a) (Problem a)
problemCont f p = f (_problemCont p) <&> \x -> p {_problemCont = x}

problemInPats :: Problem a -> [A.Pattern]
problemInPats = map problemInPat . (^. problemEqs)

data AsBinding = AsB Name Term Type
data DotPattern = Dot A.Expr Term (Dom Type)
data AbsurdPattern = Absurd Range Type

-- | State worked on during the main loop of checking a lhs.
--   [Ulf Norell's PhD, page. 35]
data LHSState a = LHSState
  { _lhsTel     :: Telescope
    -- ^ The types of the pattern variables.
  , _lhsOutPat  :: [NamedArg DeBruijnPattern]
    -- ^ Patterns after splitting.
    --   The de Bruijn indices refer to positions in the list of abstract syntax
    --   patterns in the problem, counted from the back (right-to-left).
  , _lhsProblem :: Problem a
    -- ^ User patterns of supposed type @delta@.
  , _lhsTarget  :: Arg Type
    -- ^ Type eliminated by 'problemRestPats' in the problem.
    --   Can be 'Irrelevant' to indicate that we came by
    --   an irrelevant projection and, hence, the rhs must
    --   be type-checked in irrelevant mode.
  , _lhsPartialSplit :: ![Maybe Int] -- ^ have we splitted with a PartialFocus?
  }

lhsTel :: Lens' Telescope (LHSState a)
lhsTel f p = f (_lhsTel p) <&> \x -> p {_lhsTel = x}

lhsOutPat :: Lens' [NamedArg DeBruijnPattern] (LHSState a)
lhsOutPat f p = f (_lhsOutPat p) <&> \x -> p {_lhsOutPat = x}

lhsProblem :: Lens' (Problem a) (LHSState a)
lhsProblem f p = f (_lhsProblem p) <&> \x -> p {_lhsProblem = x}

lhsTarget :: Lens' (Arg Type) (LHSState a)
lhsTarget f p = f (_lhsTarget p) <&> \x -> p {_lhsTarget = x}

lhsPartialSplit :: Lens' [Maybe Int] (LHSState a)
lhsPartialSplit f p = f (_lhsPartialSplit p) <&> \x -> p {_lhsPartialSplit = x}

instance Subst Term (Problem a) where
  applySubst rho (Problem eqs rps cont) = Problem (applySubst rho eqs) rps cont

instance Subst Term AsBinding where
  applySubst rho (AsB x v a) = uncurry (AsB x) $ applySubst rho (v, a)

instance Subst Term DotPattern where
  applySubst rho (Dot e v a) = uncurry (Dot e) $ applySubst rho (v, a)

instance Subst Term AbsurdPattern where
  applySubst rho (Absurd r a) = Absurd r $ applySubst rho a

instance PrettyTCM ProblemEq where
  prettyTCM (ProblemEq p v a) = sep
    [ prettyA p <+> "="
    , nest 2 $ prettyTCM v <+> ":"
    , nest 2 $ prettyTCM a
    ]

instance PrettyTCM AsBinding where
  prettyTCM (AsB x v a) =
    sep [ prettyTCM x <> "@" <> parens (prettyTCM v)
        , nest 2 $ ":" <+> prettyTCM a
        ]

instance PrettyTCM DotPattern where
  prettyTCM (Dot e v a) = sep
    [ prettyA e <+> "="
    , nest 2 $ prettyTCM v <+> ":"
    , nest 2 $ prettyTCM a
    ]

instance PrettyTCM AbsurdPattern where
  prettyTCM (Absurd r a) = "() :" <+> prettyTCM a

instance PP.Pretty AsBinding where
  pretty (AsB x v a) =
    PP.pretty x PP.<+> "=" PP.<+>
      PP.hang (PP.pretty v PP.<+> ":") 2 (PP.pretty a)

instance InstantiateFull AsBinding where
  instantiateFull' (AsB x v a) = AsB x <$> instantiateFull' v <*> instantiateFull' a
