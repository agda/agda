-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS.Problem where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import Data.Foldable ( Foldable )
import Data.Maybe ( fromMaybe )
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, mconcat)
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import qualified Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.Pretty hiding ((<>))

import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Size
import qualified Agda.Utils.Pretty as PP

type Substitution   = [Maybe Term]
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

-- ^ Used to determine the origin of dot patterns in internal syntax.
--   Note that this is NOT the same as the flexOrigin.
flexVarToOrigin :: FlexibleVar a -> Origin
flexVarToOrigin f = case flexKind f of
  DotFlex      -> UserWritten
  RecordFlex _ -> Inserted
  ImplicitFlex -> Inserted
  OtherFlex    -> Inserted

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

data Problem = Problem
  { problemInPat    :: [NamedArg A.Pattern]
    -- ^ User patterns.
  , problemRestPats :: [NamedArg A.Pattern]
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
    --      problemInPat = [false]
    --      problemTel   = (b : Bool)
    --      problemRest.restPats = [zero]
    --      problemRest.restType = if b then Nat else Nat -> Nat
    --   @
    --   As we instantiate @b@ to @false@, the 'restType' reduces to
    --   @Nat -> Nat@ and we can move pattern @zero@ over to @problemInPat@.
  , problemDPI                :: [DotPatternInst]
  , problemShouldBeEmptyTypes :: [(Range,Type)]
  }
  deriving Show

data Focus
  = ConFocus
    { focusCon      :: QName
    , focusPatOrigin:: ConOrigin -- ^ Do we come from an implicit or record pattern?
    , focusConArgs  :: [NamedArg A.Pattern]
    , focusRange    :: Range
    , focusDatatype :: QName
    , focusParams   :: [Arg Term]
    , focusIndices  :: [Arg Term]
    }
  | LitFocus Literal
  | AbsurdFocus PatInfo

-- | Result of 'splitProblem':  Determines position for the next split.
data SplitProblem

  = -- | Split on constructor pattern.
    SplitArg
      { splitLPats   :: [NamedArg A.Pattern]
        -- ^ The typed user patterns left of the split position.
        --   Invariant: @'problemRest' == empty@.
      , splitFocus   :: Arg Focus
        -- ^ How to split the variable at the split position.
      , splitRPats   :: [NamedArg A.Pattern]
        -- ^ The typed user patterns right of the split position.
      }

  | -- | Split on projection pattern.
    SplitRest
      { splitProjection :: Arg QName
        -- ^ The projection could be belonging to an irrelevant record field.
      , splitProjOrigin :: ProjOrigin
      , splitProjType   :: Type
      }

-- | Put a pattern on the very left of a @SplitProblem@.
consSplitProblem
  :: NamedArg A.Pattern   -- ^ @p@ A pattern.
  -> SplitProblem         -- ^ The split problem, containing 'splitLPats' @ps;xs:ts@.
  -> SplitProblem         -- ^ The result, now containing 'splitLPats' @(p,ps);(x,xs):(t,ts)@.
consSplitProblem p s@SplitRest{}                 = s
consSplitProblem p s@SplitArg{ splitLPats = ps } = s{ splitLPats = (p:ps) }

-- | Instantiations of a dot pattern with a term.
--   `Maybe e` if the user wrote a dot pattern .e
--   `Nothing` if this is an instantiation of an implicit argument or a name.
data DotPatternInst = DPI
  { dotPatternName     :: Maybe A.Name
  , dotPatternUserExpr :: Maybe A.Expr
  , dotPatternInst     :: Term
  , dotPatternType     :: Dom Type
  } deriving (Show)
data AsBinding      = AsB Name Term Type

-- | State worked on during the main loop of checking a lhs.
--   [Ulf Norell's PhD, page. 35]
data LHSState = LHSState
  { lhsTel     :: Telescope
    -- ^ Type of pattern variables.
  , lhsOutPat  :: [NamedArg DeBruijnPattern]
    -- ^ Patterns after splitting.
    --   The de Bruijn indices refer to positions in the list of abstract
    --   patterns in the problem, counted from the back.
  , lhsProblem :: Problem
    -- ^ User patterns of supposed type @delta@.
  , lhsTarget  :: Arg Type
    -- ^ Type eliminated by 'problemRestPats' in the problem.
    --   Can be 'Irrelevant' to indicate that we came by
    --   an irrelevant projection and, hence, the rhs must
    --   be type-checked in irrelevant mode.
  }

instance Subst Term DotPatternInst where
  applySubst rho (DPI x e v a) = uncurry (DPI x e) $ applySubst rho (v,a)

instance Subst Term AsBinding where
  applySubst rho (AsB x v a) = uncurry (AsB x) $ applySubst rho (v, a)

instance PrettyTCM DotPatternInst where
  prettyTCM (DPI mx me v a) = sep
    [ x <+> text "=" <+> text "." P.<> prettyA e
    , nest 2 $ prettyTCM v <+> text ":"
    , nest 2 $ prettyTCM a
    ]
    where x = maybe (text "_") prettyA mx
          e = fromMaybe underscore me

instance PrettyTCM AsBinding where
  prettyTCM (AsB x v a) =
    sep [ prettyTCM x P.<> text "@" P.<> parens (prettyTCM v)
        , nest 2 $ text ":" <+> prettyTCM a
        ]

instance PP.Pretty AsBinding where
  pretty (AsB x v a) =
    PP.pretty x PP.<+> PP.text "=" PP.<+>
      PP.hang (PP.pretty v PP.<+> PP.text ":") 2 (PP.pretty a)

instance InstantiateFull AsBinding where
  instantiateFull' (AsB x v a) = AsB x <$> instantiateFull' v <*> instantiateFull' a

instance Null Problem where
  null p = null (problemInPat p)
           && null (problemRestPats p)
           && null (problemDPI p)
           && null (problemShouldBeEmptyTypes p)
  empty  = Problem empty empty empty empty
