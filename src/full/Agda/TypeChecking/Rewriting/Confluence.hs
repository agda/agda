{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}

-- | Checking confluence of rewrite rules.
--
-- Given a rewrite rule @f ps ↦ v@, we construct critical pairs
-- involving this as the main rule by searching for:
--
-- 1. *Different* rules @f ps' ↦ v'@ where @ps@ and @ps'@ can be
--    unified@.
--
-- 2. Subpatterns @g qs@ of @ps@ and rewrite rules @g qs' ↦ w@ where
--    @qs@ and @qs'@ can be unified.
--
-- Each of these leads to a *critical pair* @v₁ <-- u --> v₂@, which
-- should satisfy @v₁ = v₂@.

module Agda.TypeChecking.Rewriting.Confluence ( checkConfluenceOfRule ) where

import Control.Monad
import Control.Monad.Reader

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Functor ( ($>) )
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Warning
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting.Clause
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.Utils.Either
import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.Size


-- ^ Check confluence of the given rewrite rule wrt all other rewrite
--   rules (including itself).
checkConfluenceOfRule :: RewriteRule -> TCM ()
checkConfluenceOfRule rew = inTopContext $ do

  reportSDoc "rewriting.confluence" 10 $
    "Checking confluence of rule" <+> prettyTCM (rewName rew)

  let f  = rewHead rew
      es = rewPats rew
  def <- getConstInfo f

  -- Step 1: check other rewrite rules that overlap at top position
  forMM_ (getClausesAndRewriteRulesFor f) $ \ rew' ->
    checkConfluenceTop rew rew'

  -- Step 2: check other rewrite rules that overlap with a subpattern
  -- of this rewrite rule
  forM_ (allPatternHoles es) $ \ hole -> case ohpContents hole of
    PDef g es' -> forMM_ (getClausesAndRewriteRulesFor g) $ \ rew' ->
      checkConfluenceSub rew rew' hole
    _ -> return ()

  -- Step 3: check other rewrite rules that have a subpattern which
  -- overlaps with this rewrite rule
  forM_ (defMatchable def) $ \ g ->
    forMM_ (getRewriteRulesFor g) $ \ rew' ->
      forM_ (allPatternHoles $ rewPats rew') $ \ hole ->
        case ohpContents hole of
          PDef f' es' | f == f' -> checkConfluenceSub rew' rew hole
          _ -> return ()

  where

    -- Check confluence of two rewrite rules that have the same head symbol,
    -- e.g. @f ps --> a@ and @f ps' --> b@.
    checkConfluenceTop :: RewriteRule -> RewriteRule -> TCM ()
    checkConfluenceTop rew1 rew2 =
      traceCall (CheckConfluence (rewName rew1) (rewName rew2)) $
      localTCStateSavingWarnings $ do

        sub1 <- makeMetaSubst $ rewContext rew1
        sub2 <- makeMetaSubst $ rewContext rew2

        es1 <- applySubst sub1 <$> nlPatToTerm (rewPats rew1)
        es2 <- applySubst sub2 <$> nlPatToTerm (rewPats rew2)

        let f    = rewHead rew1 -- == rewHead rew2
            lhs1 = Def f es1
            lhs2 = Def f es2

        reportSDoc "rewriting.confluence" 20 $ sep
          [ "Considering potential critical pair at top-level: "
          , nest 2 $ prettyTCM $ lhs1 , " =?= "
          , nest 2 $ prettyTCM $ lhs2
          ]

        maybeCriticalPair <- tryUnification lhs1 lhs2 $ do
          -- Unify the left-hand sides of both rewrite rules
          fa   <- defType <$> getConstInfo f
          fpol <- getPolarity' CmpEq f
          onlyReduceTypes $
            compareElims fpol [] fa (Def f []) es1 es2

          -- Get the rhs of both rewrite rules (after unification)
          let rhs1 = applySubst sub1 $ rewRHS rew1
              rhs2 = applySubst sub2 $ rewRHS rew2

          return (rhs1 , rhs2)

        let a   = applySubst sub1 $ rewType rew1
            lhs = Def f es1

        whenJust maybeCriticalPair $ \ (rhs1 , rhs2) ->
          checkCriticalPair a lhs rhs1 rhs2

    -- Check confluence between two rules that overlap at a subpattern,
    -- e.g. @f ps[g qs] --> a@ and @g qs' --> b@.
    checkConfluenceSub :: RewriteRule -> RewriteRule -> OneHolePattern PElims -> TCM ()
    checkConfluenceSub rew1 rew2 hole =
      traceCall (CheckConfluence (rewName rew1) (rewName rew2)) $
      localTCStateSavingWarnings $ do

        let f          = rewHead rew1
            PDef g es' = ohpContents hole
            bvTel      = ohpBoundVars hole
            plug       = ohpPlugHole hole

        sub1 <- makeMetaSubst $ rewContext rew1
        sub2 <- makeMetaSubst $ rewContext rew2

        es1 <- applySubst (liftS (size bvTel) sub1) <$> nlPatToTerm es'
        es2 <- raise (size bvTel) . applySubst sub2 <$> nlPatToTerm (rewPats rew2)

        lhs1 <- Def f . applySubst sub1 <$> nlPatToTerm (rewPats rew1)
        lhs2 <- Def f . applySubst sub1 <$> nlPatToTerm (plug $ PTerm $ Def g es2)

        reportSDoc "rewriting.confluence" 20 $ sep
          [ "Considering potential critical pair at subpattern: "
          , nest 2 $ prettyTCM $ lhs1 , " =?= "
          , nest 2 $ prettyTCM $ lhs2
          ]

        maybeCriticalPair <- tryUnification lhs1 lhs2 $ do
          -- Unify the subpattern of the first rewrite rule with the lhs
          -- of the second one
          ga   <- defType <$> getConstInfo g
          gpol <- getPolarity' CmpEq g
          onlyReduceTypes $ addContext bvTel $
            compareElims gpol [] ga (Def g []) es1 es2

          -- Right-hand side of first rewrite rule (after unification)
          let rhs1 = applySubst sub1 $ rewRHS rew1

          -- Left-hand side of first rewrite rule, with subpattern
          -- rewritten by the second rewrite rule
          let w = raise (size bvTel) $ applySubst sub2 $ rewRHS rew2
          reportSDoc "rewriting.confluence" 30 $ sep
            [ "Plugging hole with w = "
            , nest 2 $ addContext bvTel $ prettyTCM w
            ]
          rhs2 <- Def f . applySubst sub1 <$> nlPatToTerm (plug $ PTerm w)

          return (rhs1 , rhs2)

        let a   = applySubst sub1 $ rewType rew1

        whenJust maybeCriticalPair $ \ (rhs1 , rhs2) ->
          checkCriticalPair a lhs1 rhs1 rhs2

    getClausesAndRewriteRulesFor :: QName -> TCM [RewriteRule]
    getClausesAndRewriteRulesFor f =
      (++) <$> getClausesAsRewriteRules f <*> getRewriteRulesFor f

    -- Build a substitution that replaces all variables in the given
    -- telescope by fresh metavariables.
    makeMetaSubst :: (MonadMetaSolver m) => Telescope -> m Substitution
    makeMetaSubst gamma = parallelS . reverse . map unArg <$> newTelMeta gamma

    -- Try to run the TCM action, return @Just x@ if it succeeds with
    -- result @x@ or @Nothing@ if it throws a type error. Abort if
    -- there are any constraints.
    tryUnification :: Term -> Term -> TCM a -> TCM (Maybe a)
    tryUnification lhs1 lhs2 f = (Just <$> f)
      `catchError` \case
        err@TypeError{} -> do
          reportSDoc "rewriting.confluence" 20 $ vcat
            [ "Unification failed with error: "
            , nest 2 $ prettyTCM err
            ]
          return Nothing
        err -> throwError err
      `ifNoConstraints` return $ \pid _ -> do
        cs <- getConstraintsForProblem pid
        prettyCs <- traverse prettyConstraint $ filter interestingConstraint cs
        warning $ RewriteMaybeNonConfluent lhs1 lhs2 prettyCs
        return Nothing

    checkCriticalPair
      :: Type     -- Type of the critical pair
      -> Term     -- Unified left-hand side
      -> Term     -- First reduct
      -> Term     -- Second reduct
      -> TCM ()
    checkCriticalPair a lhs rhs1 rhs2 = do

      (a,lhs,rhs1,rhs2) <- instantiateFull (a,lhs,rhs1,rhs2)

      reportSDoc "rewriting.confluence" 10 $ sep
        [ "Found critical pair: " , nest 2 $ prettyTCM rhs1
        , " =?= " , nest 2 $ prettyTCM rhs2
        , " : " , nest 2 $ prettyTCM a ]

      let ms = Set.toList $ allMetas singleton $ (a,lhs,rhs1,rhs2)

      reportSDoc "rewriting.confluence" 30 $ sep
        [ "Abstracting over metas: "
        , prettyList_ (map (text . show) ms)
        ]
      (gamma , (a,lhs,rhs1,rhs2)) <- fromMaybe __IMPOSSIBLE__ <$>
        abstractOverMetas ms (a,lhs,rhs1,rhs2)

      addContext gamma $ do
          dontAssignMetas $ noConstraints $ equalTerm a rhs1 rhs2
        `catchError` \case
          TypeError s err -> do
            prettyErr <- withTCState (const s) $ prettyTCM err
            warning $ RewriteNonConfluent lhs rhs1 rhs2 prettyErr
          err           -> throwError err

-- | Given metavariables ms and some x, construct a telescope Γ and
--   replace all occurrences of the given metavariables in @x@ by
--   normal variables from Γ. Returns @Nothing@ if metas have cyclic
--   dependencies.
abstractOverMetas :: (MetasToVars a) => [MetaId] -> a -> TCM (Maybe (Telescope, a))
abstractOverMetas ms x = do

  -- Sort metas in dependency order
  forMM (dependencySortMetas ms) $ \ms' -> do

    -- Get types and suggested names of metas
    as <- forM ms' getMetaType
    ns <- forM ms' getMetaNameSuggestion

    -- Construct telescope (still containing the metas)
    let gamma = unflattenTel ns $ map defaultDom as

    -- Replace metas by variables
    let n           = size ms'
        metaIndex x = (n-1-) <$> elemIndex x ms'
    runReaderT (metasToVars (gamma, x)) metaIndex

-- ^ A @OneHolePattern p@ is a @p@ with a subpattern @f ps@ singled out.
data OneHolePattern a = OneHolePattern
  { ohpBoundVars :: Telescope     -- Telescope of bound variables at the hole
  , ohpPlugHole  :: NLPat -> a    -- Plug the hole with some pattern
  , ohpContents  :: NLPat         -- The pattern in the hole
  } deriving (Functor)

ohpAddBV :: ArgName -> Dom Type -> OneHolePattern a -> OneHolePattern a
ohpAddBV x a ohp = ohp { ohpBoundVars = ExtendTel a $ Abs x $ ohpBoundVars ohp }

-- ^ Given a @p@, @allPatternHoles p@ lists all the possible
--   decompositions @p = p'[(f ps)/x]@.
class AllPatternHoles p where
  allPatternHoles :: p -> [OneHolePattern p]

instance AllPatternHoles p => AllPatternHoles [p] where
  allPatternHoles []     = []
  allPatternHoles (p:ps) =
    map (fmap ( :ps)) (allPatternHoles p ) ++
    map (fmap (p:  )) (allPatternHoles ps)

instance AllPatternHoles p => AllPatternHoles (Arg p) where
  allPatternHoles x = map (fmap (x $>)) $ allPatternHoles $ unArg x

instance AllPatternHoles p => AllPatternHoles (Dom p) where
  allPatternHoles x = map (fmap (x $>)) $ allPatternHoles $ unDom x

instance AllPatternHoles p  => AllPatternHoles (Elim' p) where
  allPatternHoles = \case
    Apply x  -> map (fmap Apply) $ allPatternHoles x
    Proj{}   -> []
    IApply{} -> __IMPOSSIBLE__ -- Not yet implemented

instance AllPatternHoles p  => AllPatternHoles (Abs p) where
  allPatternHoles = \case
    Abs   i x -> map (ohpAddBV i __DUMMY_DOM__ . fmap (Abs i)) $ allPatternHoles x
    NoAbs i x -> map (fmap (NoAbs i)) $ allPatternHoles x

instance AllPatternHoles NLPType where
  allPatternHoles (NLPType l a) = map (fmap $ NLPType l) $ allPatternHoles a

instance AllPatternHoles NLPat where
  allPatternHoles = \case
    PVar i xs      -> []
    PTerm u        -> []
    p@(PDef f es)      ->
      (OneHolePattern EmptyTel id p) :
      map (fmap $ PDef f) (allPatternHoles es)
    PLam i u       -> map (fmap $ PLam i) $ allPatternHoles u
    PPi a b        ->
      map (fmap $ \a -> PPi a b) (allPatternHoles a) ++
      map (fmap $ \b -> PPi a b) (allPatternHoles b)
    PBoundVar i es -> []

-- ^ Convert from a non-linear pattern to a term
class NLPatToTerm p a where
  nlPatToTerm
    :: (MonadReduce m, HasBuiltins m, HasConstInfo m, MonadDebug m)
    => p -> m a
  default nlPatToTerm ::
    ( NLPatToTerm p' a', Traversable f, p ~ f p', a ~ f a'
    , MonadReduce m, HasBuiltins m, HasConstInfo m, MonadDebug m
    ) => p -> m a
  nlPatToTerm = traverse nlPatToTerm

instance NLPatToTerm p a => NLPatToTerm [p] [a] where
instance NLPatToTerm p a => NLPatToTerm (Arg p) (Arg a) where
instance NLPatToTerm p a => NLPatToTerm (Dom p) (Dom a) where
instance NLPatToTerm p a => NLPatToTerm (Elim' p) (Elim' a) where
instance NLPatToTerm p a => NLPatToTerm (Abs p) (Abs a) where

instance NLPatToTerm Nat Term where
  nlPatToTerm = return . var

instance NLPatToTerm NLPat Term where
  nlPatToTerm = \case
    PVar i xs      -> Var i . map Apply <$> nlPatToTerm xs
    PTerm u        -> return u
    PDef f es      -> (theDef <$> getConstInfo f) >>= \case
      Constructor{ conSrcCon = c } -> Con c ConOSystem <$> nlPatToTerm es
      _                            -> Def f <$> nlPatToTerm es
    PLam i u       -> Lam i <$> nlPatToTerm u
    PPi a b        -> Pi <$> nlPatToTerm a <*> nlPatToTerm b
    PBoundVar i es -> Var i <$> nlPatToTerm es

instance NLPatToTerm NLPat Level where
  nlPatToTerm = nlPatToTerm >=> levelView

instance NLPatToTerm NLPType Type where
  nlPatToTerm (NLPType l a) = El <$> (Type <$> nlPatToTerm l) <*> nlPatToTerm a

-- | Convert metavariables to normal variables. Warning: doesn't
--   convert sort metas.
class MetasToVars a where
  metasToVars
    :: (MonadReader (MetaId -> Maybe Nat) m , HasBuiltins m)
    => a -> m a

  default metasToVars
    :: ( MetasToVars a', Traversable f, a ~ f a'
       , MonadReader (MetaId -> Maybe Nat) m , HasBuiltins m)
    => a -> m a
  metasToVars = traverse metasToVars

instance MetasToVars a => MetasToVars [a] where
instance MetasToVars a => MetasToVars (Arg a) where
instance MetasToVars a => MetasToVars (Dom a) where
instance MetasToVars a => MetasToVars (Elim' a) where

instance MetasToVars a => MetasToVars (Abs a) where
  metasToVars (Abs   i x) = Abs i   <$> local (fmap succ .) (metasToVars x)
  metasToVars (NoAbs i x) = NoAbs i <$> metasToVars x

instance MetasToVars Term where
  metasToVars = \case
    Var i es   -> Var i    <$> metasToVars es
    Lam i u    -> Lam i    <$> metasToVars u
    Lit l      -> Lit      <$> pure l
    Def f es   -> Def f    <$> metasToVars es
    Con c i es -> Con c i  <$> metasToVars es
    Pi a b     -> Pi       <$> metasToVars a <*> metasToVars b
    Sort s     -> Sort     <$> metasToVars s
    Level l    -> Level    <$> metasToVars l
    MetaV x es -> ($ x) <$> ask >>= \case
      Just i   -> Var i    <$> metasToVars es
      Nothing  -> MetaV x  <$> metasToVars es
    DontCare u -> DontCare <$> metasToVars u
    Dummy s es -> Dummy s  <$> metasToVars es

instance MetasToVars Type where
  metasToVars (El s t) = El <$> metasToVars s <*> metasToVars t

instance MetasToVars Sort where
  metasToVars = \case
    Type l     -> Type     <$> metasToVars l
    Prop l     -> Prop     <$> metasToVars l
    Inf        -> pure Inf
    SizeUniv   -> pure SizeUniv
    PiSort s t -> PiSort   <$> metasToVars s <*> metasToVars t
    UnivSort s -> UnivSort <$> metasToVars s
    MetaS x es -> MetaS x  <$> metasToVars es
    DefS f es  -> DefS f   <$> metasToVars es
    DummyS s   -> pure $ DummyS s

instance MetasToVars Level where
  metasToVars (Max ls) = Max <$> metasToVars ls

instance MetasToVars PlusLevel where
  metasToVars (ClosedLevel n) = pure $ ClosedLevel n
  metasToVars (Plus n x)      = Plus n <$> metasToVars x

instance MetasToVars LevelAtom where
  metasToVars = \case
    MetaLevel m es    -> NeutralLevel mempty <$> metasToVars (MetaV m es)
    BlockedLevel _ u  -> UnreducedLevel      <$> metasToVars u
    NeutralLevel nb u -> NeutralLevel nb     <$> metasToVars u
    UnreducedLevel u  -> UnreducedLevel      <$> metasToVars u

instance MetasToVars a => MetasToVars (Tele a) where
  metasToVars EmptyTel = pure EmptyTel
  metasToVars (ExtendTel a tel) = ExtendTel <$> metasToVars a <*> metasToVars tel

instance (MetasToVars a, MetasToVars b) => MetasToVars (a,b) where
  metasToVars (x,y) = (,) <$> metasToVars x <*> metasToVars y

instance (MetasToVars a, MetasToVars b, MetasToVars c) => MetasToVars (a,b,c) where
  metasToVars (x,y,z) = (,,) <$> metasToVars x <*> metasToVars y <*> metasToVars z

instance (MetasToVars a, MetasToVars b, MetasToVars c, MetasToVars d) => MetasToVars (a,b,c,d) where
  metasToVars (x,y,z,w) = (,,,) <$> metasToVars x <*> metasToVars y <*> metasToVars z <*> metasToVars w
