{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE NondecreasingIndentation #-}

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

module Agda.TypeChecking.Rewriting.Confluence ( checkConfluenceOfRules , checkConfluenceOfClause ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader

import Data.Function ( on )
import Data.Functor ( ($>) )
import Data.List ( elemIndex , tails )
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance ( workOnTypes )
import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Pretty.Warning
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting.Clause
import Agda.TypeChecking.Rewriting.NonLinPattern
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.Size


-- ^ Check confluence of the given rewrite rules wrt all other rewrite
--   rules (also amongst themselves).
checkConfluenceOfRules :: [RewriteRule] -> TCM ()
checkConfluenceOfRules = checkConfluenceOfRules' False

-- ^ Check confluence of the given clause wrt rewrite rules of the
-- constructors it matches against
checkConfluenceOfClause :: QName -> Int -> Clause -> TCM ()
checkConfluenceOfClause f i cl = do
  fi <- clauseQName f i
  whenJust (clauseToRewriteRule f fi cl) $ \rew -> do
    checkConfluenceOfRules' True [rew]
    let matchables = getMatchables rew
    reportSDoc "rewriting.confluence" 30 $
      "Function" <+> prettyTCM f <+> "has matchable symbols" <+> prettyList_ (map prettyTCM matchables)
    modifySignature $ setMatchableSymbols f matchables

checkConfluenceOfRules' :: Bool -> [RewriteRule] -> TCM ()
checkConfluenceOfRules' isClause rews = inTopContext $ inAbstractMode $ do

  forM_ (tails rews) $ listCase (return ()) $ \rew rewsRest -> do

  reportSDoc "rewriting.confluence" 10 $
    "Checking confluence of rule" <+> prettyTCM (rewName rew)

  let f   = rewHead rew
      qs  = rewPats rew
      tel = rewContext rew
  def <- getConstInfo f
  (fa , hdf) <- addContext tel $ makeHead def (rewType rew)

  -- Step 1: check other rewrite rules that overlap at top position
  forMM_ (getRulesFor f isClause) $ \ rew' ->
    unless (any (sameName rew') $ rew:rewsRest) $
      checkConfluenceTop hdf rew rew'

  -- Step 2: check other rewrite rules that overlap with a subpattern
  -- of this rewrite rule
  es <- nlPatToTerm qs
  forMM_ (addContext tel $ allHolesList (fa, hdf) es) $ \ hole ->
    caseMaybe (headView $ ohContents hole) __IMPOSSIBLE__ $ \ (g , hdg , _) -> do
      forMM_ (getRulesFor g isClause) $ \rew' ->
        unless (any (sameName rew') rewsRest) $
          checkConfluenceSub hdf hdg rew rew' hole

  -- Step 3: check other rewrite rules that have a subpattern which
  -- overlaps with this rewrite rule
  forM_ (defMatchable def) $ \ g -> do
    forMM_ (getClausesAndRewriteRulesFor g) $ \ rew' -> do
      unless (any (sameName rew') rewsRest) $ do
        es' <- nlPatToTerm (rewPats rew')
        let tel' = rewContext rew'
        def' <- getConstInfo g
        (ga , hdg) <- addContext tel' $ makeHead def' (rewType rew')
        forMM_ (addContext tel' $ allHolesList (ga , hdg) es') $ \ hole ->
          caseMaybe (headView $ ohContents hole) __IMPOSSIBLE__ $ \ (f' , _ , _) ->
            when (f == f') $ checkConfluenceSub hdg hdf rew' rew hole

  where

    sameName = (==) `on` rewName

    -- Check confluence of two rewrite rules that have the same head symbol,
    -- e.g. @f ps --> a@ and @f ps' --> b@.
    checkConfluenceTop :: (Elims -> Term) -> RewriteRule -> RewriteRule -> TCM ()
    checkConfluenceTop hd rew1 rew2 =
      traceCall (CheckConfluence (rewName rew1) (rewName rew2)) $
      localTCStateSavingWarnings $ do

        sub1 <- makeMetaSubst $ rewContext rew1
        sub2 <- makeMetaSubst $ rewContext rew2

        let f    = rewHead rew1 -- == rewHead rew2
            a1   = applySubst sub1 $ rewType rew1
            a2   = applySubst sub2 $ rewType rew2

        es1 <- applySubst sub1 <$> nlPatToTerm (rewPats rew1)
        es2 <- applySubst sub2 <$> nlPatToTerm (rewPats rew2)

        -- Make sure we are comparing eliminations with the same arity
        -- (see #3810).
        let n = min (size es1) (size es2)
            (es1' , es1r) = splitAt n es1
            (es2' , es2r) = splitAt n es2

            lhs1 = hd $ es1' ++ es2r
            lhs2 = hd $ es2' ++ es1r

            -- Use type of rewrite rule with the most eliminations
            a | null es1r = a2
              | otherwise = a1

        reportSDoc "rewriting.confluence" 20 $ sep
          [ "Considering potential critical pair at top-level: "
          , nest 2 $ prettyTCM $ lhs1, " =?= "
          , nest 2 $ prettyTCM $ lhs2 , " : " , nest 2 $ prettyTCM a
          ]

        maybeCriticalPair <- tryUnification lhs1 lhs2 $ do
          -- Unify the left-hand sides of both rewrite rules
          fa   <- defType <$> getConstInfo f
          fpol <- getPolarity' CmpEq f
          onlyReduceTypes $
            compareElims fpol [] fa (hd []) es1' es2'

          -- Get the rhs of both rewrite rules (after unification). In
          -- case of different arities, add additional arguments from
          -- one side to the other side.
          let rhs1 = applySubst sub1 (rewRHS rew1) `applyE` es2r
              rhs2 = applySubst sub2 (rewRHS rew2) `applyE` es1r

          return (rhs1 , rhs2)

        whenJust maybeCriticalPair $ \ (rhs1 , rhs2) ->
          checkCriticalPair a hd (es1' ++ es2r) rhs1 rhs2

    -- Check confluence between two rules that overlap at a subpattern,
    -- e.g. @f ps[g qs] --> a@ and @g qs' --> b@.
    checkConfluenceSub :: (Elims -> Term) -> (Elims -> Term) -> RewriteRule -> RewriteRule -> OneHole Elims -> TCM ()
    checkConfluenceSub hdf hdg rew1 rew2 hole0 =
      traceCall (CheckConfluence (rewName rew1) (rewName rew2)) $
      localTCStateSavingWarnings $ do

        sub1 <- makeMetaSubst $ rewContext rew1

        let f          = rewHead rew1
            bvTel0     = ohBoundVars hole0
            k          = size bvTel0
            b0         = applySubst (liftS k sub1) $ ohType hole0
            (g,_,es0)  = fromMaybe __IMPOSSIBLE__ $ headView $
                           applySubst (liftS k sub1) $ ohContents hole0
            qs2        = rewPats rew2

        -- If the second rewrite rule has more eliminations than the
        -- subpattern of the first rule, the only chance of overlap is
        -- by eta-expanding the subpattern of the first rule.
        hole1 <- addContext bvTel0 $
          forceEtaExpansion b0 (hdg es0) $ drop (size es0) qs2

        verboseS "rewriting.confluence.eta" 30 $
          unless (size es0 == size qs2) $
          addContext bvTel0 $
          reportSDoc "rewriting.confluence.eta" 30 $ vcat
            [ "forceEtaExpansion result:"
            , nest 2 $ "bound vars: " <+> prettyTCM (ohBoundVars hole1)
            , nest 2 $ "hole contents: " <+> addContext (ohBoundVars hole1) (prettyTCM $ ohContents hole1)
            ]

        let hole      = hole1 `composeHole` hole0
            (g,_,es') = fromMaybe __IMPOSSIBLE__ $ headView $ ohContents hole -- g == rewHead rew2
            bvTel     = ohBoundVars hole
            plug      = ohPlugHole hole

        sub2 <- addContext bvTel $ makeMetaSubst $ rewContext rew2

        let es1 = applySubst (liftS (size bvTel) sub1) es'
        es2 <- applySubst sub2 <$> nlPatToTerm (rewPats rew2)

        -- Make sure we are comparing eliminations with the same arity
        -- (see #3810). Because we forced eta-expansion of es1, we
        -- know that it is at least as long as es2.
        when (size es1 < size es2) __IMPOSSIBLE__
        let n = size es2
            (es1' , es1r) = splitAt n es1

        let lhs1 = applySubst sub1 $ hdf $ plug $ hdg es1
            lhs2 = applySubst sub1 $ hdf $ plug $ hdg $ es2 ++ es1r
            a    = applySubst sub1 $ rewType rew1

        reportSDoc "rewriting.confluence" 20 $ sep
          [ "Considering potential critical pair at subpattern: "
          , nest 2 $ prettyTCM $ lhs1 , " =?= "
          , nest 2 $ prettyTCM $ lhs2 , " : " , nest 2 $ prettyTCM a
          ]

        maybeCriticalPair <- tryUnification lhs1 lhs2 $ do
          -- Unify the subpattern of the first rewrite rule with the lhs
          -- of the second one
          ga   <- defType <$> getConstInfo g
          gpol <- getPolarity' CmpEq g
          onlyReduceTypes $ addContext bvTel $
            compareElims gpol [] ga (hdg []) es1' es2

          -- Right-hand side of first rewrite rule (after unification)
          let rhs1 = applySubst sub1 $ rewRHS rew1

          -- Left-hand side of first rewrite rule, with subpattern
          -- rewritten by the second rewrite rule
          let w = applySubst sub2 (rewRHS rew2) `applyE` es1r
          reportSDoc "rewriting.confluence" 30 $ sep
            [ "Plugging hole with w = "
            , nest 2 $ addContext bvTel $ prettyTCM w
            ]
          let rhs2 = applySubst sub1 $ hdf $ plug w

          return (rhs1 , rhs2)

        whenJust maybeCriticalPair $ \ (rhs1 , rhs2) ->
          checkCriticalPair a hdf (applySubst sub1 $ plug $ hdg es1) rhs1 rhs2

    headView :: Term -> Maybe (QName, Elims -> Term, Elims)
    headView (Def f es) = Just (f , Def f , es)
    headView (Con c ci es) = Just (conName c , Con c ci , es)
    headView _ = Nothing

    makeHead :: Definition -> Type -> TCM (Type , Elims -> Term)
    makeHead def a = case theDef def of
      Constructor{ conSrcCon = ch } -> do
        ca <- snd . fromMaybe __IMPOSSIBLE__ <$> getFullyAppliedConType ch a
        return (ca , Con ch ConOSystem)
      -- For record projections @f : R Δ → A@, we rely on the invariant
      -- that any clause is fully general in the parameters, i.e. it
      -- is quantified over the parameter telescope @Δ@
      Function { funProjection = Just proj } -> do
        let f          = projOrig proj
            r          = unArg $ projFromType proj
        rtype <- defType <$> getConstInfo r
        TelV ptel _ <- telView rtype
        n <- getContextSize
        let pars :: Args
            pars = raise (n - size ptel) $ teleArgs ptel
        ftype <- defType def `piApplyM` pars
        return (ftype , Def f)
      _ -> return (defType def , Def $ defName def)

    getClausesAndRewriteRulesFor :: QName -> TCM [RewriteRule]
    getClausesAndRewriteRulesFor f =
      (++) <$> getClausesAsRewriteRules f <*> getRewriteRulesFor f

    getRulesFor :: QName -> Bool -> TCM [RewriteRule]
    getRulesFor f isClause
      | isClause  = getRewriteRulesFor f
      | otherwise = getClausesAndRewriteRulesFor f

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
        prettyCs <- prettyInterestingConstraints cs
        warning $ RewriteMaybeNonConfluent lhs1 lhs2 prettyCs
        return Nothing

    checkCriticalPair
      :: Type     -- Type of the critical pair
      -> (Elims -> Term)  -- Head of lhs
      -> Elims            -- Eliminations of lhs
      -> Term     -- First reduct
      -> Term     -- Second reduct
      -> TCM ()
    checkCriticalPair a hd es rhs1 rhs2 = do

      (a,es,rhs1,rhs2) <- instantiateFull (a,es,rhs1,rhs2)

      let ms = Set.toList $ allMetas singleton $ (a,es,rhs1,rhs2)

      reportSDoc "rewriting.confluence" 30 $ sep
        [ "Abstracting over metas: "
        , prettyList_ (map (text . show) ms)
        ]
      (gamma , (a,es,rhs1,rhs2)) <- fromMaybe __IMPOSSIBLE__ <$>
        abstractOverMetas ms (a,es,rhs1,rhs2)

      addContext gamma $ reportSDoc "rewriting.confluence" 10 $ sep
        [ "Found critical pair: " , nest 2 $ prettyTCM rhs1
        , " =?= " , nest 2 $ prettyTCM rhs2
        , " : " , nest 2 $ prettyTCM a ]

      addContext gamma $ do
          dontAssignMetas $ noConstraints $ equalTerm a rhs1 rhs2
        `catchError` \case
          TypeError s err -> do
            prettyErr <- withTCState (const s) $ prettyTCM err
            warning $ RewriteNonConfluent (hd es) rhs1 rhs2 prettyErr
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

-- ^ A @OneHole p@ is a @p@ with a subpattern @f ps@ singled out.
data OneHole a = OneHole
  { ohBoundVars :: Telescope     -- Telescope of bound variables at the hole
  , ohType      :: Type          -- Type of the term in the hole
  , ohPlugHole  :: Term -> a     -- Plug the hole with some term
  , ohContents  :: Term          -- The term in the hole
  } deriving (Functor)

-- | The trivial hole
idHole :: Type -> Term -> OneHole Term
idHole a v = OneHole EmptyTel a id v

-- | Plug a hole with another hole
composeHole :: OneHole Term -> OneHole a -> OneHole a
composeHole inner outer = OneHole
  { ohBoundVars = ohBoundVars outer `abstract` ohBoundVars inner
  , ohType      = ohType inner
  , ohPlugHole  = ohPlugHole outer . ohPlugHole inner
  , ohContents  = ohContents inner
  }

ohAddBV :: ArgName -> Dom Type -> OneHole a -> OneHole a
ohAddBV x a oh = oh { ohBoundVars = ExtendTel a $ Abs x $ ohBoundVars oh }

-- ^ Given a @p : a@, @allHoles p@ lists all the possible
--   decompositions @p = p'[(f ps)/x]@.
class (Subst Term p , Free p) => AllHoles p where
  type PType p
  allHoles :: (Alternative m , MonadReduce m, MonadAddContext m, HasBuiltins m, HasConstInfo m)
           => PType p -> p -> m (OneHole p)

allHoles_
  :: ( Alternative m , MonadReduce m, MonadAddContext m, HasBuiltins m, HasConstInfo m, MonadDebug m
     , AllHoles p , PType p ~ () )
  => p -> m (OneHole p)
allHoles_ = allHoles ()

allHolesList
  :: ( MonadReduce m, MonadAddContext m, HasBuiltins m, HasConstInfo m , AllHoles p)
  => PType p -> p -> m [OneHole p]
allHolesList a = sequenceListT . allHoles a

-- | Given a term @v : a@ and eliminations @es@, force eta-expansion
--   of @v@ to match the structure (Apply/Proj) of the eliminations.
--
--   Examples:
--
--   1. @v : _A@ and @es = [$ w]@: this will instantiate
--      @_A := (x : _A1) → _A2@ and return the @OneHole Term@
--      @λ x → [v x]@.
--
--   2. @v : _A@ and @es = [.fst]@: this will instantiate
--      @_A := _A1 × _A2@ and return the @OneHole Term@
--      @([v .fst]) , (v .snd)@.
forceEtaExpansion :: Type -> Term -> [Elim' a] -> TCM (OneHole Term)
forceEtaExpansion a v [] = return $ idHole a v
forceEtaExpansion a v (e:es) = case e of

  Apply (Arg i w) -> do

    -- Force a to be a pi type
    reportSDoc "rewriting.confluence.eta" 40 $ fsep
      [ "Forcing" , prettyTCM v , ":" , prettyTCM a , "to take one more argument" ]
    dom <- defaultArgDom i <$> newTypeMeta_
    cod <- addContext dom $ newTypeMeta_
    equalType a $ mkPi (("x",) <$> dom) cod

    -- Construct body of eta-expansion
    let body = raise 1 v `apply` [Arg i $ var 0]

    -- Continue with remaining eliminations
    addContext dom $ ohAddBV "x" dom . fmap (Lam i . mkAbs "x") <$>
      forceEtaExpansion cod body es

  Proj o f -> do

    -- Force a to be the right record type for projection by f
    reportSDoc "rewriting.confluence.eta" 40 $ fsep
      [ "Forcing" , prettyTCM v , ":" , prettyTCM a , "to be projectible by" , prettyTCM f ]
    r <- fromMaybe __IMPOSSIBLE__ <$> getRecordOfField f
    rdef <- getConstInfo r
    let ra = defType rdef
    pars <- newArgsMeta ra
    s <- ra `piApplyM` pars >>= \s -> ifIsSort s return __IMPOSSIBLE__
    equalType a $ El s (Def r $ map Apply pars)

    -- Eta-expand v at record type r, and get field corresponding to f
    (_ , c , ci , fields) <- etaExpandRecord_ r pars (theDef rdef) v
    let fs        = map argFromDom $ recFields $ theDef rdef
        i         = fromMaybe __IMPOSSIBLE__ $ elemIndex f $ map unArg fs
        fContent  = unArg $ fromMaybe __IMPOSSIBLE__ $ fields !!! i
        fUpdate w = Con c ci $ map Apply $ updateAt i (w <$) fields

    -- Get type of field corresponding to f
    ~(Just (El _ (Pi b c))) <- getDefType f =<< reduce a
    let fa = c `absApp` v

    -- Continue with remaining eliminations
    fmap fUpdate <$> forceEtaExpansion fa fContent es

  IApply{} -> __IMPOSSIBLE__ -- Not yet implemented

-- ^ Instances for @AllHoles@

instance AllHoles p => AllHoles (Arg p) where
  type PType (Arg p) = Dom (PType p)
  allHoles a x = fmap (x $>) <$> allHoles (unDom a) (unArg x)

instance AllHoles p => AllHoles (Dom p) where
  type PType (Dom p) = PType p
  allHoles a x = fmap (x $>) <$> allHoles a (unDom x)

instance AllHoles (Abs Term) where
  type PType (Abs Term) = (Dom Type , Abs Type)
  allHoles (dom , a) x = addContext (absName x , dom) $
    ohAddBV (absName a) dom . fmap (mkAbs $ absName x) <$>
      allHoles (absBody a) (absBody x)

instance AllHoles (Abs Type) where
  type PType (Abs Type) = Dom Type
  allHoles dom a = addContext (absName a , dom) $
    ohAddBV (absName a) dom . fmap (mkAbs $ absName a) <$>
      allHoles_ (absBody a)

instance AllHoles Elims where
  type PType Elims = (Type , Elims -> Term)
  allHoles (a,hd) [] = empty
  allHoles (a,hd) (e:es) = do
    reportSDoc "rewriting.confluence.hole" 65 $ fsep
      [ "Head symbol" , prettyTCM (hd []) , ":" , prettyTCM a
      , "is eliminated by" , prettyTCM e
      ]
    case e of
      Apply x -> do
        ~(Pi b c) <- unEl <$> reduce a
        let a'  = c `absApp` unArg x
            hd' = hd . (e:)
        (fmap ((:es) . Apply) <$> allHoles b x)
         <|> (fmap (e:) <$> allHoles (a' , hd') es)
      Proj o f -> do
        ~(Just (El _ (Pi b c))) <- getDefType f =<< reduce a
        let a' = c `absApp` hd []
        hd' <- applyE <$> applyDef o f (argFromDom b $> hd [])
        fmap (e:) <$> allHoles (a' , hd') es
      IApply x y u -> __IMPOSSIBLE__ -- Not yet implemented

instance AllHoles Type where
  type PType Type = ()
  allHoles _ (El s a) = workOnTypes $
    fmap (El s) <$> allHoles (sort s) a

instance AllHoles Term where
  type PType Term = Type
  allHoles a u = do
    reportSDoc "rewriting.confluence.hole" 60 $ fsep
      [ "Getting holes of term" , prettyTCM u , ":" , prettyTCM a ]
    case u of
      Var i es       -> do
        ai <- typeOfBV i
        fmap (Var i) <$> allHoles (ai , Var i) es
      Lam i u        -> do
        ~(Pi b c) <- unEl <$> reduce a
        fmap (Lam i) <$> allHoles (b,c) u
      Lit l          -> empty
      v@(Def f es)   -> do
        fa <- defType <$> getConstInfo f
        pure (idHole a v)
         <|> (fmap (Def f) <$> allHoles (fa , Def f) es)
      v@(Con c ci es) -> do
        ca <- snd . fromMaybe __IMPOSSIBLE__ <$> do
          getFullyAppliedConType c =<< reduce a
        pure (idHole a v)
         <|> (fmap (Con c ci) <$> allHoles (ca , Con c ci) es)
      Pi a b         ->
        (fmap (\a -> Pi a b) <$> allHoles_ a) <|>
        (fmap (\b -> Pi a b) <$> allHoles a b)
      Sort s         -> fmap Sort <$> allHoles_ s
      Level l        -> fmap Level <$> allHoles_ l
      MetaV{}        -> __IMPOSSIBLE__
      DontCare{}     -> empty
      Dummy{}        -> empty

instance AllHoles Sort where
  type PType Sort = ()
  allHoles _ = \case
    Type l       -> fmap Type <$> allHoles_ l
    Prop l       -> fmap Prop <$> allHoles_ l
    Inf          -> empty
    SizeUniv     -> empty
    PiSort{}     -> __IMPOSSIBLE__
    FunSort{}    -> __IMPOSSIBLE__
    UnivSort{}   -> __IMPOSSIBLE__
    MetaS{}      -> __IMPOSSIBLE__
    DefS f es    -> do
      fa <- defType <$> getConstInfo f
      fmap (DefS f) <$> allHoles (fa , Def f) es
    DummyS{}     -> empty

instance AllHoles Level where
  type PType Level = ()
  allHoles _ (Max n ls) = fmap (Max n) <$> allHoles_ ls

instance AllHoles [PlusLevel] where
  type PType [PlusLevel] = ()
  allHoles _ []     = empty
  allHoles _ (l:ls) =
    (fmap (:ls) <$> allHoles_ l)
    <|> (fmap (l:) <$> allHoles_ ls)

instance AllHoles PlusLevel where
  type PType PlusLevel = ()
  allHoles _ (Plus n l) = fmap (Plus n) <$> allHoles_ l

instance AllHoles LevelAtom where
  type PType LevelAtom = ()
  allHoles _ l = do
    la <- levelType
    case l of
      MetaLevel{}      -> __IMPOSSIBLE__
      BlockedLevel{}   -> __IMPOSSIBLE__
      NeutralLevel b u -> fmap (NeutralLevel b) <$> allHoles la u
      UnreducedLevel u -> fmap UnreducedLevel <$> allHoles la u


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
    FunSort s t -> FunSort <$> metasToVars s <*> metasToVars t
    UnivSort s -> UnivSort <$> metasToVars s
    MetaS x es -> MetaS x  <$> metasToVars es
    DefS f es  -> DefS f   <$> metasToVars es
    DummyS s   -> pure $ DummyS s

instance MetasToVars Level where
  metasToVars (Max n ls) = Max n <$> metasToVars ls

instance MetasToVars PlusLevel where
  metasToVars (Plus n x) = Plus n <$> metasToVars x

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
