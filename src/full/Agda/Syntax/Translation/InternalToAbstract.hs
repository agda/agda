{-# LANGUAGE NondecreasingIndentation   #-}

{-|
    Translating from internal syntax to abstract syntax. Enables nice
    pretty printing of internal syntax.

    TODO

        - numbers on metas
        - fake dependent functions to independent functions
        - meta parameters
        - shadowing
-}
module Agda.Syntax.Translation.InternalToAbstract
  ( Reify(..)
  , MonadReify
  , NamedClause(..)
  , reifyPatterns
  , reifyUnblocked
  , blankNotInScope
  , reifyDisplayFormP
  ) where

import Prelude hiding (null)

import Control.Applicative ( liftA2 )
import Control.Arrow       ( (&&&) )
import Control.Monad       ( filterM, forM )

import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe
import Data.Semigroup ( Semigroup, (<>) )
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Traversable (mapM)

import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Concrete (FieldAssignment'(..))
import Agda.Syntax.Info as Info
import Agda.Syntax.Abstract as A hiding (Binder)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Abstract.UsedNames
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import Agda.Syntax.Scope.Base (inverseScopeLookupName)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Records
import Agda.TypeChecking.CompiledClause (CompiledClauses'(Fail))
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.Level
import {-# SOURCE #-} Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.SyntacticEquality
import Agda.TypeChecking.Telescope

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Syntax.Common.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible


-- | Like @reify@ but instantiates blocking metas, useful for reporting.
reifyUnblocked :: Reify i => i -> TCM (ReifiesTo i)
reifyUnblocked t = locallyTCState stInstantiateBlocking (const True) $ reify t


-- Composition of reified applications ------------------------------------
--UNUSED Liang-Ting 2019-07-16
---- | Drops hidden arguments unless --show-implicit.
--napps :: Expr -> [NamedArg Expr] -> TCM Expr
--napps e = nelims e . map I.Apply

-- | Drops hidden arguments unless --show-implicit.
apps :: MonadReify m => Expr -> [Arg Expr] -> m Expr
apps e = elims e . map I.Apply

-- Composition of reified eliminations ------------------------------------

-- | Drops hidden arguments unless --show-implicit.
nelims :: MonadReify m => Expr -> [I.Elim' (Named_ Expr)] -> m Expr
nelims e [] = return e
nelims e (I.IApply x y r : es) =
  nelims (A.App defaultAppInfo_ e $ defaultArg r) es
nelims e (I.Apply arg : es) = do
  arg <- reify arg  -- This replaces the arg by _ if irrelevant
  dontShowImp <- not <$> showImplicitArguments
  let hd | notVisible arg && dontShowImp = e
         | otherwise                     = A.App defaultAppInfo_ e arg
  nelims hd es
nelims e (I.Proj ProjPrefix d : es)             = nelimsProjPrefix e d es
nelims e (I.Proj o          d : es) | isSelf e  = nelims (A.Proj ProjPrefix $ unambiguous d) es
                                    | otherwise =
  nelims (A.App defaultAppInfo_ e (defaultNamedArg $ A.Proj o $ unambiguous d)) es

nelimsProjPrefix :: MonadReify m => Expr -> QName -> [I.Elim' (Named_ Expr)] -> m Expr
nelimsProjPrefix e d es =
  nelims (A.App defaultAppInfo_ (A.Proj ProjPrefix $ unambiguous d) $ defaultNamedArg e) es

-- | If we are referencing the record from inside the record definition, we don't insert an
-- | A.App
isSelf :: Expr -> Bool
isSelf = \case
  A.Var n -> nameIsRecordName n
  _ -> False

-- | Drops hidden arguments unless --show-implicit.
elims :: MonadReify m => Expr -> [I.Elim' Expr] -> m Expr
elims e = nelims e . map (fmap unnamed)

-- Omitting information ---------------------------------------------------

noExprInfo :: ExprInfo
noExprInfo = ExprRange noRange

-- Conditional reification to omit terms that are not shown --------------

reifyWhenE :: (Reify i, MonadReify m, Underscore (ReifiesTo i)) => Bool -> i -> m (ReifiesTo i)
reifyWhenE True  i = reify i
reifyWhenE False t = return underscore

-- Reification ------------------------------------------------------------

type MonadReify m =
  ( PureTCM m
  , MonadInteractionPoints m
  , MonadFresh NameId m
  )

class Reify i where
    type ReifiesTo i

    reify :: MonadReify m => i -> m (ReifiesTo i)

    --   @reifyWhen False@ should produce an 'underscore'.
    --   This function serves to reify hidden/irrelevant things.
    reifyWhen :: MonadReify m => Bool -> i -> m (ReifiesTo i)
    reifyWhen _ = reify

instance Reify Bool where
    type ReifiesTo Bool = Bool
    reify = return

instance Reify Name where
    type ReifiesTo Name = Name
    reify = return

instance Reify Expr where
    type ReifiesTo Expr = Expr

    reifyWhen = reifyWhenE
    reify = return

instance Reify MetaId where
    type ReifiesTo MetaId = Expr

    reifyWhen = reifyWhenE
    reify x = do
      b <- asksTC envPrintMetasBare
      mi  <- mvInfo <$> lookupLocalMeta x
      let mi' = Info.MetaInfo
                 { metaRange          = getRange $ miClosRange mi
                 , metaScope          = clScope $ miClosRange mi
                 , metaNumber         = if b then Nothing else Just x
                 , metaNameSuggestion = if b then "" else miNameSuggestion mi
                 }
          underscore = return $ A.Underscore mi'
      -- If we are printing a term that will be pasted into the user
      -- source, we turn all unsolved (non-interaction) metas into
      -- interaction points
      isInteractionMeta x >>= \case
        Nothing | b -> do
          ii <- registerInteractionPoint False noRange Nothing
          connectInteractionPoint ii x
          return $ A.QuestionMark mi' ii
        Just ii | b -> underscore
        Nothing     -> underscore
        Just ii     -> return $ A.QuestionMark mi' ii

instance Reify DisplayTerm where
  type ReifiesTo DisplayTerm = Expr

  reifyWhen = reifyWhenE
  reify = \case
    DTerm' v es       -> elims ==<< (reifyTerm False v, reify es)
    DDot'  v es       -> elims ==<< (reify v, reify es)
    DCon c ci vs      -> recOrCon (conName c) ci =<< reify vs
    DDef f es         -> elims (A.Def f) =<< reify es
    DWithApp u us es0 -> do
      (e, es) <- reify (u, us)
      elims (if null es then e else A.WithApp noExprInfo e es) =<< reify es0

-- | @reifyDisplayForm f vs fallback@
--   tries to rewrite @f vs@ with a display form for @f@.
--   If successful, reifies the resulting display term,
--   otherwise, does @fallback@.
reifyDisplayForm :: MonadReify m => QName -> I.Elims -> m A.Expr -> m A.Expr
reifyDisplayForm f es fallback =
  ifNotM displayFormsEnabled fallback $ {- else -}
    caseMaybeM (displayForm f es) fallback reify

-- | @reifyDisplayFormP@ tries to recursively
--   rewrite a lhs with a display form.
--
--   Note: we are not necessarily in the empty context upon entry!
reifyDisplayFormP
  :: MonadReify m
  => QName         -- ^ LHS head symbol
  -> A.Patterns    -- ^ Patterns to be taken into account to find display form.
  -> A.Patterns    -- ^ Remaining trailing patterns ("with patterns").
  -> m (QName, A.Patterns) -- ^ New head symbol and new patterns.
reifyDisplayFormP f ps wps = do
  let fallback = return (f, ps ++ wps)
  ifNotM displayFormsEnabled fallback $ {- else -} do
    -- Try to rewrite @f 0 1 2 ... |ps|-1@ to a dt.
    -- Andreas, 2014-06-11  Issue 1177:
    -- I thought we need to add the placeholders for ps to the context,
    -- because otherwise displayForm will not raise the display term
    -- and we will have variable clashes.
    -- But apparently, it has no influence...
    -- Ulf, can you add an explanation?
    md <- -- addContext (replicate (length ps) "x") $
      displayForm f $ zipWith (\ p i -> I.Apply $ p $> I.var i) ps [0..]
    reportSLn "reify.display" 60 $
      "display form of " ++ prettyShow f ++ " " ++ show ps ++ " " ++ show wps ++ ":\n  " ++ show md
    case md of
      Just d  | okDisplayForm d -> do
        -- In the display term @d@, @var i@ should be a placeholder
        -- for the @i@th pattern of @ps@.
        -- Andreas, 2014-06-11:
        -- Are we sure that @d@ did not use @var i@ otherwise?
        (f', ps', wps') <- displayLHS ps d
        reportSDoc "reify.display" 70 $ do
          doc <- prettyA $ SpineLHS empty f' (ps' ++ wps' ++ wps)
          return $ vcat
            [ "rewritten lhs to"
            , "  lhs' = " <+> doc
            ]
        reifyDisplayFormP f' ps' (wps' ++ wps)
      _ -> do
        reportSLn "reify.display" 70 $ "display form absent or not valid as lhs"
        fallback
  where
    -- Andreas, 2015-05-03: Ulf, please comment on what
    -- is the idea behind okDisplayForm.
    -- Ulf, 2016-04-15: okDisplayForm should return True if the display form
    -- can serve as a valid left-hand side. That means checking that it is a
    -- defined name applied to valid lhs eliminators (projections or
    -- applications to constructor patterns).
    okDisplayForm :: DisplayTerm -> Bool
    okDisplayForm = \case
      DWithApp d ds es ->
        okDisplayForm d && all okDisplayTerm ds  && all okToDropE es
        -- Andreas, 2016-05-03, issue #1950.
        -- We might drop trailing hidden trivial (=variable) patterns.
      DTerm' (I.Def f es') es -> all okElim es' && all okElim es
      DDef f es               -> all okDElim es
      DDot'{}                 -> False
      DCon{}                  -> False
      DTerm'{}                -> False

    okDisplayTerm :: DisplayTerm -> Bool
    okDisplayTerm = \case
      DTerm' v es -> null es && okTerm v
      DDot'{}     -> True
      DCon{}      -> True
      DDef{}      -> False
      DWithApp{}  -> False

    okDElim :: Elim' DisplayTerm -> Bool
    okDElim (I.IApply x y r) = okDisplayTerm r
    okDElim (I.Apply v) = okDisplayTerm $ unArg v
    okDElim I.Proj{}    = True

    okToDropE :: Elim' Term -> Bool
    okToDropE (I.Apply v) = okToDrop v
    okToDropE I.Proj{}    = False
    okToDropE (I.IApply x y r) = False

    okToDrop :: Arg I.Term -> Bool
    okToDrop arg = notVisible arg && case unArg arg of
      I.Var _ []   -> True
      I.DontCare{} -> True  -- no matching on irrelevant things.  __IMPOSSIBLE__ anyway?
      I.Level{}    -> True  -- no matching on levels. __IMPOSSIBLE__ anyway?
      _ -> False

    okArg :: Arg I.Term -> Bool
    okArg = okTerm . unArg

    okElim :: Elim' I.Term -> Bool
    okElim (I.IApply x y r) = okTerm r
    okElim (I.Apply a) = okArg a
    okElim I.Proj{}  = True

    okTerm :: I.Term -> Bool
    okTerm (I.Var _ []) = True
    okTerm (I.Con c ci vs) = all okElim vs
    okTerm (I.Def x []) = isNoName $ qnameToConcrete x -- Handling wildcards in display forms
    okTerm _            = False

    -- Flatten a dt into (parentName, parentElims, withArgs).
    flattenWith :: DisplayTerm -> (QName, [I.Elim' DisplayTerm], [I.Elim' DisplayTerm])
    flattenWith (DWithApp d ds1 es2) =
      let (f, es, ds0) = flattenWith d
      in  (f, es, ds0 ++ map (I.Apply . defaultArg) ds1 ++ map (fmap DTerm) es2)
    flattenWith (DDef f es) = (f, es, [])     -- .^ hacky, but we should only hit this when printing debug info
    flattenWith (DTerm' (I.Def f es') es) = (f, map (fmap DTerm) $ es' ++ es, [])
    flattenWith _ = __IMPOSSIBLE__

    displayLHS
      :: MonadReify m
      => A.Patterns   -- Patterns to substituted into display term.
      -> DisplayTerm  -- Display term.
      -> m (QName, A.Patterns, A.Patterns)  -- New head, patterns, with-patterns.
    displayLHS ps d = do
        let (f, vs, es) = flattenWith d
        ps  <- mapM elimToPat vs
        wps <- mapM (updateNamedArg (A.WithP empty) <.> elimToPat) es
        return (f, ps, wps)
      where
        argToPat :: MonadReify m => Arg DisplayTerm -> m (NamedArg A.Pattern)
        argToPat arg = traverse termToPat arg

        elimToPat :: MonadReify m => I.Elim' DisplayTerm -> m (NamedArg A.Pattern)
        elimToPat (I.IApply _ _ r) = argToPat (Arg defaultArgInfo r)
        elimToPat (I.Apply arg) = argToPat arg
        elimToPat (I.Proj o d)  = return $ defaultNamedArg $ A.ProjP patNoRange o $ unambiguous d

        -- Substitute variables in display term by patterns.
        termToPat :: MonadReify m => DisplayTerm -> m (Named_ A.Pattern)

        -- Main action HERE:
        termToPat (DTerm (I.Var n [])) =
          return $ unArg $ fromMaybe __IMPOSSIBLE__ $ ps !!! n

        termToPat (DCon c ci vs)          = fmap unnamed <$> tryRecPFromConP =<< do
           A.ConP (ConPatInfo ci patNoRange ConPatEager) (unambiguous (conName c)) <$> mapM argToPat vs

        termToPat (DTerm' (I.Con c ci vs) es) = fmap unnamed <$> tryRecPFromConP =<< do
           A.ConP (ConPatInfo ci patNoRange ConPatEager) (unambiguous (conName c)) <$>
             mapM (elimToPat . fmap DTerm) (vs ++ es)

        termToPat (DTerm (I.Def _ [])) = return $ unnamed $ A.WildP patNoRange
        termToPat (DDef _ [])          = return $ unnamed $ A.WildP patNoRange

        termToPat (DTerm (I.Lit l))    = return $ unnamed $ A.LitP patNoRange l

        termToPat (DDot' v es) =
          unnamed . A.DotP patNoRange <$> do elims ==<< (termToExpr v, reify es)

        termToPat v =
          unnamed . A.DotP patNoRange <$> reify v

        len = length ps

        argsToExpr :: MonadReify m => I.Args -> m [Arg A.Expr]
        argsToExpr = mapM (traverse termToExpr)

        -- TODO: restructure this to avoid having to repeat the code for reify
        termToExpr :: MonadReify m => Term -> m A.Expr
        termToExpr v = do
          reportSLn "reify.display" 60 $ "termToExpr " ++ show v
          -- After unSpine, a Proj elimination is __IMPOSSIBLE__!
          case unSpine v of
            I.Con c ci es -> do
              let vs = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es
              apps (A.Con (unambiguous (conName c))) =<< argsToExpr vs
            I.Def f es -> do
              let vs = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es
              apps (A.Def f) =<< argsToExpr vs
            I.Var n es -> do
              let vs = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es
              -- Andreas, 2014-06-11  Issue 1177
              -- due to β-normalization in substitution,
              -- even the pattern variables @n < len@ can be
              -- applied to some args @vs@.
              e <- if n < len
                   then return $ A.patternToExpr $ namedArg $ indexWithDefault __IMPOSSIBLE__ ps n
                   else reify (I.var (n - len))
              apps e =<< argsToExpr vs
            _ -> return underscore

instance Reify Literal where
  type ReifiesTo Literal = Expr

  reifyWhen = reifyWhenE
  reify l = return $ A.Lit empty l

instance Reify Term where
  type ReifiesTo Term = Expr

  reifyWhen = reifyWhenE
  reify v = reifyTerm True v

reifyPathPConstAsPath :: MonadReify m => QName -> Elims -> m (QName, Elims)
reifyPathPConstAsPath x es@[I.Apply l, I.Apply t, I.Apply lhs, I.Apply rhs] = do
   reportSLn "reify.def" 100 $ "reifying def path " ++ show (x,es)
   mpath  <- getBuiltinName' builtinPath
   mpathp <- getBuiltinName' builtinPathP
   let fallback = return (x,es)
   case (,) <$> mpath <*> mpathp of
     Just (path,pathp) | x == pathp -> do
       let a = case unArg t of
                I.Lam _ (NoAbs _ b)    -> Just b
                I.Lam _ (Abs   _ b)
                  | not $ 0 `freeIn` b -> Just (strengthen impossible b)
                _                      -> Nothing
       case a of
         Just a -> return (path, [I.Apply l, I.Apply (setHiding Hidden $ defaultArg a), I.Apply lhs, I.Apply rhs])
         Nothing -> fallback
     _ -> fallback
reifyPathPConstAsPath x es = return (x,es)

-- | Check if the term matches an existing let-binding, in that case use the corresponding variable,
--   otherwise reify using the continuation.
tryReifyAsLetBinding :: MonadReify m => Term -> m Expr -> m Expr
tryReifyAsLetBinding v fallback = ifM (asksTC $ not . envFoldLetBindings) fallback $ do
  letBindings <- do
    binds  <- asksTC (Map.toAscList . envLetBindings)
    opened <- forM binds $ \ (name, open) -> (,name) <$> getOpen open
    return [ (body, name) | (LetBinding UserWritten body _, name) <- opened, not $ isNoName name ]  -- Only fold user-written lets
  matchingBindings <- filterM (\t -> checkSyntacticEquality v (fst t) (\_ _ -> return True) (\_ _ -> return False)) letBindings
  case matchingBindings of
    (_, name) : _ -> return $ A.Var name
    []            -> fallback

reifyTerm ::
      MonadReify m
   => Bool           -- ^ Try to expand away anonymous definitions?
   -> Term
   -> m Expr
reifyTerm expandAnonDefs0 v0 = tryReifyAsLetBinding v0 $ do
  -- Jesper 2018-11-02: If 'PrintMetasBare', drop all meta eliminations.
  metasBare <- asksTC envPrintMetasBare
  reportSDoc "reify.term" 80 $ pure $ "reifyTerm v0 = " <+> pretty v0
  v <- instantiate v0 >>= \case
    I.MetaV x _ | metasBare -> return $ I.MetaV x []
    v -> return v
  reportSDoc "reify.term" 80 $ pure $ "reifyTerm v = " <+> pretty v
  -- Ulf 2014-07-10: Don't expand anonymous when display forms are disabled
  -- (i.e. when we don't care about nice printing)
  expandAnonDefs <- return expandAnonDefs0 `and2M` displayFormsEnabled
  -- Andreas, 2016-07-21 if --postfix-projections
  -- then we print system-generated projections as postfix, else prefix.
  havePfp <- optPostfixProjections <$> pragmaOptions
  let pred = if havePfp then (== ProjPrefix) else (/= ProjPostfix)
  reportSDoc "reify.term" 80 $ pure $ "reifyTerm (unSpine v) = " <+> pretty (unSpine' pred v)
  case unSpine' pred v of
    -- Hack to print generalized field projections with nicer names. Should
    -- only show up in errors. Check the spined form!
    _ | I.Var n (I.Proj _ p : es) <- v,
        Just name <- getGeneralizedFieldName p -> do
      let fakeName = (qnameName p) {nameConcrete = C.simpleName name} -- TODO: infix names!?
      elims (A.Var fakeName) =<< reify es
    I.Var n es -> do
      x <- fromMaybeM (freshName_ $ "@" ++ show n) $ nameOfBV' n
      elims (A.Var x) =<< reify es
    I.Def x es -> do
      reportSDoc "reify.def" 80 $ return $ "reifying def" <+> pretty x
      (x, es) <- reifyPathPConstAsPath x es
      reifyDisplayForm x es $ reifyDef expandAnonDefs x es
    I.Con c ci vs -> do
      let x = conName c
      isR <- isGeneratedRecordConstructor x
      if isR || ci == ConORec
        then do
          showImp <- showImplicitArguments
          let keep (a, v) = showImp || visible a
          r <- getConstructorData x
          xs <- fromMaybe __IMPOSSIBLE__ <$> getRecordFieldNames_ r
          vs <- map unArg <$> reify (fromMaybe __IMPOSSIBLE__ $ allApplyElims vs)
          return $ A.Rec noExprInfo $ map (Left . uncurry FieldAssignment . mapFst unDom) $ filter keep $ zip xs vs
        else reifyDisplayForm x vs $ do
          def <- getConstInfo x
          let Constructor {conPars = np} = theDef def
          -- if we are the the module that defines constructor x
          -- then we have to drop at least the n module parameters
          n <- getDefFreeVars x
          -- the number of parameters is greater (if the data decl has
          -- extra parameters) or equal (if not) to n
          when (n > np) __IMPOSSIBLE__
          let h = A.Con (unambiguous x)
          if null vs
            then return h
            else do
              es <- reify (map (fromMaybe __IMPOSSIBLE__ . isApplyElim) vs)
              -- Andreas, 2012-04-20: do not reify parameter arguments of constructor
              -- if the first regular constructor argument is hidden
              -- we turn it into a named argument, in order to avoid confusion
              -- with the parameter arguments which can be supplied in abstract syntax
              --
              -- Andreas, 2012-09-17: this does not remove all sources of confusion,
              -- since parameters could have the same name as regular arguments
              -- (see for example the parameter {i} to Data.Star.Star, which is also
              -- the first argument to the cons).
              -- @data Star {i}{I : Set i} ... where cons : {i :  I} ...@
              if np == 0
                then apps h es
                else do
                  -- Get name of first argument from type of constructor.
                  -- Here, we need the reducing version of @telView@
                  -- because target of constructor could be a definition
                  -- expanding into a function type.  See test/succeed/NameFirstIfHidden.agda.
                  TelV tel _ <- telView (defType def)
                  let (pars, rest) = splitAt np $ telToList tel
                  case rest of
                    -- Andreas, 2012-09-18
                    -- If the first regular constructor argument is hidden,
                    -- we keep the parameters to avoid confusion.
                    (Dom {domInfo = info} : _) | notVisible info -> do
                      let us = for (drop n pars) $ \(Dom {domInfo = ai}) ->
                            -- setRelevance Relevant $
                            hideOrKeepInstance $ Arg ai underscore
                      apps h $ us ++ es -- Note: unless --show-implicit, @apps@ will drop @us@.
                    -- otherwise, we drop all parameters
                    _ -> apps h es

--    I.Lam info b | isAbsurdBody b -> return $ A. AbsurdLam noExprInfo $ getHiding info
    I.Lam info b    -> do
      (x,e) <- reify b
      -- #4160: Hacky solution: if --show-implicit, treat all lambdas as user-written. This will
      -- prevent them from being dropped by AbstractToConcrete (where we don't have easy access to
      -- the --show-implicit flag.
      info <- ifM showImplicitArguments (return $ setOrigin UserWritten info) (return info)
      return $ A.Lam exprNoRange (mkDomainFree $ unnamedArg info $ mkBinder_ x) e
      -- Andreas, 2011-04-07 we do not need relevance information at internal Lambda
    I.Lit l        -> reify l
    I.Level l      -> reify l
    I.Pi a b       -> case b of
        NoAbs _ b'
          | visible a, not (domIsFinite a) -> uncurry (A.Fun $ noExprInfo) <$> reify (a, b')
            -- Andreas, 2013-11-11 Hidden/Instance I.Pi must be A.Pi
            -- since (a) the syntax {A} -> B or {{A}} -> B is not legal
            -- and (b) the name of the binder might matter.
            -- See issue 951 (a) and 952 (b).
            --
            -- Amy, 2022-09-05: Can't be finite either, since otherwise
            -- we say ".(IsOne φ) → A ≠ .(IsOne φ) → A" with no
            -- indication of which is finite and which isn't
          | otherwise   -> mkPi b =<< reify a
        b               -> mkPi b =<< do
          ifM (domainFree a (absBody b))
            {- then -} (pure $ Arg (domInfo a) underscore)
            {- else -} (reify a)
      where
        mkPi b (Arg info a') = ifM (skipGeneralizedParameter info) (snd <$> reify b) $ do
          tac <- traverse (Ranged noRange <.> reify) $ domTactic a
          (x, b) <- reify b
          let xs = singleton $ Arg info $ Named (domName a) $ mkBinder_ x
          return $ A.Pi noExprInfo
            (singleton $ TBind noRange (TypedBindingInfo tac (domIsFinite a)) xs a')
            b
        -- We can omit the domain type if it doesn't have any free variables
        -- and it's mentioned in the target type.
        domainFree a b = do
          df <- asksTC envPrintDomainFreePi
          return $ df && freeIn 0 b && closed a

        skipGeneralizedParameter :: MonadReify m => ArgInfo -> m Bool
        skipGeneralizedParameter info = (not <$> showGeneralizedArguments) <&> (&& (argInfoOrigin info == Generalization))

    I.Sort s     -> reify s
    I.MetaV x es -> do
          x' <- reify x

          es' <- reify es

          mv <- lookupLocalMeta x
          (msub1,meta_tel,msub2) <- do
            local_chkpt <- viewTC eCurrentCheckpoint
            (chkpt, tel, msub2) <- enterClosure mv $ \ _ ->
                               (,,) <$> viewTC eCurrentCheckpoint
                                    <*> getContextTelescope
                                    <*> viewTC (eCheckpoints . key local_chkpt)
            (,,) <$> viewTC (eCheckpoints . key chkpt) <*> pure tel <*> pure msub2

          opt_show_ids <- showIdentitySubstitutions
          let
              addNames []    es = map (fmap unnamed) es
              addNames _     [] = []
              addNames xs     (I.Proj{} : _) = __IMPOSSIBLE__
              addNames xs     (I.IApply x y r : es) =
                -- Needs to be I.Apply so it can have an Origin field.
                addNames xs (I.Apply (defaultArg r) : es)
              addNames (x:xs) (I.Apply arg : es) =
                I.Apply (Named (Just x) <$> (setOrigin Substitution arg)) : addNames xs es

              p = mvPermutation mv
              applyPerm p vs = permute (takeP (size vs) p) vs

              names = map (WithOrigin Inserted . unranged) $ p `applyPerm` teleNames meta_tel
              named_es' = addNames names es'

              dropIdentitySubs sub_local2G sub_tel2G =
                 let
                     args_G = applySubst sub_tel2G $ p `applyPerm` (teleArgs meta_tel :: [Arg Term])
                     es_G = sub_local2G `applySubst` es
                     sameVar x (I.Apply y) = isJust xv && xv == deBruijnView (unArg y)
                      where
                       xv = deBruijnView $ unArg x
                     sameVar _ _ = False
                     dropArg = take (size names) $ zipWith sameVar args_G es_G
                     doDrop (b : xs)  (e : es) = (if b then id else (e :)) $ doDrop xs es
                     doDrop []        es = es
                     doDrop _         [] = []
                 in doDrop dropArg $ named_es'

              simpl_named_es' | opt_show_ids                 = named_es'
                              | Just sub_mtel2local <- msub1 = dropIdentitySubs IdS           sub_mtel2local
                              | Just sub_local2mtel <- msub2 = dropIdentitySubs sub_local2mtel IdS
                              | otherwise                    = named_es'

          nelims x' simpl_named_es'

    I.DontCare v -> do
      showIrr <- optShowIrrelevant <$> pragmaOptions
      if | showIrr   -> reifyTerm expandAnonDefs v
         | otherwise -> return underscore
    I.Dummy s [] -> return $ A.Lit empty $ LitString (T.pack s)
    I.Dummy "applyE" es | I.Apply (Arg _ h) : es' <- es -> do
                            h <- reify h
                            es' <- reify es'
                            elims h es'
                        | otherwise -> __IMPOSSIBLE__
    I.Dummy s es -> do
      s <- reify (I.Dummy s [])
      es <- reify es
      elims s es
  where
    -- Andreas, 2012-10-20  expand a copy if not in scope
    -- to improve error messages.
    -- Don't do this if we have just expanded into a display form,
    -- otherwise we loop!
    reifyDef :: MonadReify m => Bool -> QName -> I.Elims -> m Expr
    reifyDef True x es =
      ifM (not . null . inverseScopeLookupName x <$> getScope) (reifyDef' x es) $ do
      r <- reduceDefCopy x es
      case r of
        YesReduction _ v -> do
          reportS "reify.anon" 60
            [ "reduction on defined ident. in anonymous module"
            , "x = " ++ prettyShow x
            , "v = " ++ show v
            ]
          reify v
        NoReduction () -> do
          reportS "reify.anon" 60
            [ "no reduction on defined ident. in anonymous module"
            , "x  = " ++ prettyShow x
            , "es = " ++ show es
            ]
          reifyDef' x es
    reifyDef _ x es = reifyDef' x es

    reifyDef' :: MonadReify m => QName -> I.Elims -> m Expr
    reifyDef' x es = do
      reportSLn "reify.def" 60 $ "reifying call to " ++ prettyShow x
      -- We should drop this many arguments from the local context.
      n <- getDefFreeVars x
      reportSLn "reify.def" 70 $ "freeVars for " ++ prettyShow x ++ " = " ++ show n
      -- If the definition is not (yet) in the signature,
      -- we just do the obvious.
      let fallback _ = elims (A.Def x) =<< reify (drop n es)
      caseEitherM (getConstInfo' x) fallback $ \ defn -> do
      let def = theDef defn

      -- Check if we have an absurd lambda.
      case def of
       Function{ funCompiled = Just Fail{}, funClauses = [cl] }
          | isAbsurdLambdaName x -> do
                  -- get hiding info from last pattern, which should be ()
                  let (ps, p) = fromMaybe __IMPOSSIBLE__ $ initLast $ namedClausePats cl
                  let h = getHiding p
                      n = length ps  -- drop all args before the absurd one
                      absLam = A.AbsurdLam exprNoRange h
                  if | n > length es -> do -- We don't have all arguments before the absurd one!
                        let name (I.VarP _ x) = patVarNameToString $ dbPatVarName x
                            name _            = __IMPOSSIBLE__  -- only variables before absurd pattern
                            vars = map (getArgInfo &&& name . namedArg) $ drop (length es) ps
                            lam (i, s) = do
                              x <- freshName_ s
                              return $ A.Lam exprNoRange (A.mkDomainFree $ unnamedArg i $ A.mkBinder_ x)
                        foldr ($) absLam <$> mapM lam vars
                      | otherwise -> elims absLam =<< reify (drop n es)

      -- Otherwise (no absurd lambda):
       _ -> do

        -- Andrea(s), 2016-07-06
        -- Extended lambdas are not considered to be projection like,
        -- as they are mutually recursive with their parent.
        -- Thus we do not have to consider padding them.

        -- Check whether we have an extended lambda and display forms are on.
        df <- displayFormsEnabled

        -- #3004: give up if we have to print a pattern lambda inside its own body!
        alreadyPrinting <- viewTC ePrintingPatternLambdas

        extLam <- case def of
          Function{ funExtLam = Just{}, funProjection = Right{} } -> __IMPOSSIBLE__
          Function{ funExtLam = Just (ExtLamInfo m b sys) } ->
            Just . (,Strict.toLazy sys) . size <$> lookupSection m
          _ -> return Nothing

        -- Amy, 2023-04-12: Don't reify clauses generated by the cubical
        -- coverage checker when printing an extended lambda. We can
        -- identify these clauses by looking for patterns headed by DefP
        -- (either transpX or hcomp associated with a data type).
        --
        -- Since these are always automatically derived, printing them
        -- is noise, and shows up even in non-cubical modules, as long
        -- as an imported extended lambda is defined cubical-compatibly.
        let insClause = hasDefP . namedClausePats
        case extLam of
          Just (pars, sys) | df, x `notElem` alreadyPrinting ->
            locallyTC ePrintingPatternLambdas (x :) $
            reifyExtLam x (defArgInfo defn) pars sys
              (filter (not . insClause) (defClauses defn)) es

        -- Otherwise (ordinary function call):
          _ -> do
           (pad, nes :: [Elim' (Named_ Term)]) <- case def of

            Function{ funProjection = Right Projection{ projIndex = np } } | np > 0 -> do
              reportSLn "reify.def" 70 $ "  def. is a projection with projIndex = " ++ show np

              -- This is tricky:
              --  * getDefFreeVars x tells us how many arguments
              --    are part of the local context
              --  * some of those arguments might have been dropped
              --    due to projection likeness
              --  * when showImplicits is on we'd like to see the dropped
              --    projection arguments

              TelV tel _ <- telViewUpTo np (defType defn)
              let (as, rest) = splitAt (np - 1) $ telToList tel
                  dom = headWithDefault __IMPOSSIBLE__ rest

              -- These are the dropped projection arguments
              scope <- getScope
              let underscore = A.Underscore $ Info.emptyMetaInfo { metaScope = scope }
              let pad :: [NamedArg Expr]
                  pad = for as $ \ (Dom{domInfo = ai, unDom = (x, _)}) ->
                    Arg ai $ Named (Just $ WithOrigin Inserted $ unranged x) underscore
                      -- TODO #3353 Origin from Dom?

              -- Now pad' ++ es' = drop n (pad ++ es)
              let pad' = drop n pad
                  es'  = drop (max 0 (n - size pad)) es
              -- Andreas, 2012-04-21: get rid of hidden underscores {_} and {{_}}
              -- Keep non-hidden arguments of the padding.
              --
              -- Andreas, 2016-12-20, issue #2348:
              -- Let @padTail@ be the list of arguments of the padding
              -- (*) after the last visible argument of the padding, and
              -- (*) with the same visibility as the first regular argument.
              -- If @padTail@ is not empty, we need to
              -- print the first regular argument with name.
              -- We further have to print all elements of @padTail@
              -- which have the same name and visibility of the
              -- first regular argument.
              showImp <- showImplicitArguments

              -- Get the visible arguments of the padding and the rest
              -- after the last visible argument.
              let (padVisNamed, padRest) = filterAndRest visible pad'

              -- Remove the names from the visible arguments.
              let padVis  = map (fmap $ unnamed . namedThing) padVisNamed

              -- Keep only the rest with the same visibility of @dom@...
              let padTail = filter (sameHiding dom) padRest

              -- ... and even the same name.
              let padSame = filter ((Just (fst $ unDom dom) ==) . bareNameOf) padTail

              return $ if null padTail || not showImp
                then (padVis           , map (fmap unnamed) es')
                else (padVis ++ padSame, nameFirstIfHidden dom es')

            -- If it is not a projection(-like) function, we need no padding.
            _ -> return ([], map (fmap unnamed) $ drop n es)

           reportSDoc "reify.def" 100 $ return $ vcat
             [ "  pad =" <+> pshow pad
             , "  nes =" <+> pshow nes
             ]
           let hd0 | isProperProjection def = A.Proj ProjPrefix $ AmbQ $ singleton x
                   | otherwise = A.Def x
           let hd = List.foldl' (A.App defaultAppInfo_) hd0 pad
           nelims hd =<< reify nes

    -- Andreas, 2016-07-06 Issue #2047

    -- With parameter refinement, the "parameter" patterns of an extended
    -- lambda can now be different from variable patterns.  If we just drop
    -- them (plus the associated arguments to the extended lambda), we produce
    -- something

    -- i) that violates internal invariants.  In particular, the permutation
    -- dbPatPerm from the patterns to the telescope can no longer be
    -- computed.  (And in fact, dropping from the start of the telescope is
    -- just plainly unsound then.)

    -- ii) prints the wrong thing (old fix for #2047)

    -- What we do now, is more sound, although not entirely satisfying:
    -- When the "parameter" patterns of an external lambdas are not variable
    -- patterns, we fall back to printing the internal function created for the
    -- extended lambda, instead trying to construct the nice syntax.

    reifyExtLam
      :: MonadReify m
      => QName -> ArgInfo -> Int -> Maybe System -> [I.Clause]
      -> I.Elims -> m Expr
    reifyExtLam x ai npars msys cls es = do
      reportSLn "reify.def" 10 $ "reifying extended lambda " ++ prettyShow x
      reportSLn "reify.def" 50 $ render $ nest 2 $ vcat
        [ "npars =" <+> pretty npars
        , "es    =" <+> fsep (map (prettyPrec 10) es)
        , "def   =" <+> vcat (map pretty cls) ]
      -- As extended lambda clauses live in the top level, we add the whole
      -- section telescope to the number of parameters.
      let (pares, rest) = splitAt npars es
      let pars = fromMaybe __IMPOSSIBLE__ $ allApplyElims pares

      -- Since we applying the clauses to the parameters,
      -- we do not need to drop their initial "parameter" patterns
      -- (this is taken care of by @apply@).
      cls <- caseMaybe msys
               (mapM (reify . NamedClause x False . (`apply` pars)) cls)
               (reify . QNamed x . (`apply` pars))
      let cx     = nameConcrete $ qnameName x
          dInfo  = mkDefInfo cx noFixity' PublicAccess ConcreteDef
                     (getRange x)
          erased = case getQuantity ai of
            Quantity0 o -> Erased o
            Quantityω o -> NotErased o
            Quantity1 o -> __IMPOSSIBLE__
          lam = case cls of
            []       -> A.AbsurdLam exprNoRange NotHidden
            (cl:cls) -> A.ExtendedLam exprNoRange dInfo erased x (cl :| cls)
      elims lam =<< reify rest

-- | @nameFirstIfHidden (x:a) ({e} es) = {x = e} es@
nameFirstIfHidden :: Dom (ArgName, t) -> [Elim' a] -> [Elim' (Named_ a)]
nameFirstIfHidden dom (I.Apply (Arg info e) : es) | notVisible info =
  I.Apply (Arg info (Named (Just $ WithOrigin Inserted $ unranged $ fst $ unDom dom) e)) :
  map (fmap unnamed) es
nameFirstIfHidden _ es =
  map (fmap unnamed) es

instance Reify i => Reify (Named n i) where
  type ReifiesTo (Named n i) = Named n (ReifiesTo i)

  reify = traverse reify
  reifyWhen b = traverse (reifyWhen b)

-- | Skip reification of implicit and irrelevant args if option is off.
instance Reify i => Reify (Arg i) where
  type ReifiesTo (Arg i) = Arg (ReifiesTo i)

  reify (Arg info i) = Arg info <$> (flip reifyWhen i =<< condition)
    where condition = (return (argInfoHiding info /= Hidden) `or2M` showImplicitArguments)
              `and2M` (return (getRelevance info /= Irrelevant) `or2M` showIrrelevantArguments)
  reifyWhen b i = traverse (reifyWhen b) i

-- instance Reify Elim Expr where
--   reifyWhen = reifyWhenE
--   reify = \case
--     I.IApply x y r -> appl "iapply" <$> reify (defaultArg r :: Arg Term)
--     I.Apply v -> appl "apply" <$> reify v
--     I.Proj f  -> appl "proj"  <$> reify ((defaultArg $ I.Def f []) :: Arg Term)
--     where
--       appl :: String -> Arg Expr -> Expr
--       appl s v = A.App exprInfo (A.Lit empty (LitString s)) $ fmap unnamed v

data NamedClause = NamedClause QName Bool I.Clause
  -- ^ Also tracks whether module parameters should be dropped from the patterns.

-- The Monoid instance for Data.Map doesn't require that the values are a
-- monoid.
newtype MonoidMap k v = MonoidMap { _unMonoidMap :: Map.Map k v }

instance (Ord k, Monoid v) => Semigroup (MonoidMap k v) where
  MonoidMap m1 <> MonoidMap m2 = MonoidMap (Map.unionWith mappend m1 m2)

instance (Ord k, Monoid v) => Monoid (MonoidMap k v) where
  mempty = MonoidMap Map.empty
  mappend = (<>)

-- | Removes argument names.  Preserves names present in the source.
removeNameUnlessUserWritten :: (LensNamed a, LensOrigin (NameOf a)) => a -> a
removeNameUnlessUserWritten a
  | (getOrigin <$> getNameOf a) == Just UserWritten = a
  | otherwise = setNameOf Nothing a


-- | Removes implicit arguments that are not needed, that is, that don't bind
--   any variables that are actually used and doesn't do pattern matching.
--   Doesn't strip any arguments that were written explicitly by the user.
stripImplicits :: MonadReify m
  => Set Name -- ^ Variables to always include (occurs on RHS of clause)
  -> A.Patterns -> A.Patterns -> m A.Patterns
stripImplicits toKeep params ps = do
  -- if --show-implicit we don't need the names
  ifM showImplicitArguments (return $ map (fmap removeNameUnlessUserWritten) ps) $ do
    reportSDoc "reify.implicit" 100 $ return $ vcat
      [ "stripping implicits"
      , nest 2 $ "ps   =" <+> pshow ps
      ]
    let ps' = blankDots $ strip ps
    reportSDoc "reify.implicit" 100 $ return $ vcat
      [ nest 2 $ "ps'  =" <+> pshow ps'
      ]
    return ps'
    where
      -- Replace variables in dot patterns by an underscore _ if they are hidden
      -- in the pattern. This is slightly nicer than making the implicts explicit.
      blankDots ps = blank (varsBoundIn $ params ++ ps) ps

      strip ps = stripArgs True ps
        where
          stripArgs _ [] = []
          stripArgs fixedPos (a : as)
            -- A hidden non-UserWritten variable is removed if not needed for
            -- correct position of the following hidden arguments.
            | canStrip a =
                 if   all canStrip $ takeWhile isUnnamedHidden as
                 then stripArgs False as
                 else goWild
            -- Other arguments are kept.
            | otherwise = stripName fixedPos (stripArg a) : stripArgs True as
            where
              a'     = setNamedArg a $ A.WildP $ Info.PatRange $ getRange a
              goWild = stripName fixedPos a' : stripArgs True as

          stripName True  = fmap removeNameUnlessUserWritten
          stripName False = id

          -- TODO: vars appearing in EqualPs shouldn't be stripped.
          canStrip a = and
            [ notVisible a
            , getOrigin a `notElem` [ UserWritten , CaseSplit ]
            , (getOrigin <$> getNameOf a) /= Just UserWritten
            , varOrDot (namedArg a)
            , not $ mustKeepVar (namedArg a)
            ]

          mustKeepVar (A.VarP (A.BindName x)) = Set.member x toKeep
          mustKeepVar _                       = False

          isUnnamedHidden x = notVisible x && isNothing (getNameOf x) && isNothing (isProjP x)

          stripArg a = fmap (fmap stripPat) a

          stripPat = \case
            p@(A.VarP _)        -> p
            A.ConP i c ps       -> A.ConP i c $ stripArgs True ps
            p@A.ProjP{}         -> p
            p@(A.DefP _ _ _)    -> p
            p@(A.DotP _ _e)     -> p
            p@(A.WildP _)       -> p
            p@(A.AbsurdP _)     -> p
            p@(A.LitP _ _)      -> p
            A.AsP i x p         -> A.AsP i x $ stripPat p
            A.PatternSynP _ _ _ -> __IMPOSSIBLE__
            A.RecP i fs         -> A.RecP i $ map (fmap stripPat) fs  -- TODO Andreas: is this right?
            p@A.EqualP{}        -> p -- EqualP cannot be blanked.
            A.WithP i p         -> A.WithP i $ stripPat p -- TODO #2822: right?
            A.AnnP i a p        -> A.AnnP i a $ stripPat p

          varOrDot A.VarP{}      = True
          varOrDot A.WildP{}     = True
          varOrDot A.DotP{}      = True
          varOrDot (A.ConP cpi _ ps) | conPatOrigin cpi == ConOSystem
                                 = conPatLazy cpi == ConPatLazy || all (varOrDot . namedArg) ps
          varOrDot _             = False

-- | @blankNotInScope e@ replaces variables in expression @e@ with @_@
-- if they are currently not in scope.
blankNotInScope :: (MonadTCEnv m, MonadDebug m, BlankVars a) => a -> m a
blankNotInScope e = do
  ctxNames <- getContextNames
  letNames <- map fst <$> getLetBindings
  let names = Set.fromList . filter ((== C.InScope) . C.isInScope) $ ctxNames ++ letNames
  reportSDoc "reify.blank" 80 . pure $ "names in scope for blanking:" <+> pretty names
  return $ blank names e


-- | @blank bound e@ replaces all variables in expression @e@ that are not in @bound@ by
--   an underscore @_@. It is used for printing dot patterns: we don't want to
--   make implicit variables explicit, so we blank them out in the dot patterns
--   instead (this is fine since dot patterns can be inferred anyway).

class BlankVars a where
  blank :: Set Name -> a -> a

  default blank :: (Functor f, BlankVars b, f b ~ a) => Set Name -> a -> a
  blank = fmap . blank

instance BlankVars a => BlankVars (Arg a)
instance BlankVars a => BlankVars (Named s a)
instance BlankVars a => BlankVars [a]
instance BlankVars a => BlankVars (List1 a)
instance BlankVars a => BlankVars (FieldAssignment' a)
-- instance BlankVars a => BlankVars (A.Pattern' a)         -- see case EqualP !

instance (BlankVars a, BlankVars b) => BlankVars (a, b) where
  blank bound (x, y) = (blank bound x, blank bound y)

instance (BlankVars a, BlankVars b) => BlankVars (Either a b) where
  blank bound (Left x)  = Left $ blank bound x
  blank bound (Right y) = Right $ blank bound y

instance BlankVars A.ProblemEq where
  blank bound = id

instance BlankVars A.Clause where
  blank bound (A.Clause lhs strippedPats rhs wh ca)
    | null wh =
        A.Clause (blank bound' lhs)
                 (blank bound' strippedPats)
                 (blank bound' rhs) noWhereDecls ca
    | otherwise = __IMPOSSIBLE__
    where bound' = varsBoundIn lhs `Set.union` bound

instance BlankVars A.LHS where
  blank bound (A.LHS i core) = A.LHS i $ blank bound core

instance BlankVars A.LHSCore where
  blank bound (A.LHSHead f ps) = A.LHSHead f $ blank bound ps
  blank bound (A.LHSProj p b ps) = uncurry (A.LHSProj p) $ blank bound (b, ps)
  blank bound (A.LHSWith h wps ps) = uncurry (uncurry A.LHSWith) $ blank bound ((h, wps), ps)

instance BlankVars A.Pattern where
  blank bound p = case p of
    A.VarP _      -> p   -- do not blank pattern vars
    A.ConP c i ps -> A.ConP c i $ blank bound ps
    A.ProjP{}     -> p
    A.DefP i f ps -> A.DefP i f $ blank bound ps
    A.DotP i e    -> A.DotP i $ blank bound e
    A.WildP _     -> p
    A.AbsurdP _   -> p
    A.LitP _ _    -> p
    A.AsP i n p   -> A.AsP i n $ blank bound p
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__
    A.RecP i fs   -> A.RecP i $ blank bound fs
    A.EqualP{}    -> p
    A.WithP i p   -> A.WithP i (blank bound p)
    A.AnnP i a p  -> A.AnnP i (blank bound a) (blank bound p)

instance BlankVars A.Expr where
  blank bound e = case e of
    A.ScopedExpr i e         -> A.ScopedExpr i $ blank bound e
    A.Var x                  -> if x `Set.member` bound then e
                                else A.Underscore emptyMetaInfo  -- Here is the action!
    A.Def' _ _               -> e
    A.Proj{}                 -> e
    A.Con _                  -> e
    A.Lit _ _                -> e
    A.QuestionMark{}         -> e
    A.Underscore _           -> e
    A.Dot i e                -> A.Dot i $ blank bound e
    A.App i e1 e2            -> uncurry (A.App i) $ blank bound (e1, e2)
    A.WithApp i e es         -> uncurry (A.WithApp i) $ blank bound (e, es)
    A.Lam i b e              -> let bound' = varsBoundIn b `Set.union` bound
                                in  A.Lam i (blank bound b) (blank bound' e)
    A.AbsurdLam _ _          -> e
    A.ExtendedLam i d e f cs -> A.ExtendedLam i d e f $ blank bound cs
    A.Pi i tel e             -> let bound' = varsBoundIn tel `Set.union` bound
                                in  uncurry (A.Pi i) $ blank bound' (tel, e)
    A.Generalized {}         -> __IMPOSSIBLE__
    A.Fun i a b              -> uncurry (A.Fun i) $ blank bound (a, b)
    A.Let _ _ _              -> __IMPOSSIBLE__
    A.Rec i es               -> A.Rec i $ blank bound es
    A.RecUpdate i e es       -> uncurry (A.RecUpdate i) $ blank bound (e, es)
    A.Quote {}               -> __IMPOSSIBLE__
    A.QuoteTerm {}           -> __IMPOSSIBLE__
    A.Unquote {}             -> __IMPOSSIBLE__
    A.DontCare v             -> A.DontCare $ blank bound v
    A.PatternSyn {}          -> e
    A.Macro {}               -> e

instance BlankVars A.ModuleName where
  blank bound = id

instance BlankVars RHS where
  blank bound (RHS e mc)             = RHS (blank bound e) mc
  blank bound AbsurdRHS              = AbsurdRHS
  blank bound (WithRHS _ es clauses) = __IMPOSSIBLE__ -- NZ
  blank bound (RewriteRHS xes spats rhs _) = __IMPOSSIBLE__ -- NZ

instance BlankVars A.LamBinding where
  blank bound b@A.DomainFree{} = b
  blank bound (A.DomainFull bs) = A.DomainFull $ blank bound bs

instance BlankVars TypedBinding where
  blank bound (TBind r t n e) = TBind r t n $ blank bound e
  blank bound (TLet _ _)    = __IMPOSSIBLE__ -- Since the internal syntax has no let bindings left


-- | Collect the binders in some abstract syntax lhs.

class Binder a where
  varsBoundIn :: a -> Set Name

  default varsBoundIn :: (Foldable f, Binder b, f b ~ a) => a -> Set Name
  varsBoundIn = foldMap varsBoundIn

instance Binder A.LHS where
  varsBoundIn (A.LHS _ core) = varsBoundIn core

instance Binder A.LHSCore where
  varsBoundIn (A.LHSHead _ ps)     = varsBoundIn ps
  varsBoundIn (A.LHSProj _ b ps)   = varsBoundIn (b, ps)
  varsBoundIn (A.LHSWith h wps ps) = varsBoundIn ((h, wps), ps)

instance Binder A.Pattern where
  varsBoundIn = foldAPattern $ \case
    A.VarP x            -> varsBoundIn x
    A.AsP _ x _         -> empty    -- Not x because of #2414 (?)
    A.ConP _ _ _        -> empty
    A.ProjP{}           -> empty
    A.DefP _ _ _        -> empty
    A.WildP{}           -> empty
    A.DotP{}            -> empty
    A.AbsurdP{}         -> empty
    A.LitP{}            -> empty
    A.PatternSynP _ _ _ -> empty
    A.RecP _ _          -> empty
    A.EqualP{}          -> empty
    A.WithP _ _         -> empty
    A.AnnP{}            -> empty

instance Binder a => Binder (A.Binder' a) where
  varsBoundIn (A.Binder p n) = varsBoundIn (p, n)

instance Binder A.LamBinding where
  varsBoundIn (A.DomainFree _ x) = varsBoundIn x
  varsBoundIn (A.DomainFull b)   = varsBoundIn b

instance Binder TypedBinding where
  varsBoundIn (TBind _ _ xs _) = varsBoundIn xs
  varsBoundIn (TLet _ bs)      = varsBoundIn bs

instance Binder BindName where
  varsBoundIn x = singleton (unBind x)

instance Binder A.LetBinding where
  varsBoundIn (LetBind _ _ x _ _) = varsBoundIn x
  varsBoundIn (LetPatBind _ p _)  = varsBoundIn p
  varsBoundIn LetApply{}          = empty
  varsBoundIn LetOpen{}           = empty
  varsBoundIn LetDeclaredVariable{} = empty

instance Binder a => Binder (FieldAssignment' a)
instance Binder a => Binder (Arg a)
instance Binder a => Binder (Named x a)
instance Binder a => Binder [a]
instance Binder a => Binder (List1 a)
instance Binder a => Binder (Maybe a)

instance (Binder a, Binder b) => Binder (a, b) where
  varsBoundIn (x, y) = varsBoundIn x `Set.union` varsBoundIn y


-- | Assumes that pattern variables have been added to the context already.
--   Picks pattern variable names from context.
reifyPatterns :: MonadReify m => [NamedArg I.DeBruijnPattern] -> m [NamedArg A.Pattern]
reifyPatterns = mapM $ (stripNameFromExplicit . stripHidingFromPostfixProj) <.>
                       traverse (traverse reifyPat)
  where
    -- #4399 strip also empty names
    stripNameFromExplicit :: NamedArg p -> NamedArg p
    stripNameFromExplicit a
      | visible a || maybe True (liftA2 (||) null isNoName) (bareNameOf a) =
          fmap (unnamed . namedThing) a
      | otherwise = a

    stripHidingFromPostfixProj :: IsProjP p => NamedArg p -> NamedArg p
    stripHidingFromPostfixProj a = case isProjP a of
      Just (o, _) | o /= ProjPrefix -> setHiding NotHidden a
      _                             -> a

    reifyPat :: MonadReify m => I.DeBruijnPattern -> m A.Pattern
    reifyPat p = do
     reportSDoc "reify.pat" 80 $ return $ "reifying pattern" <+> pretty p
     keepVars <- optKeepPatternVariables <$> pragmaOptions
     case p of
      -- Possibly expanded literal pattern (see #4215)
      p | Just (PatternInfo PatOLit asB) <- patternInfo p -> do
        reduce (I.patternToTerm p) >>= \case
          I.Lit l -> addAsBindings asB $ return $ A.LitP empty l
          _       -> __IMPOSSIBLE__
      I.VarP i x -> addAsBindings (patAsNames i) $ case patOrigin i of
        o@PatODot  -> reifyDotP o $ var $ dbPatVarIndex x
        PatOWild   -> return $ A.WildP patNoRange
        PatOAbsurd -> return $ A.AbsurdP patNoRange
        _          -> reifyVarP x
      I.DotP i v -> addAsBindings (patAsNames i) $ case patOrigin i of
        PatOWild   -> return $ A.WildP patNoRange
        PatOAbsurd -> return $ A.AbsurdP patNoRange
        -- If Agda turned a user variable @x@ into @.x@, print it back as @x@.
        o@(PatOVar x) | I.Var i [] <- v -> do
          x' <- nameOfBV i
          if nameConcrete x == nameConcrete x' then
            return $ A.VarP $ mkBindName x'
          else
            reifyDotP o v
        o -> reifyDotP o v
      I.LitP i l  -> addAsBindings (patAsNames i) $ return $ A.LitP empty l
      I.ProjP o d -> return $ A.ProjP patNoRange o $ unambiguous d
      I.ConP c cpi ps | conPRecord cpi -> addAsBindings (patAsNames $ conPInfo cpi) $
        case patOrigin (conPInfo cpi) of
          PatOWild   -> return $ A.WildP patNoRange
          PatOAbsurd -> return $ A.AbsurdP patNoRange
          PatOVar x | keepVars -> return $ A.VarP $ mkBindName x
          _               -> reifyConP c cpi ps
      I.ConP c cpi ps -> addAsBindings (patAsNames $ conPInfo cpi) $ reifyConP c cpi ps
      I.DefP i f ps  -> addAsBindings (patAsNames i) $ case patOrigin i of
        PatOWild   -> return $ A.WildP patNoRange
        PatOAbsurd -> return $ A.AbsurdP patNoRange
        PatOVar x | keepVars -> return $ A.VarP $ mkBindName x
        _ -> A.DefP patNoRange (unambiguous f) <$> reifyPatterns ps
      I.IApplyP i _ _ x -> addAsBindings (patAsNames i) $ case patOrigin i of
        o@PatODot  -> reifyDotP o $ var $ dbPatVarIndex x
        PatOWild   -> return $ A.WildP patNoRange
        PatOAbsurd -> return $ A.AbsurdP patNoRange
        _          -> reifyVarP x

    reifyVarP :: MonadReify m => DBPatVar -> m A.Pattern
    reifyVarP x = do
      n <- nameOfBV $ dbPatVarIndex x
      let y = dbPatVarName x
      if | y == "_" -> return $ A.VarP $ mkBindName n
           -- Andreas, 2017-09-03: TODO for #2580
           -- Patterns @VarP "()"@ should have been replaced by @AbsurdP@, but the
           -- case splitter still produces them.
         | prettyShow (nameConcrete n) == "()" -> return $ A.VarP (mkBindName n)
           -- Andreas, 2017-09-03, issue #2729
           -- Restore original pattern name.  AbstractToConcrete picks unique names.
         | otherwise -> return $ A.VarP $
             mkBindName n { nameConcrete = C.simpleName y }

    reifyDotP :: MonadReify m => PatOrigin -> Term -> m A.Pattern
    reifyDotP o v = do
      keepVars <- optKeepPatternVariables <$> pragmaOptions
      if | PatOVar x <- o , keepVars       -> return $ A.VarP $ mkBindName x
         | otherwise                       -> A.DotP patNoRange <$> reify v

    reifyConP :: MonadReify m
              => ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern]
              -> m A.Pattern
    reifyConP c cpi ps = do
      tryRecPFromConP =<< do A.ConP ci (unambiguous (conName c)) <$> reifyPatterns ps
      where
        ci = ConPatInfo origin patNoRange lazy
        lazy | conPLazy cpi = ConPatLazy
             | otherwise    = ConPatEager
        origin = fromConPatternInfo cpi

    addAsBindings :: Functor m => [A.Name] -> m A.Pattern -> m A.Pattern
    addAsBindings xs p = foldr (fmap . AsP patNoRange . mkBindName) p xs


-- | If the record constructor is generated or the user wrote a record pattern,
--   turn constructor pattern into record pattern.
--   Otherwise, keep constructor pattern.
tryRecPFromConP :: MonadReify m => A.Pattern -> m A.Pattern
tryRecPFromConP p = do
  let fallback = return p
  case p of
    A.ConP ci c ps -> do
        reportSLn "reify.pat" 60 $ "tryRecPFromConP " ++ prettyShow c
        caseMaybeM (isRecordConstructor $ headAmbQ c) fallback $ \ (r, def) -> do
          -- If the record constructor is generated or the user wrote a record pattern,
          -- print record pattern.
          -- Otherwise, print constructor pattern.
          if recNamedCon def && conPatOrigin ci /= ConORec then fallback else do
            fs <- fromMaybe __IMPOSSIBLE__ <$> getRecordFieldNames_ r
            unless (length fs == length ps) __IMPOSSIBLE__
            return $ A.RecP patNoRange $ zipWith mkFA fs ps
        where
          mkFA ax nap = FieldAssignment (unDom ax) (namedArg nap)
    _ -> __IMPOSSIBLE__

-- | If the record constructor is generated or the user wrote a record expression,
--   turn constructor expression into record expression.
--   Otherwise, keep constructor expression.
recOrCon :: MonadReify m => QName -> ConOrigin -> [Arg Expr] -> m A.Expr
recOrCon c co es = do
  reportSLn "reify.expr" 60 $ "recOrCon " ++ prettyShow c
  caseMaybeM (isRecordConstructor c) fallback $ \ (r, def) -> do
    -- If the record constructor is generated or the user wrote a record expression,
    -- print record expression.
    -- Otherwise, print constructor expression.
    if recNamedCon def && co /= ConORec then fallback else do
      fs <- fromMaybe __IMPOSSIBLE__ <$> getRecordFieldNames_ r
      unless (length fs == length es) __IMPOSSIBLE__
      return $ A.Rec empty $ zipWith mkFA fs es
  where
  fallback = apps (A.Con (unambiguous c)) es
  mkFA ax  = Left . FieldAssignment (unDom ax) . unArg

instance Reify (QNamed I.Clause) where
  type ReifiesTo (QNamed I.Clause) = A.Clause

  reify (QNamed f cl) = reify (NamedClause f True cl)

instance Reify NamedClause where
  type ReifiesTo NamedClause = A.Clause

  reify (NamedClause f toDrop cl) = addContext (clauseTel cl) $ do
    reportSDoc "reify.clause" 60 $ return $ vcat
      [ "reifying NamedClause"
      , "  f      =" <+> pretty f
      , "  toDrop =" <+> pshow toDrop
      , "  cl     =" <+> pretty cl
      ]

    let clBody = clauseBody cl
        rhsVars = maybe [] freeVars clBody

    rhsBody     <- traverse reify clBody
    rhsVarNames <- mapM nameOfBV' rhsVars
    let rhsUsedNames = maybe mempty allUsedNames rhsBody
        rhsUsedVars  = [i | (i, Just n) <- zip rhsVars rhsVarNames, n `Set.member` rhsUsedNames]

    reportSDoc "reify.clause" 60 $ return $ "RHS:" <+> pretty clBody
    reportSDoc "reify.clause" 60 $ return $ "variables occurring on RHS:" <+> pretty rhsVars
      <+> "variable names:" <+> pretty rhsVarNames
      <+> parens (maybe "no clause body" (const "there was a clause body") clBody)
    reportSDoc "reify.clause" 60 $ return $ "names occurring on RHS" <+> pretty (Set.toList rhsUsedNames)

    let ell = clauseEllipsis cl
    ps  <- reifyPatterns $ namedClausePats cl
    lhs <- uncurry (SpineLHS $ empty { lhsEllipsis = ell }) <$> reifyDisplayFormP f ps []
    -- Unless @toDrop@ we have already dropped the module patterns from the clauses
    -- (e.g. for extended lambdas). We still get here with toDrop = True and
    -- pattern lambdas when doing make-case, so take care to drop the right
    -- number of parameters.
    (params , lhs) <- if not toDrop then return ([] , lhs) else do
      nfv <- getDefModule f >>= \case
        Left _  -> return 0
        Right m -> size <$> lookupSection m
      return $ splitParams nfv lhs
    lhs <- stripImps rhsUsedNames params lhs
    let rhs    = caseMaybe rhsBody AbsurdRHS $ \ e -> RHS e Nothing
        result = A.Clause (spineToLhs lhs) [] rhs A.noWhereDecls (I.clauseCatchall cl)
    return result
    where
      splitParams n (SpineLHS i f ps) =
        let (params , pats) = splitAt n ps
        in  (params , SpineLHS i f pats)
      stripImps :: MonadReify m => Set Name -> [NamedArg A.Pattern] -> SpineLHS -> m SpineLHS
      stripImps rhsUsedNames params (SpineLHS i f ps) =  SpineLHS i f <$> stripImplicits rhsUsedNames params ps

instance Reify (QNamed System) where
  type ReifiesTo (QNamed System) = [A.Clause]

  reify (QNamed f (System tel sys)) = addContext tel $ do
    reportS "reify.system" 40 $ show tel : map show sys
    view <- intervalView'
    unview <- intervalUnview'
    sys <- flip filterM sys $ \ (phi,t) -> do
      allM phi $ \ (u,b) -> do
        u <- reduce u
        return $ case (view u, b) of
          (IZero, True) -> False
          (IOne, False) -> False
          _ -> True
    forM sys $ \ (alpha,u) -> do
      rhs <- RHS <$> reify u <*> pure Nothing
      ep <- fmap (A.EqualP patNoRange) . forM alpha $ \ (phi,b) -> do
        let
            d True = unview IOne
            d False = unview IZero
        reify (phi, d b)

      ps <- reifyPatterns $ teleNamedArgs tel
      ps <- stripImplicits mempty [] $ ps ++ [defaultNamedArg ep]
      let
        lhs = SpineLHS empty f ps
        result = A.Clause (spineToLhs lhs) [] rhs A.noWhereDecls False
      return result

instance Reify I.Type where
    type ReifiesTo I.Type = A.Type

    reifyWhen = reifyWhenE
    reify (I.El _ t) = reify t

instance Reify Sort where
    type ReifiesTo Sort = Expr

    reifyWhen = reifyWhenE
    reify s = do
      s <- instantiateFull s
      SortKit{..} <- infallibleSortKit
      case s of
        I.Univ u (I.ClosedLevel 0) -> return $ A.Def' (nameOfUniv USmall u) A.NoSuffix
        I.Univ u (I.ClosedLevel n) -> return $ A.Def' (nameOfUniv USmall u) (A.Suffix n)
        I.Univ u a -> do
          a <- reify a
          return $ A.App defaultAppInfo_ (A.Def $ nameOfUniv USmall u) (defaultNamedArg a)
        I.Inf u 0 -> return $ A.Def' (nameOfUniv ULarge u) A.NoSuffix
        I.Inf u n -> return $ A.Def' (nameOfUniv ULarge u) (A.Suffix n)
        I.SizeUniv  -> do
          I.Def sizeU [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSizeUniv
          return $ A.Def sizeU
        I.LockUniv  -> do
          lockU <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinLockUniv
          return $ A.Def lockU
        I.LevelUniv -> do
          levelU <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinLevelUniv
          return $ A.Def levelU
        I.IntervalUniv -> do
          intervalU <- fromMaybe __IMPOSSIBLE__ <$> getName' builtinIntervalUniv
          return $ A.Def intervalU
        I.PiSort a s1 s2 -> do
          pis <- freshName_ ("piSort" :: String) -- TODO: hack
          (e1,e2) <- reify (s1, I.Lam defaultArgInfo $ fmap Sort s2)
          let app x y = A.App defaultAppInfo_ x (defaultNamedArg y)
          return $ A.Var pis `app` e1 `app` e2
        I.FunSort s1 s2 -> do
          funs <- freshName_ ("funSort" :: String) -- TODO: hack
          (e1,e2) <- reify (s1 , s2)
          let app x y = A.App defaultAppInfo_ x (defaultNamedArg y)
          return $ A.Var funs `app` e1 `app` e2
        I.UnivSort s -> do
          univs <- freshName_ ("univSort" :: String) -- TODO: hack
          e <- reify s
          return $ A.App defaultAppInfo_ (A.Var univs) $ defaultNamedArg e
        I.MetaS x es -> reify $ I.MetaV x es
        I.DefS d es -> reify $ I.Def d es
        I.DummyS s -> return $ A.Lit empty $ LitString $ T.pack s

instance Reify Level where
  type ReifiesTo Level = Expr

  reifyWhen = reifyWhenE
  reify l   = ifM haveLevels (reify =<< reallyUnLevelView l) $ {-else-} do
    -- Andreas, 2017-09-18, issue #2754
    -- While type checking the level builtins, they are not
    -- available for debug printing.  Thus, print some garbage instead.
    name <- freshName_ (".#Lacking_Level_Builtins#" :: String)
    return $ A.Var name

instance (Free i, Reify i) => Reify (Abs i) where
  type ReifiesTo (Abs i) = (Name, ReifiesTo i)

  reify (NoAbs x v) = freshName_ x >>= \name -> (name,) <$> reify v
  reify (Abs s v) = do

    -- If the bound variable is free in the body, then the name "_" is
    -- replaced by "z".
    s <- return $ if isUnderscore s && 0 `freeIn` v then "z" else s

    x <- C.setNotInScope <$> freshName_ s
    e <- addContext x -- type doesn't matter
         $ reify v
    return (x,e)

instance Reify I.Telescope where
  type ReifiesTo I.Telescope = A.Telescope

  reify EmptyTel = return []
  reify (ExtendTel arg tel) = do
    Arg info e <- reify arg
    (x, bs)  <- reify tel
    let r    = getRange e
        name = domName arg
    tac <- traverse (Ranged noRange <.> reify) $ domTactic arg
    let xs = singleton $ Arg info $ Named name $ A.mkBinder_ x
    return $ TBind r (TypedBindingInfo tac (domIsFinite arg)) xs e : bs

instance Reify i => Reify (Dom i) where
    type ReifiesTo (Dom i) = Arg (ReifiesTo i)

    reify (Dom{domInfo = info, unDom = i}) = Arg info <$> reify i

instance Reify i => Reify (I.Elim' i)  where
  type ReifiesTo (I.Elim' i) = I.Elim' (ReifiesTo i)

  reify = traverse reify
  reifyWhen b = traverse (reifyWhen b)

instance Reify i => Reify [i] where
  type ReifiesTo [i] = [ReifiesTo i]

  reify = traverse reify
  reifyWhen b = traverse (reifyWhen b)

instance (Reify i1, Reify i2) => Reify (i1, i2) where
    type ReifiesTo (i1, i2) = (ReifiesTo i1, ReifiesTo i2)
    reify (x,y) = (,) <$> reify x <*> reify y

instance (Reify i1, Reify i2, Reify i3) => Reify (i1,i2,i3) where
    type ReifiesTo (i1, i2, i3) = (ReifiesTo i1, ReifiesTo i2, ReifiesTo i3)
    reify (x,y,z) = (,,) <$> reify x <*> reify y <*> reify z

instance (Reify i1, Reify i2, Reify i3, Reify i4) => Reify (i1,i2,i3,i4) where
    type ReifiesTo (i1, i2, i3, i4) = (ReifiesTo i1, ReifiesTo i2, ReifiesTo i3, ReifiesTo i4)
    reify (x,y,z,w) = (,,,) <$> reify x <*> reify y <*> reify z <*> reify w
