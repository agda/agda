
-- | Code which replaces pattern matching on record constructors with
-- uses of projection functions.

module Agda.TypeChecking.RecordPatterns
  ( translateCompiledClauses
  , translateSplitTree
  , recordPatternToProjections
  , recordRHSToCopatterns
  ) where

import Control.Arrow          ( first, second )
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.Reader   ( MonadReader(..), ReaderT(..), runReaderT )
import Control.Monad.State    ( MonadState(..), StateT(..), runStateT )

import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map

import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common.Pretty (Pretty(..), prettyShow)
import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Permutation hiding (dropFrom)
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Update (MonadChange, tellDirty)

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Record pattern translation for let bindings
---------------------------------------------------------------------------

-- | Take a record pattern @p@ and yield a list of projections
--   corresponding to the pattern variables, from left to right.
--
--   E.g. for @(x , (y , z))@ we return @[ fst, fst . snd, snd . snd ]@.
--
--   If it is not a record pattern, error 'ShouldBeRecordPattern' is raised.
recordPatternToProjections :: DeBruijnPattern -> TCM [Term -> Term]
recordPatternToProjections p =
  case p of
    VarP{}       -> return [ id ]
    LitP{}       -> typeError $ ShouldBeRecordPattern p
    DotP{}       -> typeError $ ShouldBeRecordPattern p
    ConP c ci ps -> do
      unless (conPRecord ci) $
        typeError $ ShouldBeRecordPattern p
      let t = unArg $ fromMaybe __IMPOSSIBLE__ $ conPType ci
      reportSDoc "tc.rec" 45 $ vcat
        [ "recordPatternToProjections: "
        , nest 2 $ "constructor pattern " <+> prettyTCM p <+> " has type " <+> prettyTCM t
        ]
      reportSLn "tc.rec" 70 $ "  type raw: " ++ show t
      fields <- getRecordTypeFields t
      concat <$> zipWithM comb (map proj fields) (map namedArg ps)
    ProjP{}      -> __IMPOSSIBLE__ -- copattern cannot appear here
    IApplyP{}    -> typeError $ ShouldBeRecordPattern p
    DefP{}       -> typeError $ ShouldBeRecordPattern p
  where
    proj p = (`applyE` [Proj ProjSystem $ unDom p])
    comb :: (Term -> Term) -> DeBruijnPattern -> TCM [Term -> Term]
    comb prj p = map (\ f -> f . prj) <$> recordPatternToProjections p


---------------------------------------------------------------------------
-- * Record pattern translation for compiled clauses
---------------------------------------------------------------------------

-- | Take a matrix of booleans (at least one row!) and summarize the columns
--   using conjunction.
conjColumns :: [[Bool]] -> [Bool]
conjColumns =  foldl1 (zipWith (&&))

-- UNUSED Liang-Ting 2019-07-16
---- | @insertColumn i a m@ inserts a column before the @i@th column in
----   matrix @m@ and fills it with value @a@.
--insertColumn :: Int -> a -> [[a]] -> [[a]]
--insertColumn i a rows = map ins rows where
--  ins row = let (init, last) = splitAt i row in init ++ a : last

{- UNUSED
-- | @cutColumn i m@ removes the @i@th column from matrix @m@.
cutColumn :: Int -> [[a]] -> [[a]]
cutColumn i rows = map cut rows where
  cut row = let (init, _:last) = splitAt i row in init ++ last

-- | @cutColumns i n xss = (yss, xss')@ cuts out a submatrix @yss@
--   of width @n@ from @xss@, starting at column @i@.
cutColumns :: Int -> Int -> [[a]] -> ([[a]], [[a]])
cutColumns i n rows = unzip (map (cutSublist i n) rows)
-}

-- UNUSED Liang-Ting 2019-07-16
---- | @cutSublist i n xs = (xs', ys, xs'')@ cuts out a sublist @ys@
----   of width @n@ from @xs@, starting at column @i@.
--cutSublist :: Int -> Int -> [a] -> ([a], [a], [a])
--cutSublist i n row =
--  let (init, rest) = splitAt i row
--      (mid , last) = splitAt n rest
--  in  (init, mid, last)

getEtaAndArity :: SplitTag -> TCM (Bool, Nat)
getEtaAndArity (SplitCon c) =
  getConstructorInfo c <&> \case
    DataCon n           -> (False, n)
    RecordCon _ eta n _ -> (eta == YesEta, n)
getEtaAndArity (SplitLit l) = return (False, 0)
getEtaAndArity SplitCatchall = return (False, 1)

translateCompiledClauses
  :: forall m. (HasConstInfo m, MonadChange m)
  => CompiledClauses -> m CompiledClauses
translateCompiledClauses cc = ignoreAbstractMode $ do
  reportSDoc "tc.cc.record" 20 $ vcat
    [ "translate record patterns in compiled clauses"
    , nest 2 $ return $ pretty cc
    ]
  cc <- loop cc
  reportSDoc "tc.cc.record" 20 $ vcat
    [ "translated compiled clauses (no eta record patterns):"
    , nest 2 $ return $ pretty cc
    ]
  cc <- recordExpressionsToCopatterns cc
  reportSDoc "tc.cc.record" 20 $ vcat
    [ "translated compiled clauses (record expressions to copatterns):"
    , nest 2 $ return $ pretty cc
    ]
  return cc
  where

    loop :: CompiledClauses -> m (CompiledClauses)
    loop cc = case cc of
      Fail{}    -> return cc
      Done{}    -> return cc
      Case i cs -> loops i cs

    loops :: Arg Int               -- split variable
          -> Case CompiledClauses  -- original split tree
          -> m CompiledClauses
    loops i cs@Branches{ projPatterns   = comatch
                       , conBranches    = conMap
                       , etaBranch      = eta
                       , litBranches    = litMap
                       , fallThrough    = fT
                       , catchAllBranch = catchAll
                       , lazyMatch      = lazy } = do

      catchAll <- traverse loop catchAll
      litMap   <- traverse loop litMap
      (conMap, eta) <- do
        let noEtaCase = (, Nothing) <$> (traverse . traverse) loop conMap
            yesEtaCase b ch = (Map.empty,) . Just . (ch,) <$> traverse loop b
        case Map.toList conMap of
              -- This is already an eta match. Still need to recurse though.
              -- This can happen (#2981) when we
              -- 'revisitRecordPatternTranslation' in Rules.Decl, due to
              -- inferred eta.
          _ | Just (ch, b) <- eta -> yesEtaCase b ch
          [(c, b)] | not comatch -> -- possible eta-match
            getConstructorInfo' c >>= \ case
              Just (RecordCon pm YesEta _ar fs) -> yesEtaCase b $
                ConHead c (IsRecord pm) Inductive (map argFromDom fs)
              _ -> noEtaCase
          _ -> noEtaCase
      return $ Case i cs{ conBranches    = conMap
                        , etaBranch      = eta
                        , litBranches    = litMap
                        , fallThrough    = fT
                        , catchAllBranch = catchAll
                        }


-- | Transform definitions returning record values to use copatterns instead.
--   This allows e.g. termination-checking constructor-style coinduction.
--
--   For example:
--
--   @
--     nats : Nat → Stream Nat
--     nats n = n ∷ nats (1 + n)
--   @
--
--   The clause is translated to:
--
--   @
--     nats n .head = n
--     nats n .tail = nats (1 + n)
--   @
--
--   A change is signalled if definitional equalities might not hold after the
--   translation, e.g. if a non-eta constructor was turned to copattern matching.
recordRHSsToCopatterns ::
     forall m. (MonadChange m, PureTCM m)
  => [Clause]
  -> m [Clause]
recordRHSsToCopatterns cls = do
  reportSLn "tc.inline.con" 40 $ "enter recordRHSsToCopatterns with " ++ show (length cls) ++ " clauses"
  concatMapM recordRHSToCopatterns cls

recordRHSToCopatterns ::
     forall m. (MonadChange m, PureTCM m)
  => Clause
  -> m [Clause]
recordRHSToCopatterns cl = do
  reportSLn "tc.inline.con" 40 $ "enter recordRHSToCopatterns"

  case cl of

    -- RHS must be fully applied coinductive constructor/record expression.
    cl@Clause{ namedClausePats = ps
             , clauseBody      = Just v0@(Con con@(ConHead c _ _ind fs) _ci es)
             , clauseType      = mt
             }
      | not (null fs)           -- at least one field
      , length fs == length es  -- fully applied
      , Just vs <- allApplyElims es

          -- Only expand constructors labelled @{-# INLINE c #-}@.
      -> inlineConstructor c >>= \case
        Nothing  -> return [cl]
        Just eta -> do

          mt <- traverse reduce mt

          -- If it may change definitional equality,
          -- announce that the translation actually fired.
          unless eta tellDirty

          -- Iterate the translation for nested constructor rhss.
          recordRHSsToCopatterns =<< do

            -- Create one clause per projection.
            forM (zip fs vs) $ \ (f, v) -> do

              -- Get the type of the field.
              let inst :: Type -> m (Maybe Type)
                  inst t = fmap thd3 <$> projectTyped v0 t ProjSystem (unArg f)

              let fuse :: Maybe (Arg (Maybe a)) -> Maybe (Arg a)
                  fuse = join . fmap distributeF

              mt' :: Maybe (Arg Type) <- fuse <$> traverse (traverse inst) mt

              -- Make clause ... .f = v
              return cl
                { namedClausePats = ps ++ [ unnamed . ProjP ProjSystem <$> f ]
                , clauseBody      = Just $ unArg v
                , clauseType      = mt'
                }

    -- Otherwise: no change.
    cl -> return [cl]

  where
    -- @Nothing@ means do not inline, @Just eta@ means inline.
    inlineConstructor :: QName -> m (Maybe Bool)
    inlineConstructor c = getConstInfo c <&> theDef >>= \case
      Constructor { conData, conInline } -> do
        reportSLn "tc.inline.con" 80 $
          ("can" ++) $ applyUnless conInline ("not" ++) $ " inline constructor " ++ prettyShow c
        if not conInline then return Nothing else Just <$> isEtaRecord conData
      _ -> return Nothing

-- | Transform definitions returning record expressions to use copatterns
--   instead. This prevents terms from blowing up when reduced.
recordExpressionsToCopatterns
  :: (HasConstInfo m, MonadChange m)
  => CompiledClauses
  -> m CompiledClauses
recordExpressionsToCopatterns = \case
    Case i bs -> Case i <$> traverse recordExpressionsToCopatterns bs
    cc@Fail{} -> return cc
    cc@(Done xs (Con c co es))
      | elem co [ConORec, ConORecWhere] -> do  -- don't translate if using the record /constructor/
      let vs = map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      irrProj <- optIrrelevantProjections <$> pragmaOptions
      getConstructorInfo (conName c) >>= \ case
        RecordCon CopatternMatching YesEta ar fs
          | ar > 0                                     -- only for eta-records with at least one field
          , length vs == ar                            -- where the constructor application is saturated
          , irrProj || not (any isIrrelevant fs) -> do -- and irrelevant projections (if any) are allowed
              tellDirty
              Case (defaultArg $ length xs) <$> do
                -- translate new cases recursively (there might be nested record expressions)
                traverse recordExpressionsToCopatterns $ Branches
                  { projPatterns   = True
                  , conBranches    = Map.fromListWith __IMPOSSIBLE__ $
                      zipWith (\ f v -> (unDom f, WithArity 0 $ Done xs v)) fs vs
                  , etaBranch      = Nothing
                  , litBranches    = Map.empty
                  , catchAllBranch = Nothing
                  , fallThrough    = Nothing
                  , lazyMatch      = False
                  }
        _ -> return cc
    cc@Done{} -> return cc

---------------------------------------------------------------------------
-- * Record pattern translation for split trees
---------------------------------------------------------------------------

-- | Bottom-up procedure to record-pattern-translate split tree.
translateSplitTree :: SplitTree -> TCM SplitTree
translateSplitTree = snd <.> loop
  where

    -- @loop t = return (xs, t')@ returns the translated split tree @t'@
    -- plus the status @xs@ of the clause variables
    --   True  = variable will never be split on in @t'@ (virgin variable)
    --   False = variable will be spilt on in @t'@
    loop :: SplitTree -> TCM ([Bool], SplitTree)
    loop = \case
      SplittingDone n ->
        -- start with n virgin variables
        return (replicate n True, SplittingDone n)
      SplitAt i lz ts    -> do
        (x, xs, ts) <- loops (unArg i) ts
        -- if we case on record constructor, drop case
        let t' = if x then
                   case ts of
                     [(c,t)] -> t
                     _       -> __IMPOSSIBLE__
                  -- else retain case
                  else SplitAt i lz ts
        return (xs, t')

    -- @loops i ts = return (x, xs, ts')@ cf. @loop@
    -- @x@ says wether at arg @i@ we have a record pattern split
    -- that can be removed
    loops :: Int -> SplitTrees -> TCM (Bool, [Bool], SplitTrees)
    loops i ts = do
      -- note: ts not empty
      (rs, xss, ts) <- unzip3 <$> do
        forM ts $ \ (c, t) -> do
          (xs, t) <- loop t
          (isRC, n) <- getEtaAndArity c
          -- now drop variables from i to i+n-1
          let (xs0, rest) = splitAt i xs
              (xs1, xs2)  = splitAt n rest
              -- if all dropped variables are virgins and we are record cons.
              -- then new variable x is also virgin
              -- and we can translate away the split
              x           = isRC && and xs1
              -- xs' = updated variables
              xs'         = xs0 ++ x : xs2
              -- delete splits from t if record match
              t'          = if x then dropFrom i (n - 1) t else t
          return (x, xs', (c, t'))
      -- x = did we split on a record constructor?
      let x = and rs
      -- invariant: if record constructor, then exactly one constructor
      if x then unless (rs == [True]) __IMPOSSIBLE__
      -- else no record constructor
       else when (or rs) __IMPOSSIBLE__
      return (x, conjColumns xss, ts)

-- | @dropFrom i n@ drops arguments @j@  with @j < i + n@ and @j >= i@.
--   NOTE: @n@ can be negative, in which case arguments are inserted.
class DropFrom a where
  dropFrom :: Int -> Int -> a -> a

instance DropFrom (SplitTree' c) where
  dropFrom i n = \case
    SplittingDone m -> SplittingDone (m - n)
    SplitAt x@(Arg ai j) lz ts
      | j >= i + n -> SplitAt (Arg ai $ j - n) lz $ dropFrom i n ts
      | j < i      -> SplitAt x lz $ dropFrom i n ts
      | otherwise  -> __IMPOSSIBLE__

instance DropFrom (c, SplitTree' c) where
  dropFrom i n (c, t) = (c, dropFrom i n t)

instance DropFrom a => DropFrom [a] where
  dropFrom i n ts = map (dropFrom i n) ts
