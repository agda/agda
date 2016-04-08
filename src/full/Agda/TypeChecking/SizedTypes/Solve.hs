{-# LANGUAGE CPP                   #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

-- | Solving size constraints under hypotheses.
--
-- The size solver proceeds as follows:
--
-- 1. Get size constraints, cluster into connected components.
--
--    All size constraints that mention the same metas go into the same
--    cluster.  Each cluster can be solved by itself.
--
--    Constraints that do not fit our format are ignored.
--    We check whether our computed solution fulfills them as well
--    in the last step.
--
-- 2. Find a joint context for each cluster.
--
--    Each constraint comes with its own typing context, which
--    contains size hypotheses @j : Size< i@.  We need to find a
--    common super context in which all constraints of a cluster live,
--    and raise all constraints to this context.
--
--    There might not be a common super context.  Then we are screwed,
--    since our solver is not ready to deal with such a situation.  We
--    will blatantly refuse to solve this cluster and blame it on the
--    user.
--
-- 3. Convert the joint context into a hypothesis graph.
--
--    This is straightforward.  Each de Bruijn index becomes a
--    rigid variable, each typing assumption @j : Size< i@ becomes an
--    arc.
--
-- 4. Convert the constraints into a constraint graph.
--
--    Here we need to convert @MetaV@s into flexible variables.
--
-- 5. Run the solver
--
-- 6. Convert the solution into meta instantiations.
--
-- 7. Double-check whether the constraints are solved.

-- Opportunities for optimization:
--
-- - NamedRigids has some cost to retrieve variable names
--   just for the sake of debug printing.

module Agda.TypeChecking.SizedTypes.Solve where

import Control.Monad (unless)
import Data.Foldable (Foldable, foldMap, forM_)
import Data.Function
import Data.List
import Data.Monoid (mappend)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (Traversable, forM)

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad as TCM hiding (Offset)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.MetaVars
-- import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints as C
-- import {-# SOURCE #-} Agda.TypeChecking.Conversion
-- import {-# SOURCE #-} Agda.TypeChecking.Constraints

import qualified Agda.TypeChecking.SizedTypes as S
import Agda.TypeChecking.SizedTypes.Syntax as Size
import Agda.TypeChecking.SizedTypes.Utils
import Agda.TypeChecking.SizedTypes.WarshallSolver as Size

import Agda.Utils.Cluster
import Agda.Utils.Either
import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Function
import Agda.Utils.Functor

#if MIN_VERSION_base(4,8,0)
import Agda.Utils.List hiding ( uncons )
#else
import Agda.Utils.List
#endif

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | Flag to control the behavior of size solver.
data DefaultToInfty
  = DefaultToInfty      -- ^ Instantiate all unconstrained size variables to ∞.
  | DontDefaultToInfty  -- ^ Leave unconstrained size variables unsolved.
  deriving (Eq, Ord, Show)

-- | Solve size constraints involving hypotheses.
solveSizeConstraints :: DefaultToInfty -> TCM ()
solveSizeConstraints flag =  do
  -- Get the constraints.
  cs0 <- S.getSizeConstraints
  let -- Error for giving up
      cannotSolve = typeError . GenericDocError =<<
        vcat (text "Cannot solve size constraints" : map prettyTCM
                   cs0)
  unless (null cs0) $ solveSizeConstraints_ cs0

  -- Andreas, issue 1862: do not default to ∞ always, could be too early.
  when (flag == DefaultToInfty) $ do

  -- Set the unconstrained size metas to ∞.
  ms <- S.getSizeMetas False -- do not get interaction metas
  unless (null ms) $ do
    inf <- primSizeInf
    forM_ ms $ \ (m, t, tel) -> do
      reportSDoc "tc.size.solve" 20 $
        text "solution " <+> prettyTCM (MetaV m []) <+>
        text " := "      <+> prettyTCM inf
      assignMeta 0 m t (downFrom $ size tel) inf

  -- Double check.
  unless (null cs0 && null ms) $ do
    flip catchError (const cannotSolve) $
      noConstraints $
        forM_ cs0 $ \ cl -> enterClosure cl solveConstraint

solveSizeConstraints_ :: [Closure TCM.Constraint] -> TCM ()
solveSizeConstraints_ cs0 = do
  -- Pair constraints with their representation as size constraints.
  -- Discard constraints that do not have such a representation.
  ccs <- catMaybes <$> do
    forM cs0 $ \ c -> fmap (c,) <$> computeSizeConstraint c

  -- Simplify constraints and check for obvious inconsistencies.
  cs <- concat <$> do
    forM ccs $ \ (c, HypSizeConstraint cxt hids hs sc) -> do
      case simplify1 (\ c -> return [c]) sc of
        Left _ -> typeError . GenericDocError =<< do
          text "Contradictory size constraint" <+> prettyTCM c
        Right cs -> return $ HypSizeConstraint cxt hids hs <$> cs

  -- Cluster constraints according to the meta variables they mention.
  -- @csNoM@ are the constraints that do not mention any meta.
  let (csNoM, csMs) = (`partitionMaybe` cs) $ \ c ->
        fmap (c,) $ uncons $ map (metaId . sizeMetaId) $ Set.toList $ flexs c
  -- @css@ are the clusters of constraints.
      css = cluster' csMs
  -- There should be no constraints that do not mention a meta?
  unless (null csNoM) __IMPOSSIBLE__

  -- Now, process the clusters.
  forM_ css solveCluster

solveCluster :: [HypSizeConstraint] -> TCM ()
solveCluster [] = __IMPOSSIBLE__
solveCluster cs = do
  let err reason = typeError . GenericDocError =<< do
        vcat $
          [ text $ "Cannot solve size constraints" ] ++ map prettyTCM cs ++
          [ text $ "Reason: " ++ reason ]
  reportSDoc "tc.size.solve" 20 $ vcat $
    [ text "Solving constraint cluster" ] ++ map prettyTCM cs
  -- Find the super context of all contexts.
{-
  -- We use the @'ctxId'@s.
  let cis@(ci:cis') = for cs $ \ c -> (c, reverse $ map ctxId $ sizeContext c)
--  let cis@(ci:cis') = for cs $ \ c -> (c, reverse $ sizeHypIds c)
      max a@Left{}            _            = a
      max a@(Right ci@(c,is)) ci'@(c',is') =
        case preOrSuffix is is' of
          -- No common context:
          IsNofix    -> Left (ci, ci')
          IsPrefix{} -> Right ci'
          _          -> a
      res = foldl' max (Right ci) cis'
      noContext ((c,is),(c',is')) = typeError . GenericDocError =<< vcat
        [ text "Cannot solve size constraints; the following constraints have no common typing context:"
        , prettyTCM c
        , prettyTCM c'
        ]
  flip (either noContext) res $ \ (HypSizeConstraint gamma hids hs _, _) -> do
-}
  -- We rely on the fact that contexts are only extended...
  -- Just take the longest context.
  let HypSizeConstraint gamma hids hs _ = maximumBy (compare `on` (length . sizeContext)) cs
  -- Length of longest context.
  let n = size gamma

  -- Now convert all size constraints to the largest context.
      csL = for cs $ \ (HypSizeConstraint cxt _ _ c) -> raise (n - size cxt) c
  -- Canonicalize the constraints.
  -- This is unsound in the presence of hypotheses.
      csC :: [SizeConstraint]
      csC = applyWhen (null hs) (mapMaybe canonicalizeSizeConstraint) csL
  reportSDoc "tc.size.solve" 30 $ vcat $
    [ text "Size hypotheses" ] ++
    map (prettyTCM . HypSizeConstraint gamma hids hs) hs ++
    [ text "Canonicalized constraints" ] ++
    map (prettyTCM . HypSizeConstraint gamma hids hs) csC

  -- -- ALT:
  -- -- Now convert all size constraints to de Bruijn levels.

  -- -- To get from indices in a context of length m <= n
  -- -- to levels into the target context of length n,
  -- -- we apply the following substitution:
  -- -- Index m-1 needs to be mapped to level 0,
  -- -- index m-2 needs to be mapped to level 1,
  -- -- index 0 needs to be mapped to level m-1,
  -- -- so the desired substitution is @downFrom m@.
  -- let sub m = applySubst $ parallelS $ map var $ downFrom m

  -- -- We simply reverse the context to get to de Bruijn levels.
  -- -- Of course, all types in the context are broken, but
  -- -- only need it for pretty printing constraints.
  -- gamma <- return $ reverse gamma

  -- -- We convert the hypotheses to de Bruijn levels.
  -- hs <- return $ sub n hs

  -- -- We get a form for pretty-printing
  -- let prettyC = prettyTCM . HypSizeConstraint gamma hids hs

  -- -- We convert the constraints to de Bruijn level format.
  -- let csC :: [SizeConstraint]
  --     csC = for cs $ \ (HypSizeConstraint cxt _ _ c) -> sub (size cxt) c

  -- reportSDoc "tc.size.solve" 30 $ vcat $
  --   [ text "Size hypotheses" ]           ++ map prettyC hs ++
  --   [ text "Canonicalized constraints" ] ++ map prettyC csC

  -- Convert size metas to flexible vars.
  let metas :: [SizeMeta]
      metas = concat $ map (foldMap (:[])) csC
      csF   :: [Size.Constraint' NamedRigid Int]
      csF   = map (fmap (metaId . sizeMetaId)) csC

  -- Construct the hypotheses graph.
  let hyps = map (fmap (metaId . sizeMetaId)) hs
  -- There cannot be negative cycles in hypotheses graph due to scoping.
  let hg = fromRight __IMPOSSIBLE__ $ hypGraph (rigids csF) hyps

  -- Construct the constraint graph.
  --    g :: Size.Graph NamedRigid Int Label
  g <- either err return $ constraintGraph csF hg
  reportSDoc "tc.size.solve" 40 $ vcat $
    [ text "Constraint graph"
    , text (show g)
    ]

  sol :: Solution NamedRigid Int <- either err return $ solveGraph Map.empty hg g
  either err return $ verifySolution hg csF sol
  -- Convert solution to meta instantiation.
  forM_ (Map.assocs sol) $ \ (m, a) -> do
    unless (validOffset a) __IMPOSSIBLE__
    -- Solution does not contain metas
    u <- unSizeExpr $ fmap __IMPOSSIBLE__ a
    let x = MetaId m
    let SizeMeta _ xs = fromMaybe __IMPOSSIBLE__ $ find ((m==) . metaId . sizeMetaId) metas
    -- Check that solution is well-scoped
    let ys = rigidIndex <$> Set.toList (rigids a)
        ok = all (`elem` xs) ys -- TODO: more efficient
    -- unless ok $ err "ill-scoped solution for size meta variable"
    u <- if ok then return u else primSizeInf
    t <- getMetaType x
    reportSDoc "tc.size.solve" 20 $ inTopContext $ modifyContext (const gamma) $ do
      text "solution " <+> prettyTCM (MetaV x []) <+> text " := " <+> prettyTCM u
    assignMeta n x t xs u



-- | Collect constraints from a typing context, looking for SIZELT hypotheses.
getSizeHypotheses :: Context -> TCM [(CtxId, SizeConstraint)]
getSizeHypotheses gamma = inTopContext $ modifyContext (const gamma) $ do
  (_, msizelt) <- getBuiltinSize
  caseMaybe msizelt (return []) $ \ sizelt -> do
    -- Traverse the context from newest to oldest de Bruijn Index
    catMaybes <$> do
      forM (zip [0..] gamma) $ \ (i, ce) -> do
        -- Get name and type of variable i.
        let xt = unDom $ ctxEntry ce
            x  = show $ fst xt
        t <- reduce . raise (1 + i) . unEl . snd $ xt
        case ignoreSharing t of
          Def d [Apply u] | d == sizelt -> do
            caseMaybeM (sizeExpr $ unArg u) (return Nothing) $ \ a ->
              return $ Just $ (ctxId ce, Constraint (Rigid (NamedRigid x i) 0) Lt a)
          _ -> return Nothing

-- | Convert size constraint into form where each meta is applied
--   to indices @n-1,...,1,0@ where @n@ is the arity of that meta.
--
--   @X[σ] <= t@ becomes @X[id] <= t[σ^-1]@
--
--   @X[σ] ≤ Y[τ]@ becomes @X[id] ≤ Y[τ[σ^-1]]@ or @X[σ[τ^1]] ≤ Y[id]@
--   whichever is defined.  If none is defined, we give up.
--
--   Cf. @SizedTypes.oldCanonicalizeSizeConstraint@.
--
--   Fixes (the rather artificial) issue 300.
--   But it is unsound when pruned metas occur and triggers issue 1914.
--   Thus we deactivate it.
--   This needs to be properly implemented, possibly using the
--   metaPermuatation of each meta variable.

canonicalizeSizeConstraint :: SizeConstraint -> Maybe (SizeConstraint)
canonicalizeSizeConstraint c@(Constraint a cmp b) = Just c
{-
  case (a,b) of

    -- Case flex-flex
    (Flex (SizeMeta m xs) n, Flex (SizeMeta l ys) n')
         -- try to invert xs on ys
       | let len = size xs
       , Just ys' <- mapM (\ y -> (len-1 -) <$> findIndex (==y) xs) ys ->
           return $ Constraint (Flex (SizeMeta m $ downFrom len) n)
                           cmp (Flex (SizeMeta l ys') n')
         -- try to invert ys on xs
       | let len = size ys
       , Just xs' <- mapM (\ x -> (len-1 -) <$> findIndex (==x) ys) xs ->
           return $ Constraint (Flex (SizeMeta m xs') n)
                           cmp (Flex (SizeMeta l $ downFrom len) n')
         -- give up
       | otherwise -> Nothing

    -- Case flex-rigid
    (Flex (SizeMeta m xs) n, Rigid (NamedRigid x i) n') -> do
      let len = size xs
      j <- (len-1 -) <$> findIndex (==i) xs
      return $ Constraint (Flex (SizeMeta m $ downFrom len) n)
                      cmp (Rigid (NamedRigid x j) n')

    -- Case rigid-flex
    (Rigid (NamedRigid x i) n, Flex (SizeMeta m xs) n') -> do
      let len = size xs
      j <- (len-1 -) <$> findIndex (==i) xs
      return $ Constraint (Rigid (NamedRigid x j) n)
                      cmp (Flex (SizeMeta m $ downFrom len) n')

    -- Case flex-const
    (Flex (SizeMeta m xs) n, _)      ->
      return $ Constraint (Flex (SizeMeta m $ downFrom $ size xs) n) cmp b

    -- Case const-flex
    (_, Flex (SizeMeta m xs) n') -> do
      return $ Constraint a cmp (Flex (SizeMeta m $ downFrom $ size xs) n')

    -- Case no flex
    _ -> return c
-}

-- | Identifiers for rigid variables.
data NamedRigid = NamedRigid
  { rigidName  :: String   -- ^ Name for printing in debug messages.
  , rigidIndex :: Int      -- ^ De Bruijn index.
  }

instance Eq NamedRigid where (==) = (==) `on` rigidIndex
instance Ord NamedRigid where compare = compare `on` rigidIndex
instance Show NamedRigid where show = rigidName
instance Plus NamedRigid Int NamedRigid where
  plus (NamedRigid x i) j = NamedRigid x (i + j)

-- | Size metas in size expressions.
data SizeMeta = SizeMeta
  { sizeMetaId   :: MetaId
  -- TODO to fix issue 300?
  -- , sizeMetaPerm :: Permutation -- ^ Permutation from the current context
  --                               --   to the context of the meta.
  , sizeMetaArgs :: [Int]       -- ^ De Bruijn indices.
  }

-- | An equality which ignores the meta arguments.
instance Eq  SizeMeta where (==)    = (==)    `on` sizeMetaId
-- | An order which ignores the meta arguments.
instance Ord SizeMeta where compare = compare `on` sizeMetaId

instance Show SizeMeta where show = show . sizeMetaId

instance PrettyTCM SizeMeta where
  prettyTCM (SizeMeta x es) = prettyTCM (MetaV x $ map (Apply . defaultArg . var) es)

instance Subst Term SizeMeta where
  applySubst sigma (SizeMeta x es) = SizeMeta x (map raise es)
    where
      raise i =
        case lookupS sigma i of
          Var j [] -> j
          _        -> __IMPOSSIBLE__

-- | Size expression with de Bruijn indices.
type DBSizeExpr = SizeExpr' NamedRigid SizeMeta

-- deriving instance Functor     (SizeExpr' Int)
-- deriving instance Foldable    (SizeExpr' Int)
-- deriving instance Traversable (SizeExpr' Int)

-- | Only for 'raise'.
instance Subst Term (SizeExpr' NamedRigid SizeMeta) where
  applySubst sigma a =
    case a of
      Infty   -> a
      Const{} -> a
      Flex  x n -> Flex (applySubst sigma x) n
      Rigid r n ->
        case lookupS sigma $ rigidIndex r of
          Var j [] -> Rigid r{ rigidIndex = j } n
          _        -> __IMPOSSIBLE__

type SizeConstraint = Constraint' NamedRigid SizeMeta

instance Subst Term SizeConstraint where
  applySubst sigma (Constraint a cmp b) =
    Constraint (applySubst sigma a) cmp (applySubst sigma b)

-- | Assumes we are in the right context.
instance PrettyTCM (SizeConstraint) where
  prettyTCM (Constraint a cmp b) = do
    u <- unSizeExpr a
    v <- unSizeExpr b
    prettyTCM u <+> text (show cmp) <+> prettyTCM v

-- | Size constraint with de Bruijn indices.
data HypSizeConstraint = HypSizeConstraint
  { sizeContext    :: Context
  , sizeHypIds     :: [CtxId]
  , sizeHypotheses :: [SizeConstraint]  -- ^ Living in @Context@.
  , sizeConstraint :: SizeConstraint    -- ^ Living in @Context@.
  }

instance Flexs SizeMeta HypSizeConstraint where
  flexs (HypSizeConstraint _ _ hs c) = flexs hs `mappend` flexs c

instance PrettyTCM HypSizeConstraint where
  prettyTCM (HypSizeConstraint cxt _ hs c) =
    inTopContext $ modifyContext (const cxt) $ do
      -- text ("[#cxt=" ++ show (size cxt) ++ "]") <+> do
      applyUnless (null hs)
       (((hcat $ punctuate (text ", ") $ map prettyTCM hs) <+> text "|-") <+>)
       (prettyTCM c)

-- | Turn a constraint over de Bruijn indices into a size constraint.
computeSizeConstraint :: Closure TCM.Constraint -> TCM (Maybe HypSizeConstraint)
computeSizeConstraint c = do
  let cxt = envContext $ clEnv c
  inTopContext $ modifyContext (const cxt) $ do
    case clValue c of
      ValueCmp CmpLeq _ u v -> do
        reportSDoc "tc.size.solve" 50 $ sep $
          [ text "converting size constraint"
          , prettyTCM c
          ]
        ma <- sizeExpr u
        mb <- sizeExpr v
        (hids, hs) <- unzip <$> getSizeHypotheses cxt
        let mk a b = HypSizeConstraint cxt hids hs $ Size.Constraint a Le b
        -- We only create a size constraint if both terms can be
        -- parsed to our format of size expressions.
        return $ mk <$> ma <*> mb
      _ -> __IMPOSSIBLE__

-- | Turn a term into a size expression.
--
--   Returns 'Nothing' if the term isn't a proper size expression.

sizeExpr :: Term -> TCM (Maybe DBSizeExpr)
sizeExpr u = do
  u <- reduce u -- Andreas, 2009-02-09.
                -- This is necessary to surface the solutions of metavariables.
  reportSDoc "tc.conv.size" 60 $ text "sizeExpr:" <+> prettyTCM u
  s <- sizeView u
  case s of
    SizeInf     -> return $ Just Infty
    SizeSuc u   -> fmap (`plus` (1 :: Offset)) <$> sizeExpr u
    OtherSize u -> case ignoreSharing u of
      Var i []    -> (\ x -> Just $ Rigid (NamedRigid x i) 0) . show <$> nameOfBV i
--      MetaV m es  -> return $ Just $ Flex (SizeMeta m es) 0
      MetaV m es | Just xs <- mapM isVar es, fastDistinct xs
                  -> return $ Just $ Flex (SizeMeta m xs) 0
      _           -> return Nothing
  where
    isVar (Proj{})  = Nothing
    isVar (Apply v) = case ignoreSharing $ unArg v of
      Var i [] -> Just i
      _        -> Nothing

-- | Turn a de size expression into a term.
unSizeExpr :: DBSizeExpr -> TCM Term
unSizeExpr a =
  case a of
    Infty         -> primSizeInf
    Rigid r (O n) -> do
      unless (n >= 0) __IMPOSSIBLE__
      sizeSuc n $ var $ rigidIndex r
    Flex (SizeMeta x es) (O n) -> do
      unless (n >= 0) __IMPOSSIBLE__
      sizeSuc n $ MetaV x $ map (Apply . defaultArg . var) es
    Const{} -> __IMPOSSIBLE__
