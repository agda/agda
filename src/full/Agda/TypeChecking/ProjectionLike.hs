{-# LANGUAGE CPP               #-}

-- | Dropping initial arguments (``parameters'') from a function which can be
--   easily reconstructed from its principal argument.
--
--   A function which has such parameters is called ``projection-like''.
--
--   The motivation for this optimization comes from the use of nested records.
--
--   First, let us look why proper projections need not store the parameters:
--   The type of a projection @f@ is of the form
--   @
--      f : Γ → R Γ → C
--   @
--   where @R@ is the record type and @C@ is the type of the field @f@.
--   Given a projection application
--   @
--      p pars u
--   @
--   we know that the type of the principal argument @u@ is
--   @
--      u : R pars
--   @
--   thus, the parameters @pars@ are redundant in the projection application
--   if we can always infer the type of @u@.
--   For projections, this is case, because the principal argument @u@ must be
--   neutral; otherwise, if it was a record value, we would have a redex,
--   yet Agda maintains a β-normal form.
--
--   The situation for projections can be generalized to ``projection-like''
--   functions @f@.  Conditions:
--
--     1. The type of @f@ is of the form @f : Γ → D Γ → ...@ for some
--        type constructor @D@ which can never reduce.
--
--     2. For every reduced welltyped application @f pars u ...@,
--        the type of @u@ is inferable.
--
--   This then allows @pars@ to be dropped always.
--
--   Condition 2 is approximated by a bunch of criteria, for details see function
--   'makeProjection'.
--
--   Typical projection-like functions are compositions of projections
--   which arise from nested records.
--
--   Notes:
--
--     1. This analysis could be dualized to ``constructor-like'' functions
--        whose parameters are reconstructable from the target type.
--        But such functions would need to be fully applied.
--
--     2. A more general analysis of which arguments are reconstructible
--        can be found in
--
--          Jason C. Reed, Redundancy elimination for LF
--          LFTMP 2004.

module Agda.TypeChecking.ProjectionLike where

import Control.Monad

import qualified Data.Map as Map
import Data.Monoid (Any(..), getAny)

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Free (runFree, IgnoreSorts(..))
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce)

import Agda.TypeChecking.DropArgs

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Permutation

#include "undefined.h"
import Agda.Utils.Impossible

-- | View for a @Def f (Apply a : es)@ where @isProjection f@.
--   Used for projection-like @f@s.
data ProjectionView
  = ProjectionView
    { projViewProj  :: QName
    , projViewSelf  :: Arg Term
    , projViewSpine :: Elims
    }
    -- ^ A projection or projection-like function, applied to its
    --   principal argument
  | LoneProjectionLike QName ArgInfo
    -- ^ Just a lone projection-like function, missing its principal
    --   argument (from which we could infer the parameters).
  | NoProjection Term
    -- ^ Not a projection or projection-like thing.

-- | Semantics of 'ProjectionView'.
unProjView :: ProjectionView -> Term
unProjView pv =
  case pv of
    ProjectionView f a es   -> Def f (Apply a : es)
    LoneProjectionLike f ai -> Def f []
    NoProjection v          -> v

-- | Top-level 'ProjectionView' (no reduction).
{-# SPECIALIZE projView :: Term -> TCM ProjectionView #-}
projView :: HasConstInfo m => Term -> m ProjectionView
projView v = do
  let fallback = return $ NoProjection v
  case ignoreSharing v of
    Def f es -> caseMaybeM (isProjection f) fallback $ \ isP -> do
      if projIndex isP <= 0 then fallback else do
        case es of
          []           -> return $ LoneProjectionLike f $ projArgInfo isP
          Apply a : es -> return $ ProjectionView f a es
          -- Since a projection is a function, it cannot be projected itself.
          Proj{}  : _  -> __IMPOSSIBLE__
    _ -> fallback

-- | Reduce away top-level projection like functions.
--   (Also reduces projections, but they should not be there,
--   since Internal is in lambda- and projection-beta-normal form.)
--
reduceProjectionLike :: Term -> TCM Term
reduceProjectionLike v = do
  -- Andreas, 2013-11-01 make sure we do not reduce a constructor
  -- because that could be folded back into a literal by reduce.
  pv <- projView v
  case pv of
    ProjectionView{} -> onlyReduceProjections $ reduce v
                            -- ordinary reduce, only different for Def's
    _                -> return v

-- | Turn prefix projection-like function application into postfix ones.
--   This does just one layer, such that the top spine contains
--   the projection-like functions as projections.
--   Used in 'compareElims' in @TypeChecking.Conversion@
--   and in "Agda.TypeChecking.CheckInternal".
--
--   If the 'Bool' is 'True', a lone projection like function will be
--   turned into a lambda-abstraction, expecting the principal argument.
--   If the 'Bool' is 'False', it will be returned unaltered.
--
--   No precondition.
--   Preserves constructorForm, since it really does only something
--   on (applications of) projection-like functions.
elimView :: Bool -> Term -> TCM Term
elimView loneProjToLambda v = do
  reportSDoc "tc.conv.elim" 30 $ text "elimView of " <+> prettyTCM v
  reportSLn  "tc.conv.elim" 50 $ "v = " ++ show v
  v <- reduceProjectionLike v
  reportSDoc "tc.conv.elim" 40 $
    text "elimView (projections reduced) of " <+> prettyTCM v
  pv <- projView v
  case pv of
    NoProjection{}        -> return v
    LoneProjectionLike f ai
      | loneProjToLambda  -> return $ Lam ai $ Abs "r" $ Var 0 [Proj ProjPrefix f]
      | otherwise         -> return v
    ProjectionView f a es -> (`applyE` (Proj ProjPrefix f : es)) <$> elimView loneProjToLambda (unArg a)

-- | Which @Def@types are eligible for the principle argument
--   of a projection-like function?
eligibleForProjectionLike :: QName -> TCM Bool
eligibleForProjectionLike d = do
  defn <- theDef <$> getConstInfo d
  return $ case defn of
    Datatype{} -> True
    Record{}   -> True
    Axiom{}    -> True
    Function{}    -> False
    Primitive{}   -> False
    Constructor{} -> __IMPOSSIBLE__
    AbstractDefn  -> False
      -- Andreas, 2016-10-11 AIM XXIV
      -- Projection-like at abstract types violates the parameter reconstructibility property.
      -- See test/Fail/AbstractTypeProjectionLike.

-- | Turn a definition into a projection if it looks like a projection.
--
-- Conditions for projection-likeness of @f@:
--
--   1. The type of @f@ must be of the shape @Γ → D Γ → C@ for @D@
--      a name (@Def@) which is 'eligibleForProjectionLike':
--      @data@ / @record@ / @postulate@.
--
--   2. The application of f should only get stuck if the principal argument
--      is inferable (neutral).  Thus:
--
--      a. @f@ cannot have absurd clauses (which are stuck even if the principal
--         argument is a constructor)
--
--      b. @f@ cannot be abstract as it does not reduce outside abstract blocks
--         (always stuck).
--
--      c. @f@ cannot match on other arguments than the principal argument.
--
--      d. @f@ cannot match deeply.
--
--      e. @f@s body may not mention the paramters.
--
-- For internal reasons:
--
--   3. @f@ cannot be constructor headed
--
--   4. @f@ cannot be recursive, since we have not implemented a function
--      which goes through the bodies of the @f@ and the mutually recursive
--      functions and drops the parameters from all applications of @f@.
--
-- Examples for these reasons: see test/Succeed/NotProjectionLike.agda

makeProjection :: QName -> TCM ()
makeProjection x = -- if True then return () else do
 inTopContext $ do
  -- reportSLn "tc.proj.like" 30 $ "Considering " ++ show x ++ " for projection likeness"
  defn <- getConstInfo x
  let t = defType defn
  reportSDoc "tc.proj.like" 20 $ sep
    [ text "Checking for projection likeness "
    , prettyTCM x <+> text " : " <+> prettyTCM t
    ]
  case theDef defn of
    Function{funClauses = cls}
      | any (isNothing . clauseBody) cls ->
        reportSLn "tc.proj.like" 30 $ "  projection-like functions cannot have absurd clauses"
    -- Constructor-headed functions can't be projection-like (at the moment). The reason
    -- for this is that invoking constructor-headedness will circumvent the inference of
    -- the dropped arguments.
    -- Nor can abstract definitions be projection-like since they won't reduce
    -- outside the abstract block.
    def@Function{funProjection = Nothing, funClauses = cls, funCompiled = cc0, funInv = NotInjective,
                 funMutual = Just [], -- Andreas, 2012-09-28: only consider non-mutual funs (or those whose recursion status has not yet been determined)
                 funAbstr = ConcreteDef} -> do
      ps0 <- filterM validProj $ candidateArgs [] t
      reportSLn "tc.proj.like" 30 $ if null ps0 then "  no candidates found"
                                                else "  candidates: " ++ show ps0
      unless (null ps0) $ do
        -- Andreas 2012-09-26: only consider non-recursive functions for proj.like.
        -- Issue 700: problems with recursive funs. in term.checker and reduction
        ifM recursive (reportSLn "tc.proj.like" 30 $ "  recursive functions are not considered for projection-likeness") $ do
          {- else -}
          case lastMaybe (filter (checkOccurs cls . snd) ps0) of
            Nothing -> reportSLn "tc.proj.like" 50 $
              "  occurs check failed\n    clauses = " ++ show cls
            Just (d, n) -> do
              -- Yes, we are projection-like!
              reportSDoc "tc.proj.like" 10 $ sep
                [ prettyTCM x <+> text " : " <+> prettyTCM t
                , text $ " is projection like in argument " ++ show n ++ " for type " ++ show d
                ]
              __CRASH_WHEN__ "tc.proj.like.crash" 1000

              let cls' = map (dropArgs n) cls
                  cc   = dropArgs n cc0
              reportSLn "tc.proj.like" 60 $ "  rewrote clauses to\n    " ++ show cc

              -- Andreas, 2013-10-20 build parameter dropping function
              let pIndex = n + 1
                  tel = take pIndex $ telToList $ theTel $ telView' t
              unless (length tel == pIndex) __IMPOSSIBLE__
              let projection = Projection
                    { projProper   = Nothing
                    , projOrig     = x
                    , projFromType = d
                    , projIndex    = pIndex
                    , projLams     = ProjLams $ map (\ (Dom ai (y, _)) -> Arg ai y) tel
                    }
              let newDef = def
                           { funProjection     = Just projection
                           , funClauses        = cls'
                           , funCompiled       = cc
                           , funInv            = dropArgs n $ funInv def
                           }
              addConstant x $ defn { defPolarity       = drop n $ defPolarity defn
                                   , defArgOccurrences = drop n $ defArgOccurrences defn
                                   , defDisplay        = []
                                   , theDef            = newDef
                                   }
    Function{funInv = Inverse{}} ->
      reportSLn "tc.proj.like" 30 $ "  injective functions can't be projections"
    Function{funAbstr = AbstractDef} ->
      reportSLn "tc.proj.like" 30 $ "  abstract functions can't be projections"
    Function{funProjection = Just{}} ->
      reportSLn "tc.proj.like" 30 $ "  already projection like"
    _ -> reportSLn "tc.proj.like" 30 $ "  not a function"
  where
    -- @validProj (d,n)@ checks whether the head @d@ of the type of the
    -- @n@th argument is injective in all args (i.d. being name of data/record/axiom).
    validProj :: (Arg QName, Int) -> TCM Bool
    validProj (_, 0) = return False
    validProj (d, _) = eligibleForProjectionLike (unArg d)

    -- NOTE: If the following definition turns out to be slow, then
    -- one could perhaps reuse information computed by the termination
    -- and/or positivity checkers.
    recursive = do
      occs <- computeOccurrences x
      let xocc = Map.lookup (ADef x) occs
      case xocc of
        Just (_ : _) -> return True -- recursive occurrence
        _            -> return False

    checkOccurs cls n = all (nonOccur n) cls

    nonOccur n cl =
      and [ take n p == [0..n - 1]
          , onlyMatch n ps  -- projection-like functions are only allowed to match on the eliminatee
                            -- otherwise we may end up projecting from constructor applications, in
                            -- which case we can't reconstruct the dropped parameters
          , checkBody m n b ]
      where
        Perm _ p = fromMaybe __IMPOSSIBLE__ $ clausePerm cl
        ps       = namedClausePats cl
        b        = compiledClauseBody cl  -- Renumbers variables to match order in patterns
                                          -- and includes dot patterns as variables.
        m        = size $ concatMap patternVars ps  -- This also counts dot patterns!


    onlyMatch n ps = all (shallowMatch . namedArg) (take 1 ps1) &&
                     noMatches (ps0 ++ drop 1 ps1)
      where
        (ps0, ps1) = splitAt n ps
        shallowMatch (ConP _ _ ps) = noMatches ps
        shallowMatch _             = True
        noMatches = all (noMatch . namedArg)
        noMatch ConP{} = False
        noMatch LitP{} = False
        noMatch ProjP{}= False
        noMatch VarP{} = True
        noMatch DotP{} = True
        noMatch AbsurdP{} = True

    -- Make sure non of the parameters occurs in the body of the function.
    checkBody m n b = not . getAny $ runFree badVar IgnoreNot b
      where badVar x = Any $ m - n <= x && x < m

    -- @candidateArgs [var 0,...,var(n-1)] t@ adds @(n,d)@ to the output,
    -- if @t@ is a function-type with domain @t 0 .. (n-1)@
    -- (the domain of @t@ is the type of the arg @n@).
    --
    -- This means that from the type of arg @n@ all previous arguments
    -- can be computed by a simple matching.
    -- (Provided the @d@ is data/record/postulate, checked in @validProj@).
    --
    -- E.g. f : {x : _}(y : _){z : _} -> D x y z -> ...
    -- will return (D,3) as a candidate (amongst maybe others).
    --
    candidateArgs :: [Term] -> Type -> [(Arg QName, Int)]
    candidateArgs vs t =
      case ignoreSharing $ unEl t of
        Pi a b
          | Def d es <- ignoreSharing $ unEl $ unDom a,
            Just us  <- allApplyElims es,
            vs == map unArg us -> (d <$ argFromDom a, length vs) : candidateRec b
          | otherwise          -> candidateRec b
        _                      -> []
      where
        candidateRec NoAbs{}   = []
        candidateRec (Abs x t) = candidateArgs (var (size vs) : vs) t
