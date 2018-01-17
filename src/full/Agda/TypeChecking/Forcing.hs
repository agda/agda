{-# LANGUAGE CPP               #-}
{-# LANGUAGE TypeFamilies #-}

{-| A constructor argument is forced if it appears as pattern variable
in an index of the target.

For instance @x@ is forced in @sing@ and @n@ is forced in @zero@ and @suc@:

@
  data Sing {a}{A : Set a} : A -> Set where
    sing : (x : A) -> Sing x

  data Fin : Nat -> Set where
    zero : (n : Nat) -> Fin (suc n)
    suc  : (n : Nat) (i : Fin n) -> Fin (suc n)
@

At runtime, forced constructor arguments may be erased as they can be
recovered from dot patterns.  For instance,
@
  unsing : {A : Set} (x : A) -> Sing x -> A
  unsing .x (sing x) = x
@
can become
@
  unsing x sing = x
@
and
@
  proj : (n : Nat) (i : Fin n) -> Nat
  proj .(suc n) (zero n) = n
  proj .(suc n) (suc n i) = n
@
becomes
@
  proj (suc n) zero    = n
  proj (suc n) (suc i) = n
@

Forcing is a concept from pattern matching and thus builds on the
concept of equality (I) used there (closed terms, extensional) which is
different from the equality (II) used in conversion checking and the
constraint solver (open terms, intensional).

Up to issue 1441 (Feb 2015), the forcing analysis here relied on the
wrong equality (II), considering type constructors as injective.  This is
unsound for program extraction, but ok if forcing is only used to decide which
arguments to skip during conversion checking.

From now on, forcing uses equality (I) and does not search for forced
variables under type constructors.  This may lose some savings during
conversion checking.  If this turns out to be a problem, the old
forcing could be brought back, using a new modality @Skip@ to indicate
that this is a relevant argument but still can be skipped during
conversion checking as it is forced by equality (II).

-}

module Agda.TypeChecking.Forcing where

import Control.Arrow (first, second)
import Control.Monad
import Data.Foldable hiding (any)
import Data.Traversable
import Data.Semigroup hiding (Arg)
import Data.Maybe
import Data.List ((\\))

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Pretty hiding ((<>))

import Agda.Utils.Function
import Agda.Utils.PartialOrd
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Given the type of a constructor (excluding the parameters),
--   decide which arguments are forced.
--   Precondition: the type is of the form @Γ → D vs@ and the @vs@
--   are in normal form.
computeForcingAnnotations :: Type -> TCM [IsForced]
computeForcingAnnotations t =
  ifM (not . optForcing <$> commandLineOptions)
      (return []) $ do
  -- Andreas, 2015-03-10  Normalization prevents Issue 1454.
  -- t <- normalise t
  -- Andreas, 2015-03-28  Issue 1469: Normalization too costly.
  -- Instantiation also fixes Issue 1454.
  -- Note that normalization of s0 below does not help.
  t <- instantiateFull t
  let TelV tel (El _ a) = telView' t
      vs = case ignoreSharing a of
        Def _ us -> us
        _        -> __IMPOSSIBLE__
      n  = size tel
      xs = forcedVariables vs
      -- #2819: We can only mark an argument as forced if it appears in the
      -- type with a relevance below (i.e. more relevant) than the one of the
      -- constructor argument. Otherwise we can't actually get the value from
      -- the type. Also the argument shouldn't be irrelevant, since it that
      -- case it isn't really forced.
      isForced m i = getRelevance m /= Irrelevant &&
                     any (\ (m', j) -> i == j && related m' POLE m) xs
      forcedArgs =
        [ if isForced m i then Forced else NotForced
        | (i, m) <- zip (downFrom n) $ map getModality (telToList tel)
        ]
  reportSLn "tc.force" 60 $ unlines
    [ "Forcing analysis"
    , "  xs          = " ++ show xs
    , "  forcedArgs  = " ++ show forcedArgs
    ]
  return forcedArgs

-- | Compute the pattern variables of a term or term-like thing.
class ForcedVariables a where
  forcedVariables :: a -> [(Modality, Nat)]

  default forcedVariables :: (ForcedVariables b, Foldable t, a ~ t b) => a -> [(Modality, Nat)]
  forcedVariables = foldMap forcedVariables

instance ForcedVariables a => ForcedVariables [a] where

-- Note the 'a' does not include the 'Arg' in 'Apply'.
instance ForcedVariables a => ForcedVariables (Elim' a) where
  forcedVariables (Apply x) = forcedVariables x
  forcedVariables Proj{} = []

instance ForcedVariables a => ForcedVariables (Arg a) where
  forcedVariables x = [ (m <> m', i) | (m', i) <- forcedVariables (unArg x) ]
    where m = getModality x

-- | Assumes that the term is in normal form.
instance ForcedVariables Term where
  forcedVariables t = case ignoreSharing t of
    Var i [] -> [(mempty, i)]
    Con _ _ vs -> forcedVariables vs
    _ -> []

isForced :: IsForced -> Bool
isForced Forced    = True
isForced NotForced = False

nextIsForced :: [IsForced] -> (IsForced, [IsForced])
nextIsForced []     = (NotForced, [])
nextIsForced (f:fs) = (f, fs)

-----------------------------------------------------------------------------
-- * Forcing translation
-----------------------------------------------------------------------------

-- | Move bindings for forced variables to non-forced positions.
forcingTranslation :: [NamedArg DeBruijnPattern] -> TCM [NamedArg DeBruijnPattern]
forcingTranslation = go 1000
  where
    go 0 _ = __IMPOSSIBLE__
    go n ps = do
      qs <- forcedPatterns ps
      reportSDoc "tc.force" 50 $ text "forcingTranslation" <?> vcat
        [ text "patterns:" <?> pretty ps
        , text "forced:" <?> pretty qs ]
      case qs of
        []    -> return ps
        q : _ -> go (n - 1) $ unforce q ps
          -- This should terminate, but it's not obvious that you couldn't have
          -- a situation where you move a forced argument between two different
          -- forced positions indefinitely. Cap it to 1000 iterations to guard
          -- against this case.

-- | Applies the forcing translation in order to update modalities of forced
--   arguments in the telescope. This is used before checking a right-hand side
--   in order to make sure all uses of forced arguments agree with the
--   relevance of the position where the variable will ultimately be bound.
--   Precondition: the telescope types the bound variables of the patterns.
forceTranslateTelescope :: Telescope -> [NamedArg DeBruijnPattern] -> TCM Telescope
forceTranslateTelescope delta qs = do
  qs' <- forcingTranslation qs
  let xms  = patternVarModalities qs
      xms' = patternVarModalities qs'
      old  = xms \\ xms'
      new  = xms' \\ xms
  if null new then return delta else do
      reportSLn "tc.force" 40 $ "Updating modalities of forced arguments\n" ++
                                "  from: " ++ show old ++ "\n" ++
                                "  to:   " ++ show new
      let mods    = map (first dbPatVarIndex) new
          ms      = reverse [ lookup i mods | i <- [0..size delta - 1] ]
          delta'  = telFromList $ zipWith (maybe id setModality) ms $ telToList delta
      reportSDoc "tc.force" 60 $ nest 2 $ text "delta' =" <?> prettyTCM delta'
      return delta'

-- | Move the bindings in a forced pattern to non-forced positions.
--   Takes a list of top-level patterns `ps` (second argument) and a pattern to
--   "unforce" `q` (first argument). The first argument should appear somewhere
--   (possibly deep) inside the second argument. The result is a new list of
--   top-level patterns where `q` has been turned into a dot pattern, and the
--   binding sites of variables previously bound in `q` have been moved by
--   turning dot patterns into proper patterns.
--
--   Preconditions:
--    - `q` must appear in a forced position in `ps`. This ensures that we can
--      find alternative binding sites for its variables.
--    - `q` must bind at least one variable. This ensures that there is a
--      unique occurrence of `q` in `ps`.
--
--   For instance (with patterns prettified to ease readability):
--
--    unforce n [.(suc n), cons n x xs] = [suc n, cons .n x xs]
--
unforce :: DeBruijnPattern -> [NamedArg DeBruijnPattern] -> [NamedArg DeBruijnPattern]
unforce q [] = __IMPOSSIBLE__   -- unforcing cannot fail
unforce q (p : ps) =
  case namedArg p of
    VarP o y -> fmap (mkDot q (VarP o y) <$) p : unforce q ps
    DotP _ v | Just q' <- mkPat q v -> (fmap (q' <$) p : (fmap . fmap . fmap) (mkDot q) ps)
    DotP{} -> p : unforce q ps
    ConP c i qs -> fmap (ConP c i qs' <$) p : ps'
      where
        qps        = unforce q (qs ++ ps)
        (qs', ps') = splitAt (length qs) qps
    LitP{} -> p : unforce q ps
    ProjP{} -> p : unforce q ps
  where
    -- Turn a match on q into a dot pattern
    mkDot :: DeBruijnPattern -> DeBruijnPattern -> DeBruijnPattern
    mkDot q p | p =:= q = dotP $ patternToTerm p
    mkDot q p = case p of
      VarP{}          -> p
      DotP{}          -> p
      ConP c i ps     -> ConP c i $ (fmap . fmap . fmap) (mkDot q) ps
      LitP{}          -> p
      ProjP{}         -> p

    p =:= q = patternToElim (defaultArg p) == patternToElim (defaultArg q)

    -- Try to turn a term in a dot pattern into a pattern matching q
    mkPat :: DeBruijnPattern -> Term -> Maybe DeBruijnPattern
    mkPat q v | patternToTerm q == v = Just q
    mkPat q v =
      case v of
        Con c co vs -> do
          let mps = (map . traverse) (mkPat q) vs
          (mvs1, (_, Just p) : mvs2) <- return $ break (isJust . snd) (zip vs mps)
          let vs1 = map fst mvs1
              vs2 = map fst mvs2
              ci = (toConPatternInfo co) { conPLazy = True }
              dots = (map . fmap) dotP
          return (ConP c ci $ doname $ dots vs1 ++ [p] ++ dots vs2)
        _ -> Nothing
      where
        doname = (map . fmap) unnamed

forcedPatterns :: [NamedArg (Pattern' x)] -> TCM [Pattern' x]
forcedPatterns ps = concat <$> mapM (forced NotForced . namedArg) ps
  where
    forced :: IsForced -> Pattern' x -> TCM [Pattern' x]
    forced f p =
      case p of
        VarP{}  -> return [p | f == Forced]
        DotP{}  -> return []
        ConP c _ args
          | f == Forced -> return [p]
          | otherwise   -> do
            fs <- defForced <$> getConstInfo (conName c)
            concat <$> zipWithM forced (fs ++ repeat NotForced) (map namedArg args)
        LitP{}    -> return []
        ProjP{}   -> return []
