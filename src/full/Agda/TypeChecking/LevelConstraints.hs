
module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraint ) where

import qualified Data.List as List
import Data.Maybe
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level

import Agda.Utils.Impossible
import Agda.Utils.List (nubOn)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Update

-- | @simplifyLevelConstraint c cs@ turns an @c@ into an equality
--   constraint if it is an inequality constraint and the reverse
--   inequality is contained in @cs@.
--
--   The constraints don't necessarily have to live in the same context, but
--   they do need to be universally quanitfied over the context. This function
--   takes care of renaming variables when checking for matches.
simplifyLevelConstraint
  :: Constraint          -- ^ Constraint @c@ to simplify.
  -> [Constraint]        -- ^ Other constraints, enable simplification.
  -> Maybe [Constraint]  -- ^ @Just@: list of constraints equal to the original @c@.
                         --   @Nothing@: no simplification possible.
simplifyLevelConstraint c others = do
    cs <- inequalities c
    case runChange $ mapM simpl cs of
      (cs', True) -> Just cs'
      (_,  False) -> Nothing

  where
    simpl :: Leq -> Change (Constraint)
    simpl (a :=< b)
      | any (matchLeq (b :=< a)) leqs = dirty  $ LevelCmp CmpEq  (unSingleLevel a) (unSingleLevel b)
      | otherwise                     = return $ LevelCmp CmpLeq (unSingleLevel a) (unSingleLevel b)
    leqs = concat $ mapMaybe inequalities others

data Leq = SingleLevel :=< SingleLevel
  deriving (Show, Eq)

-- | Check if two inequality constraints are the same up to variable renaming.
matchLeq :: Leq -> Leq -> Bool
matchLeq (a :=< b) (c :=< d)
  | length xs == length ys = (a, b) == applySubst rho (c, d)
  | otherwise              = False
  where
    free :: Free a => a -> [Int]
    free = nubOn id . runFree (:[]) IgnoreNot  -- Note: use a list to preserve order of variables
    xs  = free (a, b)
    ys  = free (c, d)
    rho = mkSub $ List.sort $ zip ys xs
    mkSub = go 0
      where
        go _ [] = IdS
        go y ren0@((y', x) : ren)
          | y == y'   = Var x [] :# go (y + 1) ren
          | otherwise = strengthenS' impossible 1 $ go (y + 1) ren0

-- | Turn a level constraint into a list of inequalities between
--   single levels, if possible.

inequalities :: Constraint -> Maybe [Leq]

inequalities (LevelCmp CmpLeq a b)
  | Just b' <- singleLevelView b = Just $ map (:=< b') $ List1.toList $ levelMaxView a
  -- Andreas, 2016-09-28
  -- Why was this most natural case missing?
  -- See test/Succeed/LevelLeqGeq.agda for where it is useful!

-- These are very special cases only, in no way complete:
-- E.g.: a = a ⊔ b ⊔ c --> b ≤ a & c ≤ a

inequalities (LevelCmp CmpEq a b)
  | Just a' <- singleLevelView a =
  case List1.break (== a') (levelMaxView b) of
    (bs0, _ : bs1) -> Just [ b' :=< a' | b' <- bs0 ++ bs1 ]
    _              -> Nothing

inequalities (LevelCmp CmpEq a b)
  | Just b' <- singleLevelView b =
  case List1.break (== b') (levelMaxView a) of
    (as0, _ : as1) -> Just [ a' :=< b' | a' <- as0 ++ as1 ]
    _              -> Nothing
inequalities _ = Nothing
