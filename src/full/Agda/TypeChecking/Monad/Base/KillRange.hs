{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, OverlappingInstances #-}

-- | 'KillRange' instances for data structures from 'Agda.TypeChecking.Monad.Base'.

-- Andreas, 2014-05-03
module Agda.TypeChecking.Monad.Base.KillRange where

import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause

import Agda.Utils.Permutation

instance KillRange Signature where
  killRange (Sig secs defs) = killRange2 Sig secs defs

instance KillRange Sections where
  killRange = fmap killRange

instance KillRange Definitions where
  killRange = fmap killRange

instance KillRange Section where
  killRange (Section tel freeVars) = killRange2 Section tel freeVars

instance KillRange Definition where
  killRange (Defn ai name t pols occs displ mut compiled rew inst def) =
    killRange11 Defn ai name t pols occs displ mut compiled rew inst def
    -- TODO clarify: Keep the range in the defName field?

instance KillRange RewriteRule where
  killRange (RewriteRule q gamma lhs rhs t) =
    killRange5 RewriteRule q gamma lhs rhs t

instance KillRange CompiledRepresentation where
  killRange = id

instance KillRange Defn where
  killRange def =
    case def of
      Axiom -> Axiom
      Function cls comp inv mut isAbs delayed proj static copy term extlam with ->
        killRange12 Function cls comp inv mut isAbs delayed proj static copy term extlam with
      Datatype a b c d e f g h i j   -> killRange10 Datatype a b c d e f g h i j
      Record a b c d e f g h i j k l -> killRange12 Record a b c d e f g h i j k l
      Constructor a b c d e          -> killRange5 Constructor a b c d e
      Primitive a b c d              -> killRange4 Primitive a b c d

instance KillRange MutualId where
  killRange = id

instance KillRange c => KillRange (FunctionInverse' c) where
  killRange NotInjective = NotInjective
  killRange (Inverse m)  = Inverse $ killRangeMap m

instance KillRange TermHead where
  killRange SortHead     = SortHead
  killRange PiHead       = PiHead
  killRange (ConsHead q) = ConsHead $ killRange q

instance KillRange Projection where
  killRange (Projection a b c d e) = killRange4 Projection a b c d e

instance KillRange Occurrence where
  killRange = id

instance KillRange a => KillRange (Open a) where
  killRange = fmap killRange

instance KillRange DisplayForm where
  killRange (Display n vs dt) = killRange3 Display n vs dt

instance KillRange Polarity where
  killRange = id

instance KillRange DisplayTerm where
  killRange dt =
    case dt of
      DWithApp dt dts args -> killRange3 DWithApp dt dts args
      DCon q dts        -> killRange2 DCon q dts
      DDef q dts        -> killRange2 DDef q dts
      DDot v            -> killRange1 DDot v
      DTerm v           -> killRange1 DTerm v

-- * KillRange on CompiledClause

instance KillRange c => KillRange (WithArity c) where
  killRange = fmap killRange

instance KillRange c => KillRange (Case c) where
  killRange (Branches con lit all) = Branches
    (killRangeMap con)
    (killRangeMap lit)
    (killRange all)

instance KillRange CompiledClauses where
  killRange (Case i br) = killRange2 Case i br
  killRange (Done xs v) = killRange2 Done xs v
  killRange Fail        = Fail

-- * KillRange on standard data types and Utils

instance KillRange a => KillRange (Drop a) where
  killRange = fmap killRange

-- | Overlaps with @KillRange [a]@.
instance KillRange String where
  killRange = id

-- | Remove ranges in keys and values of a map.
killRangeMap :: (KillRange k, KillRange v) => KillRangeT (Map k v)
killRangeMap = Map.mapKeysMonotonic killRange . Map.map killRange

