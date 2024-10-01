{-# OPTIONS_GHC -Wunused-imports #-}

-- | Flattened scopes.
module Agda.Syntax.Scope.Flat
  ( getDefinedNames
  , createOperatorContext
  , recomputeOperatorContext
  , filterOperatorContext
  ) where

import Data.Bifunctor
import Data.Either (partitionEithers)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Concrete
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe

-- | Update the cached operator context after a change to the scope.
recomputeOperatorContext :: ScopeInfo -> ScopeInfo
recomputeOperatorContext scope = set scopeOperatorContext (createOperatorContext scope) scope

-- | Compute the operator parsing context.
createOperatorContext :: ScopeInfo -> OperatorContext
createOperatorContext scope = OperatorContext
  { opCxtFlatScope = flat
  , opCxtNames     = names
  , opCxtNotations = notations
  }
  where
    flat = flattenScope scope
    (names, notations) = localNames scope flat

-- | Discard any qualified names not in one of the given modules (given as lists of Names). Note
--   that we only keep names that live in the *top level* of one of the given modules. For instance,
--   if we filter on `[A.B, M]` we keep `A.B.f` and `M.x`, but not `A.B.C.g` or `M.N.y`.
filterOperatorContext :: [[Name]] -> OperatorContext -> OperatorContext
filterOperatorContext ms (OperatorContext (FlatScope flat) names notations) =
  OperatorContext (FlatScope $ Map.filterWithKey (const . checkPrefix) flat)
                  (filter checkPrefix names)
                  (filter (checkPrefix . notaName) notations)
  where
    checkPrefix q
      | [_] <- xs = True    -- Unqualified name
      | otherwise = any (isQual xs) ms
      where xs = List1.toList $ qnameParts q
            isQual xs m
              | Just [_] <- List.stripPrefix m xs = True   -- Needs to be qualified by *exactly* m
              | otherwise                         = False

-- | Compute a flattened scope.
flattenScope :: ScopeInfo -> FlatScope
flattenScope scope =
  FlatScope $
  Map.unionWith (<>)
    (build allNamesInScope root)
    imported
  where
    current = moduleScope $ scope ^. scopeCurrent
    root    = mergeScopes $ current : map moduleScope (scopeParents current)

    imported = Map.unionsWith (<>)
               [ qual c (build exportedNamesInScope $ moduleScope a)
               | (c, a) <- Map.toList $ scopeImports root ]
    qual c = Map.mapKeysMonotonic (q c)
      where
        q (QName x)  = Qual x
        q (Qual m x) = Qual m . q x

    build :: (forall a. InScope a => Scope -> ThingsInScope a) -> Scope -> Map QName (List1 AbstractName)
    build getNames s = Map.unionsWith (<>) $
        Map.mapKeysMonotonic QName (getNames s) :
          [ Map.mapKeysMonotonic (\ y -> Qual x y) $
              build exportedNamesInScope $ moduleScope m
          | (x, mods) <- Map.toList (getNames s)
          , AbsModule m _ <- List1.toList mods
          ]

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scope ^. scopeModules

-- | Compute all defined names in scope and their fixities/notations.
-- Note that overloaded names (constructors) can have several
-- fixities/notations. Then we 'mergeNotations'. (See issue 1194.)
getDefinedNames :: KindsOfNames -> FlatScope -> [List1 NewNotation]
getDefinedNames kinds (FlatScope names) =
  [ mergeNotations $ fmap (namesToNotation x . A.qnameName . anameName) ds
  | (x, ds) <- Map.toList names
  , any ((`elemKindsOfNames` kinds) . anameKind) ds
  ]
  -- Andreas, 2013-03-21 see Issue 822
  -- Names can have different kinds, i.e., 'defined' and 'constructor'.
  -- We need to consider all names that have *any* matching kind,
  -- not only those whose first appearing kind is matching.

-- | Compute all names (first component) and operators/notations
-- (second component) in scope.
localNames :: ScopeInfo -> FlatScope -> ([QName], [NewNotation])
localNames scope flat = second (map useDefaultFixity) $ split $ localNots ++ otherNots
  where
    defs      = getDefinedNames allKindsOfNames flat
    locals    = nubOn fst . notShadowedLocals $ scope ^. scopeLocals
    localNots = map localOp locals
    notLocal  = not . hasElem (map notaName localNots) . notaName
    otherNots = concatMap (List1.filter notLocal) defs

    localOp (x, y) = namesToNotation (QName x) y
    split          = partitionEithers . concatMap opOrNot
    opOrNot n      = Left (notaName n) :
                     [Right n | not (null (notation n))]
