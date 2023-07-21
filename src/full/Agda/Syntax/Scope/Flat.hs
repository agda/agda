{-# OPTIONS_GHC -Wunused-imports #-}

-- | Flattened scopes.
module Agda.Syntax.Scope.Flat
  ( FlatScope
  , flattenScope
  , getDefinedNames
  , localNames
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
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Debug

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Pretty

-- | Flattened scopes.
newtype FlatScope = Flat (Map QName [AbstractName])
  deriving Pretty

-- | Compute a flattened scope. Only include unqualified names or names
-- qualified by modules in the first argument.
flattenScope :: [[Name]] -> ScopeInfo -> FlatScope
flattenScope ms scope =
  Flat $
  Map.unionWith (++)
    (build ms allNamesInScope root)
    imported
  where
    current = moduleScope $ scope ^. scopeCurrent
    root    = mergeScopes $ current : map moduleScope (scopeParents current)

    imported = Map.unionsWith (++)
               [ qual c (build ms' exportedNamesInScope $ moduleScope a)
               | (c, a) <- Map.toList $ scopeImports root
               , let -- get the suffixes of c in ms
                     ms' = mapMaybe (List.stripPrefix $ List1.toList $ qnameParts c) ms
               , not $ null ms' ]
    qual c = Map.mapKeysMonotonic (q c)
      where
        q (QName x)  = Qual x
        q (Qual m x) = Qual m . q x

    build :: [[Name]] -> (forall a. InScope a => Scope -> ThingsInScope a) -> Scope -> Map QName [AbstractName]
    build ms getNames s = Map.unionsWith (++) $
        Map.mapKeysMonotonic QName (getNames s) :
          [ Map.mapKeysMonotonic (\ y -> Qual x y) $
              build ms' exportedNamesInScope $ moduleScope m
          | (x, mods) <- Map.toList (getNames s)
          , let ms' = [ tl | hd:tl <- ms, hd == x ]
          , not $ null ms'
          , AbsModule m _ <- mods ]

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scope ^. scopeModules

-- | Compute all defined names in scope and their fixities/notations.
-- Note that overloaded names (constructors) can have several
-- fixities/notations. Then we 'mergeNotations'. (See issue 1194.)
getDefinedNames :: KindsOfNames -> FlatScope -> [[NewNotation]]
getDefinedNames kinds (Flat names) =
  [ mergeNotations $ map (namesToNotation x . A.qnameName . anameName) ds
  | (x, ds) <- Map.toList names
  , any ((`elemKindsOfNames` kinds) . anameKind) ds
  , not (null ds)
  ]
  -- Andreas, 2013-03-21 see Issue 822
  -- Names can have different kinds, i.e., 'defined' and 'constructor'.
  -- We need to consider all names that have *any* matching kind,
  -- not only those whose first appearing kind is matching.

-- | Compute all names (first component) and operators/notations
-- (second component) in scope.
localNames :: FlatScope -> ScopeM ([QName], [NewNotation])
localNames flat = do
  let defs = getDefinedNames allKindsOfNames flat
  locals <- nubOn fst . notShadowedLocals <$> getLocalVars
  -- Note: Debug printout aligned with the one in
  -- Agda.Syntax.Concrete.Operators.buildParsers.
  reportS "scope.operators" 50
    [ "flat  = " ++ prettyShow flat
    , "defs  = " ++ prettyShow defs
    , "locals= " ++ prettyShow locals
    ]
  let localNots  = map localOp locals
      notLocal   = not . hasElem (map notaName localNots) . notaName
      otherNots  = concatMap (filter notLocal) defs
  return $ second (map useDefaultFixity) $ split $ localNots ++ otherNots
  where
    localOp (x, y) = namesToNotation (QName x) y
    split          = partitionEithers . concatMap opOrNot
    opOrNot n      = Left (notaName n) :
                     [Right n | not (null (notation n))]
