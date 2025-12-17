
-- | Computing scopes of names that are relevant to parsing
--   some raw expression.
module Agda.Syntax.Scope.Operator
  ( OperatorScope(..)
  , getOperatorScope
  , getDefinedNames
  , localNames
  ) where

import Prelude hiding ( (||) )

import Data.Bifunctor
import Data.Either (partitionEithers)
import Data.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Agda.Syntax.Abstract.Name as A

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Concrete
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Debug

import Agda.Utils.Boolean ( (||) )
import Agda.Utils.Function ( applyWhenJust )
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 (List1, NonEmpty(..))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.AssocList (AssocList)
import Agda.Utils.Impossible

-- | Looking up all name parts of a QName.
namePartScopeLookup :: QName -> ScopeInfo -> [Map Name (List1 AbstractName)]
namePartScopeLookup q scope = inAllScopes ++ imports
  where
    -- 1. Finding a name in the current scope and its parents.
    inAllScopes :: [Map Name (List1 AbstractName)]
    inAllScopes = concatMap (findName q) allScopes

    -- 2. Finding a name in the imports belonging to an initial part of the qualifier.
    imports :: [Map Name (List1 AbstractName)]
    imports = do
      let -- return all possible splittings, e.g.
          -- splitName X.Y.Z = [(X, Y.Z), (X.Y, Z)]
          splitName :: QName -> [(QName, QName)]
          splitName (QName x)  = []
          splitName (Qual x q) =
            (QName x, q) : [ (Qual x m, r) | (m, r) <- splitName q ]

      (m, x) <- splitName q
      s <- allScopes
      m <- maybeToList $ Map.lookup m $ scopeImports s
      findName x $ restrictPrivate $ moduleScope m

    moduleScope :: A.ModuleName -> Scope
    moduleScope m = fromMaybe __IMPOSSIBLE__ $ Map.lookup m $ scope ^. scopeModules

    allScopes :: [Scope]
    allScopes = current : map moduleScope (scopeParents current) where
      current = moduleScope $ scope ^. scopeCurrent

    findName :: QName -> Scope -> [Map Name (List1 AbstractName)]
    findName q0 s = case q0 of
      QName x  -> do
        n       <- nameStringParts x
        (_, ns) <- scopeNameSpaces s
        maybeToList $ Map.lookup n (nsNameParts ns)
      Qual x q -> do
        m <- amodName . fst <$> findNameInScope x s
        let ss = restrictPrivate <$> (Map.lookup m $ scope ^. scopeModules)
        s' <- maybeToList ss
        findName q s'

getOperatorScope :: Set QName -> ScopeInfo -> OperatorScope
getOperatorScope names scope = let

    nameList :: [QName]
    nameList = Set.toList names

    namePartSet :: Set NameParts
    namePartSet = let
      getParts :: QName -> NameParts
      getParts (QName x)  = nameParts x
      getParts (Qual _ x) = getParts x

      go :: Set NameParts -> QName -> Set NameParts
      go acc x = let
        parts = getParts x
        goPart !acc Hole  = acc
        goPart acc (Id x) = Set.insert (Id x :| []) acc
        in foldl' goPart (Set.insert parts acc) parts

      in foldl' go mempty nameList

    -- look up the name as a full identifier
    fullNameLookups :: [(QName, List1 AbstractName)]
    fullNameLookups = do
      qname <- nameList
      case scopeLookup qname scope of
        []   -> []
        a:as -> [(qname, a :| as)]

    requalify :: QName -> Name -> QName
    requalify qn n = case qn of
      QName _   -> QName n
      Qual x qn -> Qual x $! requalify qn n

    -- lookup all parts of a name as operator/notation parts
    namePartLookups :: [(QName, List1 AbstractName)]
    namePartLookups = do
      qname      <- nameList
      map        <- namePartScopeLookup qname scope
      (name, as) <- Map.toList map
      let !name' = requalify qname name
      pure (name', as)

    goLocals :: LocalVars -> (AssocList Name A.Name, Bool)
    goLocals ls = go ls mempty where
      go :: LocalVars -> Set Name -> (AssocList Name A.Name, Bool)
      go [] !seen = ([], False)
      go ((x, a):ls) seen | Set.member x seen = go ls seen
      go ((x, a):ls) seen = case notShadowedLocal a of
        Nothing -> go ls seen
        Just a  ->
          let goNamePart = \case
                Id x -> Set.member (Id x :| []) namePartSet
                _    -> False
              goNotPart = \case
                IdPart x -> Set.member (Id (rangedThing x) :| []) namePartSet
                _        -> False
              not           = theNotation (A.nameFixity a)
              parts         = nameParts x
              anyOp         = (any (== Hole) parts && any goNamePart parts) || any goNotPart not
              anyName       = Set.member parts namePartSet
              (ls', anyOp') = go ls (Set.insert x seen)
              !anyOp''      = anyOp || anyOp'
              !ls''         = if anyOp || anyName then (x, a):ls' else ls'
          in (ls'', anyOp'')

    (locals, hasLocalOp) = goLocals (scope ^. scopeLocals)

  in if null namePartLookups && not hasLocalOp
    then OpScope False (Map.fromListWith (flip List1.union) fullNameLookups) locals
    else OpScope True  (Map.fromListWith (flip List1.union) (fullNameLookups ++ namePartLookups)) locals


-- | Compute all defined names in scope and their fixities/notations.
-- Note that overloaded names (constructors) can have several
-- fixities/notations. Then we 'mergeNotations'. (See issue 1194.)
getDefinedNames' :: (AbstractName -> Bool) -> OperatorScope -> [List1 NewNotation]
getDefinedNames' f (OpScope _ names _) =
  [ mergeNotations $ fmap (namesToNotation x . A.qnameName . anameName) ds
  | (x, ds) <- Map.toList names
  , any f ds
  ]
  -- Andreas, 2013-03-21 see Issue 822
  -- Names can have different kinds, i.e., 'defined' and 'constructor'.
  -- We need to consider all names that have *any* matching kind,
  -- not only those whose first appearing kind is matching.

getDefinedNames :: KindsOfNames -> OperatorScope -> [List1 NewNotation]
getDefinedNames kinds = getDefinedNames' (filterByKind kinds)

filterByKind :: KindsOfNames -> AbstractName -> Bool
filterByKind kinds = (`elemKindsOfNames` kinds) . anameKind

-- | Compute all names (first component) and operators/notations
--   (second component) in scope.
--
--   For 'IsPattern', only constructor-like names are returned.
--
localNames :: ExprKind -> Maybe QName -> OperatorScope -> ScopeM ([QName], [NewNotation])
localNames k top opScope@(OpScope _ _ locals) = do
  -- Construct a filter for the names we consider.
  let
    f = case k of
      IsExpr    -> const True
      IsPattern YesDisplayLHS -> const True
        -- #8228: Non-constructor-like operators are useful in DISPLAY
        -- pragmas.
      IsPattern NoDisplayLHS -> let
          -- Andreas, 2025-02-28, issue #7722
          -- Filter by kind.
          -- Just return the constructor-like operators,
          -- otherwise the pattern parser blows up.
          fk = filterByKind (someKindsOfNames $ FldName : conLikeNameKinds)
          -- Filter by name, keeping @top@ in.
          ft = top <&> \ y -> (unqualify y ==) . A.nameConcrete . A.qnameName . anameName
        in applyWhenJust ft (||) fk

  -- Retrieve the names of interest from the flat scope.
  let defs = getDefinedNames' f opScope

  -- Note: Debug printout aligned with the one in
  -- Agda.Syntax.Concrete.Operators.buildParsers.
  reportS "scope.operators" 50
    [ "opScope  = " ++ prettyShow opScope
    , "defs     = " ++ prettyShow defs
    , "locals   = " ++ prettyShow locals
    ]
  let localNots  = map localOp locals
      notLocal   = not . hasElem (map notaName localNots) . notaName
      otherNots  = concatMap (List1.filter notLocal) defs
  return $ second (map useDefaultFixity) $ split $ localNots ++ otherNots
  where
    localOp (x, y) = namesToNotation (QName x) y
    split          = partitionEithers . concatMap opOrNot
    opOrNot n      = Left (notaName n) :
                     [Right n | not (null (notation n))]
