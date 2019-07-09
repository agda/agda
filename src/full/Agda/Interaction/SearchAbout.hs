module Agda.Interaction.SearchAbout (findMentions) where

import Control.Monad

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (isInfixOf)
import Data.Either (partitionEithers)
import Data.Foldable (toList)

import Agda.Syntax.Position (Range)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Env
import Agda.Syntax.Internal.Names (namesIn)
import Agda.Interaction.BasicOps (normalForm, Rewrite, parseName)

import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Internal as I

import Agda.Utils.Pretty ( prettyShow )

findMentions :: Rewrite -> Range -> String -> ScopeM [(C.Name, I.Type)]
findMentions norm rg nm = do
  -- We start by dealing with the user's input

  -- The users passes in `nm`, a list of identifiers and strings
  -- to match against definitions in scope. `findMentions` will
  -- select all of the definitions such that:
  -- - all of the specified identifiers appear in their type
  --   (which has been normalised according to `norm`)
  -- - all of the specified strings are substrings of their name

  -- We separate the strings from the names by a rough analysis
  -- and then parse and resolve the names in the current scope
  let (userSubStrings, nms) = partitionEithers $ isString <$> words nm
  rnms <- mapM (parseName rg >=> resolveName) nms
  let userIdentifiers = fmap (fmap anameName . anames) rnms

  -- We then collect all the things in scope, by name.
  -- Issue #2381: We explicitly filter out pattern synonyms because they
  -- don't have a type. Looking it up makes Agda panic!
  snms <- fmap (nsNames . allThingsInScope) $ currentModule >>= getNamedScope
  let namesInScope = filter ((PatternSynName /=) . anameKind . snd)
                   $ concatMap (uncurry $ map . (,)) $ Map.toList snms

  -- Once we have the user-provided names and the names of all the
  -- thing in scope we can start the search: for each name in scope,
  -- we grab its type, normalise it according to `norm` and collect
  -- the identifiers in it. We then check whether it meets the user's
  -- criteria.
  ress <- forM namesInScope $ \ (x, n) -> do
    t <- normalForm norm =<< typeOfConst (anameName n)
    let namesInT = Set.toList $ namesIn t
    let defName  = prettyShow x
    return $ do
      guard $ all (`isInfixOf` defName)   userSubStrings
      guard $ all (any (`elem` namesInT)) userIdentifiers
      return (x, t)
  return $ concat ress

  where
    isString str
      |  not (null str)
      && head str == '"'
      && last str == '"' = Left $ filter (/= '"') str
      | otherwise        = Right str

    anames (DefinedName _ an)     = [an]
    anames (FieldName     ans)    = toList ans
    anames (ConstructorName ans)  = toList ans
    anames _                      = []
