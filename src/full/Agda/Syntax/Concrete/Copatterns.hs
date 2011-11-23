{- Implement parsing of copattern left hand sides, e.g.

  record Tree (A : Set) : Set where
    field
      label : A
      child : Bool -> Tree A

  -- corecursive function defined by copattern matching
  alternate : {A : Set}(a b : A) -> Tree A
  -- shallow copatterns
               child True  (alternate a b) = alternate b a
               label       (alternate a b) = a
  -- deep copatterns:
  label       (child False (alternate a b)) = b
  child True  (child False (alternate a b)) = alternate a b
  child False (child False (alternate a b)) = alternate a b

  Delivers an infinite tree

                   a
              b        b
            a   a    a   a
           b b b b  b b b b
                 ...

  Each lhs is a pattern tree with a distinct path of destructors
  ("child", "label") from the root to the defined symbol ("alternate").
  All branches besides this distinct path are patterns.

-}
module Copatterns where

import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Name

{- The following data structure represents a lhs
   - the destructor path
   - the side patterns
   - the defined function symbol
   - the applied patterns
-}

-- | The left hand side of an equation with copatterns.
data LHS
  = Head     { definedFunctionSymbol :: QName -- ^ @f@
             , argPatterns :: [Pattern]       -- ^ @ps@
             }
  | Destruct { destructor    :: QName      -- ^ record projection identifier
             , patternsLeft  :: [Pattern]  -- ^ side patterns
             , focus         :: LHS        -- ^ main branch
             , patternsRight :: [Pattern]  -- ^ side patterns
             }

-- | Parses a left-hand side, and makes sure that it defined the expected name.
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--      Assume _ * is a constructor. Then 'true *' can be parsed as either the
--      intended _* applied to true, or as true applied to a variable *. If we
--      check arities this problem won't appear.
parseLHS :: Name -> Pattern -> ScopeM LHS
parseLHS top p = do
    patP <- buildParser (getRange p) DontUseBoundNames
    dest <- getNames [FieldName]
    cons <- getNames [ConName]
    case filter (validPattern top cons) $ parsePattern patP p of
        [p] -> return p
        []  -> typeError $ NoParseForLHS p
        ps  -> typeError $ AmbiguousParseForLHS p $ map fullParen ps
    where
        getNames kinds = map fst <$> getDefinedNames kinds

        validPattern :: Maybe Name -> [Name] -> Pattern -> Bool
        validPattern (Just top) cons p = case appView p of
            IdentP (QName x) : ps -> x == top && all (validPat cons) ps
            _                     -> False
        validPattern Nothing cons p = validPat cons p

        validPat :: [Name] -> Pattern -> Bool
        validPat cons p = case appView p of
            [_]                   -> True
            IdentP (QName x) : ps -> elem x cons && all (validPat cons) ps
            ps                    -> all (validPat cons) ps

        appView :: Pattern -> [Pattern]
        appView p = case p of
            AppP p a         -> appView p ++ [namedThing (unArg a)]
            OpAppP _ op ps   -> IdentP (QName op) : ps
            ParenP _ p       -> appView p
            RawAppP _ _      -> __IMPOSSIBLE__
            HiddenP _ _      -> __IMPOSSIBLE__
            InstanceP _ _    -> __IMPOSSIBLE__
            _                -> [p]

