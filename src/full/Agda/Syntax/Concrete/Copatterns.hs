{-# LANGUAGE CPP #-}

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

  Syntax.Concrete.LHSCore represents a lhs
   - the destructor path
   - the side patterns
   - the defined function symbol
   - the applied patterns
-}
module Agda.Syntax.Concrete.Copatterns where

import Control.Applicative
import Control.Monad

import Data.Either
import qualified Data.Traversable as Trav

import Agda.Utils.Either
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Operators
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad.Base (typeError, TypeError(..))
import Agda.TypeChecking.Monad.State (getScope)

#include "../../undefined.h"
import Agda.Utils.Impossible


-- | Parses a left-hand side, and makes sure that it defined the expected name.
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--      Assume _ * is a constructor. Then 'true *' can be parsed as either the
--      intended _* applied to true, or as true applied to a variable *. If we
--      check arities this problem won't appear.

parseLHS :: Name -> Pattern -> ScopeM LHSCore
parseLHS top p = do
    patP <- buildParser (getRange p) DontUseBoundNames
    cons <- getNames [ConName]
    flds <- getNames [FldName]
    case [ res | p' <- parsePat patP p
               , res <- validPattern (PatternCheckConfig top cons flds) p' ] of
        [(p,lhs)] -> return lhs
        []    -> typeError $ NoParseForLHS p
        rs  -> typeError $ AmbiguousParseForLHS p $ map (fullParen . fst) rs
    where
        getNames kinds = map fst <$> getDefinedNames kinds

        -- validPattern returns an empty or singleton list (morally a Maybe)
        validPattern :: PatternCheckConfig -> Pattern -> [(Pattern, LHSCore)]
        validPattern conf p = case classifyPattern conf p of
            Nothing -> []
            Just (Left p) -> []
            Just (Right lhscore) -> [(p,lhscore)]


{-
        appView :: Pattern -> [Pattern]
        appView p = case p of
            AppP p a         -> appView p ++ [namedThing (unArg a)]
            OpAppP _ op ps   -> IdentP (QName op) : ps
            ParenP _ p       -> appView p
            RawAppP _ _      -> __IMPOSSIBLE__
            HiddenP _ _      -> __IMPOSSIBLE__
            InstanceP _ _    -> __IMPOSSIBLE__
            _                -> [p]
-}

-- | Name sets for classifying a pattern.
data PatternCheckConfig = PatternCheckConfig
  { topName  :: Name   -- ^ name of defined symbol
  , conNames :: [Name] -- ^ valid constructor names
  , fldNames :: [Name] -- ^ valid field names
  }

type Pattern' = Either Pattern LHSCore

-- | Returns zero or one classified patterns.
classifyPattern :: PatternCheckConfig -> Pattern -> Maybe Pattern'
classifyPattern conf p =
  case patternAppView p of

    -- case @f ps@
    Arg _ _ (Named _ (IdentP (QName x))) : ps | x == topName conf ->
      if all validPat ps then Just (Right (LHSHead x ps)) else Nothing

    -- case @d ps@
    Arg _ _ (Named _ (IdentP x)) : ps0 | unqualify x `elem` fldNames conf -> do
      -- ps :: [NamedArg Pattern']
      ps <- mapM classPat ps0
      let (ps1, rest) = span (isLeft . namedThing . unArg) ps
      when (null rest) Nothing -- no field pattern or def pattern found
      let (p2:ps3) = rest
      if all (isLeft . namedThing . unArg) ps3 then
         Just $ Right $ -- LHSProj x (lefts ps1) p2 (lefts ps3)
           LHSProj x (take (length ps1) ps0) (fromR p2) (drop (1 + length ps1) ps0)
       else Nothing

    _ -> if validConPattern (conNames conf) p then Just $ Left p else Nothing

{-
    -- case @c ps@
    Arg _ _ (Named _ (IdentP x)) : ps | unqualify x `elem` conNames conf ->
      if all validPat ps then Just (Left p) else Nothing

    -- case not a valid pattern
    _ -> Nothing
-}

  where validPat = validConPattern (conNames conf) . namedThing . unArg
        classPat :: NamedArg Pattern -> Maybe (NamedArg Pattern')
        classPat = Trav.mapM (Trav.mapM (classifyPattern conf))
        fromR :: NamedArg (Either a b) -> NamedArg b
        fromR (Arg h r (Named n (Right b))) = Arg h r (Named n b)
        fromR (Arg h r (Named n (Left  a))) = __IMPOSSIBLE__

{-
type NPatterns = [NamedArg Pattern]

data Pattern'
  = ConPattern Name NPatterns  -- ^ @c ps@
  | FldPattern Name NPatterns (NamedArg Pattern') NPatterns -- ^ @d ps'@ at most one pattern in @ps'@ not a 'ConPattern'
  | DefPattern Name NPatterns  -- ^ @f ps@

isConPattern :: Pattern' -> Bool
isConPattern (ConPattern{}) = True
isConPattern _ = False

-- | Returns zero or one classified patterns.
classifyPattern :: PatternCheckConfig -> Pattern -> Maybe Pattern'
classifyPattern conf p =
  case patternAppView p of

    -- case @f ps@
    Arg _ _ (Named _ (IdentP (QName x))) : ps | x == topName conf ->
      if all validPat ps then Just (DefPattern x ps) else Nothing

    -- case @d ps@
    Arg _ _ (Named _ (IdentP (QName x))) : ps0 | x `elem` fldNames conf -> do
      -- ps :: [NamedArg Pattern']
      ps <- mapM classPat ps0
      let (ps1, rest) = span (isConPattern . namedThing . unArg) ps
      when (null rest) Nothing -- no field pattern or def pattern found
      let (p2:ps3) = rest
      if all (isConPattern . namedThing . unArg) ps3 then
         return $ FldPattern x (take (length ps1) ps0) p2 (drop (1 + length ps1) ps0)
       else Nothing

    -- case @c ps@
    Arg _ _ (Named _ (IdentP (QName x))) : ps | x `elem` conNames conf ->
      if all validPat ps then Just (ConPattern x ps) else Nothing

    -- case not a valid pattern
    _ -> Nothing

  where validPat = validConPattern (conNames conf) . namedThing . unArg
        classPat :: NamedArg Pattern -> Maybe (NamedArg Pattern')
        classPat = Trav.mapM (Trav.mapM (classifyPattern conf))
-}

{-
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

-}
