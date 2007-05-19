{-# LANGUAGE CPP #-}

-- | Generates data used for precise syntax highlighting.

module Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , tests
  ) where

import Interaction.Highlighting.Precise hiding (tests)
import qualified TypeChecking.Monad as M
import qualified Syntax.Abstract as A
import qualified Syntax.Concrete as C
import qualified Syntax.Position as P
import qualified Syntax.Scope.Base as S
import qualified Syntax.Translation.ConcreteToAbstract as CA
import Data.Monoid
import Data.Generics
import Utils.Generics
import Data.Map (Map)
import Data.Sequence (Seq, (><))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Seq (toList, foldMap)

#include "../../undefined.h"

-- | Generates syntax highlighting information from a 'TopLevelInfo'.
--
-- TODO:
--
-- * Generate highlighting info for comments, keywords, strings and
--   numbers. This should be done by examining the token stream from
--   the lexer.
--
-- * It would be nice if module names were highlighted.

generateSyntaxInfo :: CA.TopLevelInfo -> M.TCM File
generateSyntaxInfo top = do
  nameInfo <- fmap mconcat $ mapM generate (Seq.toList names)
  -- fields need to be placed before nameInfo here since record field
  -- declarations contain QNames.
  return (fields `mappend` nameInfo `mappend` dotted `mappend` bound)
  where
    decls = CA.topLevelDecls top

    everything' (+) = everythingBut (+)
                        (False `mkQ` isScope `extQ` isMap1 `extQ` isMap2)
      where
      isScope :: S.ScopeInfo                   -> Bool
      isMap1  :: Map A.QName A.QName           -> Bool
      isMap2  :: Map A.ModuleName A.ModuleName -> Bool

      isScope = const True
      isMap1  = const True
      isMap2  = const True

    -- All names mentioned in the syntax tree (not bound variables).
    names = everything' (><) (Seq.empty `mkQ` getName) decls
      where
      getName :: A.QName -> Seq A.QName
      getName n = Seq.singleton n

    -- Bound variables.
    bound = everything' mappend query decls
      where
      query :: GenericQ File
      query = mempty `mkQ`
              getVar `extQ` getLet `extQ` getLam
                     `extQ` getTyped `extQ` getPattern

      toF = nameToFile (\isOp -> empty { aspect = Just $ Name Bound isOp })
            . A.nameConcrete

      getVar (A.Var x) = toF x
      getVar _         = mempty

      getLet (A.LetBind _ x _ _) = toF x

      getLam (A.DomainFree _ x) = toF x
      getLam (A.DomainFull {})  = mempty

      getTyped (A.TBind _ xs _) = mconcat $ map toF xs
      getTyped (A.TNoBind {})   = mempty
      getPattern :: A.Pattern -> File
      getPattern (A.VarP x)    = toF x
      getPattern (A.AsP _ x _) = toF x
      getPattern _             = mempty

    -- Every dotted pattern.
    dotted = everything' mappend (mempty `mkQ` getDotted) decls
      where
      getDotted :: A.Pattern -> File
      getDotted (A.DotP pi _) = several (rToR $ P.getRange pi)
                                        (empty { dotted = True })
      getDotted _             = mempty

    -- Record fields.
    fields = everything' mappend (mempty `mkQ` getField `extQ` getFieldDecl) decls
      where
      toF = nameToFile (\isOp -> empty { aspect = Just $ Name Field isOp })

      getField :: A.Expr -> File
      getField (A.Rec _ fs) = mconcat $ map (toF . fst) fs
      getField _            = mempty

      getFieldDecl :: A.Definition -> File
      getFieldDecl (A.RecDef _ _ _ fs) = Seq.foldMap extractAxiom fs
        where
        extractAxiom (A.ScopedDecl _ ds) = Seq.foldMap extractAxiom ds
        extractAxiom (A.Axiom _ x _)     = toF $ A.nameConcrete $ A.qnameName x
        extractAxiom _                   = __IMPOSSIBLE__
      getFieldDecl _                   = mempty

-- | Generates a suitable file for a name.

generate :: A.QName -> M.TCM File
generate n = do
  info <- M.getConstInfo n
  let m isOp = empty { aspect = Just $ Name (toAspect (M.theDef info)) isOp }
  return (nameToFile m (A.nameConcrete $ A.qnameName n))
  where
  toAspect :: M.Defn -> NameKind
  toAspect M.Axiom            = Postulate
  toAspect (M.Function {})    = Function
  toAspect (M.Datatype {})    = Datatype
  toAspect (M.Record {})      = Record
  toAspect (M.Constructor {}) = Constructor
  toAspect (M.Primitive {})   = Primitive

-- | @'nameToFile' m x@ constructs a 'File' by associating the
-- 'MetaInfo' calculated by @m@ to the ranges associated with the name
-- @x@ (see 'getRanges').

nameToFile :: (Bool -- ^ 'True' iff the name (next argument) is an operator.
               -> MetaInfo)
           -> C.Name
           -> File
nameToFile m x = several rs (m isOp)
  where (rs, isOp) = getRanges x

-- | Calculates a set of ranges associated with a name.
--
-- For an operator the ranges associated with the NameParts are
-- returned. Otherwise the range associated with the Name is returned.
--
-- A boolean, indicating operatorness, is also returned.

getRanges :: C.Name -> ([Range], Bool)
getRanges (C.NoName _ _) = ([], False)
getRanges (C.Name r ps)  =
  if r == P.noRange then (concatMap getR ps, True)
                    else (rToR r, False)
  where
  getR C.Hole     = []
  getR (C.Id r _) = rToR r

-- | Converts a 'P.Range' to a 'Range' (if the input range has
-- well-defined positions).

rToR :: P.Range -> [Range]
rToR r = case (p1, p2) of
  (P.Pn { P.posPos = pos1 }, P.Pn { P.posPos = pos2 }) ->
    [Range { from = toInteger pos1, to = toInteger pos2 }]
  _ -> []
  where
  p1 = P.rStart r
  p2 = P.rEnd r

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  return ()
