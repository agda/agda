{-# LANGUAGE CPP, Rank2Types #-}

-- | Generates data used for precise syntax highlighting.

module Interaction.Highlighting.Generate
  ( generateSyntaxInfo
  , generateErrorInfo
  , tests
  ) where

import Interaction.Highlighting.Precise hiding (tests)
import qualified TypeChecking.Monad as M
import qualified Syntax.Abstract as A
import qualified Syntax.Concrete as C
import qualified Syntax.Literal as L
import qualified Syntax.Parser.Tokens as T
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

-- | Generates syntax highlighting information for an error,
-- represented as a range and a string. Also returns the file
-- containing the error, if any.

generateErrorInfo :: P.Range -> String -> (Maybe FilePath, File)
generateErrorInfo r s = (mFile, m)
  where
  mFile = case P.rStart r of
            P.Pn { P.srcFile = file } -> Just file
            P.NoPos                   -> Nothing
  m = several (rToR r) (empty { aspect = Just Error, note = Just s })

-- | Generates syntax highlighting information from a 'TopLevelInfo'.
--
-- TODO:
--
-- * Generate highlighting info for comments.
--
-- * It would be nice if module names were highlighted.

generateSyntaxInfo :: [T.Token] -> CA.TopLevelInfo -> M.TCM File
generateSyntaxInfo toks top = do
  nameInfo <- fmap mconcat $ mapM generate (Seq.toList names)
  -- theRest need to be placed before nameInfo here since record field
  -- declarations contain QNames.
  return (tokInfo `mappend` theRest `mappend` nameInfo)
  where
    tokInfo = Seq.foldMap tokenToFile toks
      where
      aToF a r = several (rToR r) (empty { aspect = Just a })

      tokenToFile :: T.Token -> File
      tokenToFile (T.TokKeyword _ r)               = aToF Keyword r
      tokenToFile (T.TokSetN (r, _))               = aToF Keyword r
      tokenToFile (T.TokLiteral (L.LitInt    r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitFloat  r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitString r _)) = aToF String r
      tokenToFile (T.TokLiteral (L.LitChar   r _)) = aToF String r
      tokenToFile _                                = mempty

    everything' :: (r -> r -> r) -> GenericQ r -> r
    everything' (+) q = everythingBut
                          (+)
                          (False `mkQ` isString
                                 `extQ` isAQName `extQ` isAName `extQ` isCName
                                 `extQ` isScope `extQ` isMap1 `extQ` isMap2)
                          q
                          (CA.topLevelDecls top)
      where
      isString :: String                        -> Bool
      isAQName :: A.QName                       -> Bool
      isAName  :: A.Name                        -> Bool
      isCName  :: C.Name                        -> Bool
      isScope  :: S.ScopeInfo                   -> Bool
      isMap1   :: Map A.QName A.QName           -> Bool
      isMap2   :: Map A.ModuleName A.ModuleName -> Bool

      isString = const True
      isAQName = const True
      isAName  = const True
      isCName  = const True
      isScope  = const True
      isMap1   = const True
      isMap2   = const True

    -- All names mentioned in the syntax tree (not bound variables).
    names = everything' (><) (Seq.empty `mkQ` getName)
      where
      getName :: A.QName -> Seq A.QName
      getName n = Seq.singleton n

    -- Bound variables, dotted patterns and record fields.
    theRest = everything' mappend query
      where
      query :: GenericQ File
      query = mempty         `mkQ`
              getFieldDecl   `extQ`
              getVarAndField `extQ`
              getLet         `extQ`
              getLam         `extQ`
              getTyped       `extQ`
              getPattern

      bound = nameToFile (\isOp -> empty { aspect = Just $ Name Bound isOp })
            . A.nameConcrete
      field = nameToFile (\isOp -> empty { aspect = Just $ Name Field isOp })

      getVarAndField :: A.Expr -> File
      getVarAndField (A.Var x)    = bound x
      getVarAndField (A.Rec _ fs) = mconcat $ map (field . fst) fs
      getVarAndField _            = mempty

      getLet :: A.LetBinding -> File
      getLet (A.LetBind _ x _ _) = bound x

      getLam :: A.LamBinding -> File
      getLam (A.DomainFree _ x) = bound x
      getLam (A.DomainFull {})  = mempty

      getTyped :: A.TypedBinding -> File
      getTyped (A.TBind _ xs _) = mconcat $ map bound xs
      getTyped (A.TNoBind {})   = mempty

      getPattern :: A.Pattern -> File
      getPattern (A.VarP x)    = bound x
      getPattern (A.AsP _ x _) = bound x
      getPattern (A.DotP pi _) = several (rToR $ P.getRange pi)
                                         (empty { dotted = True })
      getPattern _             = mempty

      getFieldDecl :: A.Definition -> File
      getFieldDecl (A.RecDef _ _ _ fs) = Seq.foldMap extractAxiom fs
        where
        extractAxiom (A.ScopedDecl _ ds) = Seq.foldMap extractAxiom ds
        extractAxiom (A.Axiom _ x _)     = field $ A.nameConcrete $ A.qnameName x
        extractAxiom _                   = __IMPOSSIBLE__
      getFieldDecl _                   = mempty

-- | Generates a suitable file for a name.

generate :: A.QName -> M.TCM File
generate n = do
  info <- M.getConstInfo n
  let mFilePos = case P.rStart $ P.getRange $ M.defName info of
        P.Pn { P.srcFile = f, P.posPos = p } -> Just (f, toInteger p)
        P.NoPos {}                           -> Nothing
      m isOp = empty { aspect = Just $ Name (toAspect (M.theDef info)) isOp
                     , definitionSite = mFilePos
                     }
  return (nameToFile m (A.nameConcrete $ A.qnameName n))
  where
  toAspect :: M.Defn -> NameKind
  toAspect (M.Axiom {})       = Postulate
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
