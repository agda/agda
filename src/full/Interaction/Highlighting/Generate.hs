{-# LANGUAGE CPP, Rank2Types #-}

-- | Generates data used for precise syntax highlighting.

module Interaction.Highlighting.Generate
  ( TypeCheckingState(..)
  , generateSyntaxInfo
  , generateErrorInfo
  , tests
  ) where

import Interaction.Highlighting.Precise hiding (tests)
import TypeChecking.Monad hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified TypeChecking.Monad as M
import qualified Syntax.Abstract as A
import qualified Syntax.Concrete as C
import qualified Syntax.Literal as L
import qualified Syntax.Parser.Tokens as T
import qualified Syntax.Position as P
import qualified Syntax.Scope.Base as S
import qualified Syntax.Translation.ConcreteToAbstract as CA
import Control.Monad
import Data.Monoid
import Data.Generics
import Utils.Generics
import Data.Map (Map)
import Data.Sequence (Seq, (><))
import Data.List ((\\))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold (toList, foldMap)

#include "../../undefined.h"

-- | Generates syntax highlighting information for an error,
-- represented as a range and a string.

generateErrorInfo :: P.Range -> String -> File
generateErrorInfo r s =
  several (rToR r) (mempty { otherAspects = [Error], note = Just s })

-- | Has typechecking been done yet?

data TypeCheckingState = TypeCheckingDone | TypeCheckingNotDone
  deriving (Show, Eq)

-- | Generates syntax highlighting information from a 'TopLevelInfo'.
--
-- TODO:
--
-- * Generate highlighting info for comments.
--
-- * It would be nice if module names were highlighted.

generateSyntaxInfo
  :: TypeCheckingState -> [T.Token] -> CA.TopLevelInfo -> TCM File
generateSyntaxInfo tcs toks top = do
  nameInfo <- fmap mconcat $ mapM (generate tcs) (Fold.toList names)
  metaInfo <- if tcs == TypeCheckingNotDone
                 then return mempty
                 else computeUnsolvedMetaWarnings
  -- theRest need to be placed before nameInfo here since record field
  -- declarations contain QNames. tokInfo is placed last since token
  -- highlighting is more crude than the others.
  return (theRest `mappend` nameInfo `mappend` tokInfo `mappend` metaInfo)
  where
    tokInfo = Fold.foldMap tokenToFile toks
      where
      aToF a r = several (rToR r) (mempty { aspect = Just a })

      tokenToFile :: T.Token -> File
      tokenToFile (T.TokSetN (r, _))               = aToF PrimitiveType r
      tokenToFile (T.TokKeyword T.KwSet  r)        = aToF PrimitiveType r
      tokenToFile (T.TokKeyword T.KwProp r)        = aToF PrimitiveType r
      tokenToFile (T.TokKeyword T.KwForall r)      = aToF Symbol r
      tokenToFile (T.TokKeyword _ r)               = aToF Keyword r
      tokenToFile (T.TokSymbol  _ r)               = aToF Symbol r
      tokenToFile (T.TokLiteral (L.LitInt    r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitFloat  r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitString r _)) = aToF String r
      tokenToFile (T.TokLiteral (L.LitChar   r _)) = aToF String r
      tokenToFile (T.TokComment (r, _))            = aToF Comment r
      tokenToFile (T.TokTeX (r, _))                = aToF Comment r
      tokenToFile (T.TokId {})                     = mempty
      tokenToFile (T.TokQId {})                    = mempty
      tokenToFile (T.TokString {})                 = mempty
      tokenToFile (T.TokDummy {})                  = mempty
      tokenToFile (T.TokEOF {})                    = mempty

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

    -- Bound variables, dotted patterns, record fields and module
    -- names.
    theRest = everything' mappend query
      where
      query :: GenericQ File
      query = mempty         `mkQ`
              getFieldDecl   `extQ`
              getVarAndField `extQ`
              getLet         `extQ`
              getLam         `extQ`
              getTyped       `extQ`
              getPattern     `extQ`
              getModuleName

      bound n = nameToFile []
                           (A.nameConcrete n)
                           (\isOp -> mempty { aspect = Just $ Name (Just Bound) isOp })
                           (Just $ A.nameBindingSite n)
      field m n = nameToFile m n
                             (\isOp -> mempty { aspect = Just $ Name (Just Field) isOp })
                             Nothing
      mod n = nameToFile []
                         (A.nameConcrete n)
                         (\isOp -> mempty { aspect = Just $ Name (Just Module) isOp })
                         (Just $ A.nameBindingSite n)

      getVarAndField :: A.Expr -> File
      getVarAndField (A.Var x)    = bound x
      getVarAndField (A.Rec _ fs) = mconcat $ map (field [] . fst) fs
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
      getPattern (A.DotP pi _) =
        several (rToR $ P.getRange pi)
                (mempty { otherAspects = [DottedPattern] })
      getPattern _             = mempty

      getFieldDecl :: A.Definition -> File
      getFieldDecl (A.RecDef _ _ _ fs) = Fold.foldMap extractAxiom fs
        where
        extractAxiom (A.ScopedDecl _ ds) = Fold.foldMap extractAxiom ds
        extractAxiom (A.Axiom _ x _)     = field (concreteQualifier x)
                                                 (concreteBase x)
        extractAxiom _                   = __IMPOSSIBLE__
      getFieldDecl _                   = mempty

      getModuleName :: A.ModuleName -> File
      getModuleName (A.MName { A.mnameToList = xs }) =
        mconcat $ map mod xs

computeUnsolvedMetaWarnings :: TCM File
computeUnsolvedMetaWarnings = do
  is <- getInteractionMetas
  ms <- getOpenMetas
  rs <- mapM getMetaRange (ms \\ is)
  return $ several (concatMap rToR rs)
         $ mempty { otherAspects = [UnsolvedMeta] }

-- | Generates a suitable file for a name.

generate :: TypeCheckingState
            -- ^ Some information can only be generated after type
            -- checking. (This can probably be improved.)
         -> A.QName
         -> TCM File
generate tcs n = do
  mNameKind <- if tcs == TypeCheckingDone then
                fmap (Just . toAspect . theDef) $ getConstInfo n
               else
                return Nothing
  let m isOp = mempty { aspect = Just $ Name mNameKind isOp }
  return (nameToFileA n m)
  where
  toAspect :: Defn -> NameKind
  toAspect (M.Axiom {})       = Postulate
  toAspect (M.Function {})    = Function
  toAspect (M.Datatype {})    = Datatype
  toAspect (M.Record {})      = Record
  toAspect (M.Constructor {}) = Constructor
  toAspect (M.Primitive {})   = Primitive

-- | Converts names to suitable 'File's.

nameToFile :: [C.Name]
              -- ^ The name qualifier (may be empty).
              --
              -- This argument is currently ignored, since the ranges
              -- associated with these names are not to be trusted.
           -> C.Name
              -- ^ The base name.
           -> (Bool -- ^ 'True' iff the name is an operator.
               -> MetaInfo)
              -- ^ Meta information to be associated with the name.
           -> Maybe P.Range
              -- ^ The definition site of the name. The calculated
              -- meta information is extended with this information,
              -- if possible.
           -> File
nameToFile xs x m mR = several rs' ((m isOp) { definitionSite = mFilePos =<< mR })
  where
  (rs, isOp) = getRanges x
  rs'        = rs -- ++ concatMap (fst . getRanges) xs
  mFilePos r = case P.rStart r of
    P.Pn { P.srcFile = f, P.posPos = p } -> Just (f, toInteger p)
    P.NoPos {}                           -> Nothing

-- | A variant of 'nameToFile' for qualified abstract names.

nameToFileA :: A.QName
               -- ^ The name.
            -> (Bool -- ^ 'True' iff the name is an operator.
                -> MetaInfo)
               -- ^ Meta information to be associated with the name.
            -> File
nameToFileA x m =
  nameToFile (concreteQualifier x)
             (concreteBase x)
             m
             (Just $ bindingSite x)

concreteBase      = A.nameConcrete . A.qnameName
concreteQualifier = map A.nameConcrete . A.mnameToList . A.qnameModule
bindingSite       = A.nameBindingSite . A.qnameName

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
