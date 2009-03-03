{-# LANGUAGE TypeSynonymInstances #-}

module Tags where

import Data.List
import Data.Maybe
import Data.Map (Map, (!))
import qualified Data.Map as Map

import HsSyn
import SrcLoc
import RdrName
import OccName
import qualified Name
import FastString
import Bag

data Pos = Pos { line, column :: Int }
           deriving (Eq, Ord)

data Tag = NoLoc String
         | Tag String FilePath Pos
  deriving (Eq, Ord)

-- | Takes a list of (filename, file contents, tags) and generates
-- text for an etags file.

-- I found the etags file format on Wikipedia; I have not found an
-- authoritative definition of it.
--
-- For every file containing tags a section is generated.
-- Section header (two lines):
--   \x0c
--   <file name>,<size of the following lines in bytes>
-- This is followed by one line for every tag:
--   <text from start of line to end of tag>\x7f
--   <tag name>\x01
--   <line number>,<some form of offset in bytes>

showETags :: [(FilePath, String, [Tag])] -> String
showETags = concatMap showFile
  where
  showFile (f, contents, ts) =
    unlines ["\x0c", f ++ "," ++ show bytes] ++ ts'
    where
    ts' = unlines $ catMaybes $ map showTag ts

    -- TODO: This should be the length in _bytes_ of ts'. However,
    -- since the rest of this program seems to assume an 8-bit
    -- character encoding I just count the number of characters.
    bytes = length ts'

    lineMap = Map.fromList $ zip [1..] (lines contents)

    showTag (NoLoc _)   = Nothing
    showTag (Tag t f p) = Just $
      take (column p) (lineMap ! line p) ++ t ++ "\x7f" ++
      t ++ "\x01" ++
      show (line p) ++ ",0"
      -- I don't know what the last offset is used for, so I have set
      -- it to 0. This seems to work.

instance Show Tag where
  show (Tag t f p) = intercalate "\t" [t, f, show (line p)]
  show (NoLoc t)   = unwords [t, ".", "0"]

srcLocTag :: SrcLoc -> Tag -> Tag
srcLocTag l (NoLoc t) = Tag t
                            (unpackFS $ srcLocFile l)
                            (Pos { line   = srcLocLine l
                                 , column = srcLocCol l
                                 })
srcLocTag _ t@Tag{}   = t

class TagName a where
  tagName :: a -> String

instance TagName RdrName where
  tagName x = case x of
    Unqual x  -> tagName x
    Qual _ x  -> tagName x
    Orig _ x  -> tagName x
    Exact x   -> tagName x

instance TagName OccName where
  tagName = unpackFS . occNameFS

instance TagName Name.Name where
  tagName = tagName . Name.nameOccName

class HasTags a where
  tags :: a -> [Tag]

instance HasTags Tag where
  tags x = [x]

instance HasTags a => HasTags [a] where
  tags = concatMap tags

instance (HasTags a, HasTags b) => HasTags (a, b) where
  tags (x, y) = tags x ++ tags y

instance HasTags a => HasTags (Maybe a) where
  tags = maybe [] tags

instance HasTags a => HasTags (Bag a) where
  tags = tags . bagToList

instance HasTags a => HasTags (Located a) where
  tags (L l x) = map (srcLocTag $ srcSpanStart l) $ tags x

newtype Name a = Name a
instance TagName name => HasTags (Name name) where
  tags (Name x) = [NoLoc $ tagName x]

tagsLN :: TagName name => Located name -> [Tag]
tagsLN = tags . fmap Name

tagsN :: TagName name => name -> [Tag]
tagsN = tags . Name

instance TagName name => HasTags (HsModule name) where
  tags (HsModule _ export _ decls _ _ _) = tags decls -- TODO: filter exports

instance TagName name => HasTags (HsDecl name) where
  tags d = case d of
    TyClD d   -> tags d
    ValD d    -> tags d
    SigD d    -> tags d
    ForD d    -> tags d
    DocD _    -> []
    SpliceD _ -> []
    RuleD _   -> []
--    DeprecD _ -> []
    DefD _    -> []
    InstD _   -> []
    DerivD _  -> []

instance TagName name => HasTags (TyClDecl name) where
  tags d = tagsLN (tcdLName d) ++
    case d of
      TyData { tcdCons = cons } -> tags cons
      ClassDecl { tcdSigs = meths
                , tcdATs  = ats
                } -> tags (meths, ats)
      _ -> []

instance TagName name => HasTags (ConDecl name) where
  tags d = tagsLN (con_name d) ++ tags (con_details d)

instance TagName name => HasTags (ConDeclField name) where
  tags (ConDeclField x _ _) = tagsLN x

-- Dummy instance.
instance HasTags (HsType name) where
  tags _ = []

instance TagName name => HasTags (HsBind name) where
  tags d = case d of
    FunBind  { fun_id    = x   } -> tagsLN x
    PatBind  { pat_lhs   = lhs } -> tags lhs
    VarBind  { var_id    = x   } -> tagsN x
    AbsBinds { abs_binds = bs  } -> tags bs

instance TagName name => HasTags (Pat name) where
  tags p = case p of
    VarPat x               -> tagsN x
    VarPatOut x _          -> tagsN x
    LazyPat p              -> tags p
    AsPat x p              -> tags (fmap Name x, p)
    ParPat p               -> tags p
    BangPat p              -> tags p
    ListPat ps _           -> tags ps
    TuplePat ps _ _        -> tags ps
    PArrPat ps _           -> tags ps
    ConPatIn _ ps          -> tags ps
    ConPatOut _ _ _ _ ps _ -> tags ps
    NPlusKPat x _ _ _      -> tagsLN x
    SigPatIn p _           -> tags p
    SigPatOut p _          -> tags p
    CoPat{}                -> []
    TypePat{}              -> []
    NPat{}                 -> []
    LitPat{}               -> []
    WildPat{}              -> []

instance (HasTags arg, HasTags rec) => HasTags (HsConDetails arg rec) where
  tags d = case d of
    PrefixCon as   -> tags as
    RecCon r       -> tags r
    InfixCon a1 a2 -> tags [a1, a2]

instance HasTags arg => HasTags (HsRecFields name arg) where
  tags (HsRecFields fs _) = tags fs

instance HasTags arg => HasTags (HsRecField name arg) where
  tags (HsRecField _ a _) = tags a

instance TagName name => HasTags (Sig name) where
  tags d = case d of
    TypeSig x _   -> tagsLN x
    FixSig{}      -> []
    InlineSig{}   -> []
    SpecSig{}     -> []
    SpecInstSig{} -> []

instance TagName name => HasTags (ForeignDecl name) where
  tags d = case d of
    ForeignImport x _ _ -> tagsLN x
    ForeignExport _ _ _ -> []

