{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Tags where

import Data.Function
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import HsSyn
import SrcLoc
import RdrName
import OccName
import qualified Name
import FastString
import Bag
import qualified BasicTypes

data Pos = Pos { line, column :: Int }
           deriving (Eq, Ord)

data Tag = NoLoc String
         | Tag String FilePath Pos
  deriving (Eq, Ord)

-- | Removes duplicate /adjacent/ tags, ignoring the 'Pos' field.

removeDuplicates :: [Tag] -> [Tag]
removeDuplicates = map head . groupBy ((==) `on` everythingButPos)
  where
  dummyPos = Pos 0 0

  everythingButPos (Tag s f p) = Tag s f dummyPos
  everythingButPos t@NoLoc {}  = t

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
    ts' = unlines $ mapMaybe showTag ts

    -- TODO: This should be the length in _bytes_ of ts'. However,
    -- since the rest of this program seems to assume an 8-bit
    -- character encoding I just count the number of characters.
    bytes = length ts'

    lineMap = Map.fromList $ zip [1..] (lines contents)

    showTag (NoLoc _)   = Nothing
    showTag (Tag t f p) = Just $
      take' (column p) (lineMap ! line p) ++ t ++ "\x7f" ++
      t ++ "\x01" ++
      show (line p) ++ ",0"
      -- I don't know what the last offset is used for, so I have set
      -- it to 0. This seems to work.

    take' = tabAwareTake 0
    m ! k = Map.findWithDefault (error $ "Cannot find line " ++ show k ++ " in lineMap") k m

    -- A variant of take which is aware of tab characters. Uses tab
    -- size 8, and only recognises the ordinary ASCII horizontal tab
    -- ('\t'). The first argument is the position of the first
    -- character. Tabs are only expanded into spaces if necessary.
    tabAwareTake pos n s | n <= 0 = ""
    tabAwareTake pos n ""         = ""
    tabAwareTake pos n (c : s)
      | c /= '\t'    = c : tabAwareTake (pos + 1) (n - 1) s
      | stepSize > n = replicate n ' '
      | otherwise    = c : tabAwareTake nextTabStop (n - stepSize) s
      where
      tabSize     = 8
      nextTabStop = (pos `div` tabSize + 1) * tabSize
      stepSize    = nextTabStop - pos

instance Show Tag where
  show (Tag t f p) = intercalate "\t" [t, f, show (line p)]
  show (NoLoc t)   = unwords [t, ".", "0"]

srcLocTag :: SrcLoc -> Tag -> Tag
srcLocTag UnhelpfulLoc{} t         = t
srcLocTag (RealSrcLoc l) (NoLoc t) =
  Tag t
      (unpackFS $ srcLocFile l)
      Pos { line   = srcLocLine l
            -- GHC 7 counts columns starting from 1.
          , column = srcLocCol l - 1
          }
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

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => TagName (FieldOcc pass) where
#else
instance TagName a => TagName (FieldOcc a) where
#endif
#if MIN_VERSION_ghc(8,6,1)
  tagName (FieldOcc _ (L _ rdrName)) = tagName rdrName
  tagName (XFieldOcc _)              = missingImp "XFieldOcc"
#else
  tagName (FieldOcc (L _ rdrName) _) = tagName rdrName
#endif

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

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (HsModule pass) where
#else
instance TagName name => HasTags (HsModule name) where
#endif
  tags HsModule{ hsmodExports = export
               , hsmodDecls   = decls
               } = tags decls -- TODO: filter exports

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (HsDecl pass) where
#else
instance TagName name => HasTags (HsDecl name) where
#endif
  tags d = case d of
#if MIN_VERSION_ghc(8,6,1)
    TyClD _ d     -> tags d
    ValD _ d      -> tags d
    SigD _ d      -> tags d
    ForD _ d      -> tags d
    XHsDecl _     -> []
#else
    TyClD d       -> tags d
    ValD d        -> tags d
    SigD d        -> tags d
    ForD d        -> tags d
#endif
    DocD{}        -> []
    SpliceD{}     -> []
    RuleD{}       -> []
    DefD{}        -> []
    InstD{}       -> []
    DerivD{}      -> []
    WarningD{}    -> []
    AnnD{}        -> []
    RoleAnnotD{}  -> []
#if !MIN_VERSION_ghc(8,6,1)
    VectD{}       -> []
#endif


#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (FamilyDecl pass) where
#else
instance TagName name => HasTags (FamilyDecl name) where
#endif
  tags d = tagsLN (fdLName d)

instance HasTags (BasicTypes.Origin) where
  tags _ = []

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (TyClDecl pass) where
#else
instance TagName name => HasTags (TyClDecl name) where
#endif
#if MIN_VERSION_ghc(8,6,1)
  tags (FamDecl _ d) = tags d
#else
  tags (FamDecl d) = tags d
#endif
  tags d = tagsLN (tcdLName d) ++
    case d of
      DataDecl { tcdDataDefn = HsDataDefn { dd_cons = cons } }
        -> tags cons
      ClassDecl { tcdSigs = meths
                , tcdATs  = ats
                } -> tags (meths, ats)
      _ -> []

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (ConDecl pass) where
#else
instance TagName name => HasTags (ConDecl name) where
#endif
#if MIN_VERSION_ghc(8,6,1)
    tags (ConDeclGADT _ cns _ _ _ _ _ _) = concatMap tagsLN cns
    tags (ConDeclH98 _ cn _ _ _ cd _)    = tagsLN cn ++ tags cd
    tags (XConDecl _)                    = missingImp "XConDecl"
#else
  tags (ConDeclGADT cns _ _)    = concatMap tagsLN cns
  tags (ConDeclH98 cn _ _ cd _) = tagsLN cn ++ tags cd
#endif

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (ConDeclField pass) where
#else
instance TagName name => HasTags (ConDeclField name) where
#endif
#if MIN_VERSION_ghc(8,6,1)
  tags (ConDeclField _ x _ _) = concatMap tagsLN x
  tags (XConDeclField _)      = missingImp "XConDeclField"
#else
  tags (ConDeclField x _ _) = concatMap tagsLN x
#endif

-- Dummy instance.
instance HasTags (HsType name) where
  tags _ = []

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (HsBind pass) where
#else
instance TagName name => HasTags (HsBind name) where
#endif
  tags d = case d of
    FunBind  { fun_id    = x   }      -> tagsLN x
    PatBind  { pat_lhs   = lhs }      -> tags lhs
    VarBind  { var_id    = x   }      -> tagsN x
    AbsBinds { abs_binds = bs  }      -> tags bs
#if !MIN_VERSION_ghc(8,4,1)
    AbsBindsSig { abs_sig_bind = bs } -> tags bs
#endif
#if MIN_VERSION_ghc(8,6,1)
    PatSynBind _ (PSB { psb_id = x }) -> tagsLN x
    PatSynBind _ XPatSynBind{}        -> missingImp "XPatSynBindPSB"
    XHsBindsLR{}                      -> missingImp "XHsBindsLR"
#else
    PatSynBind (PSB { psb_id = x }) -> tagsLN x
#endif


#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (Pat pass) where
#else
instance TagName name => HasTags (Pat name) where
#endif
  tags p = case p of
#if MIN_VERSION_ghc(8,6,1)
    VarPat _ x                 -> tagsLN x
#else
    VarPat x                   -> tagsLN x
#endif
#if MIN_VERSION_ghc(8,6,1)
    LazyPat _ p                -> tags p
    AsPat _ x p                -> tags (fmap Name x, p)
    ParPat _ p                 -> tags p
    BangPat _ p                -> tags p
    ListPat _ ps               -> tags ps
    TuplePat _ ps _            -> tags ps
    SigPat _ p                 -> tags p
    XPat _                     -> missingImp "XPat"
#else
    LazyPat p                  -> tags p
    AsPat x p                  -> tags (fmap Name x, p)
    ParPat p                   -> tags p
    BangPat p                  -> tags p
    ListPat ps _ _             -> tags ps
    TuplePat ps _ _            -> tags ps
    SigPatIn p _               -> tags p
    SigPatOut p _              -> tags p
    PArrPat ps _               -> tags ps
#endif
    ConPatIn _ ps              -> tags ps
    ConPatOut{ pat_args = ps } -> tags ps
#if MIN_VERSION_ghc(8,6,1)
    NPlusKPat _ x _ _ _ _      -> tagsLN x
#else
    NPlusKPat x _ _ _ _ _      -> tagsLN x
#endif
    CoPat{}                    -> []
    NPat{}                     -> []
    LitPat{}                   -> []
    WildPat{}                  -> []
    ViewPat{}                  -> []
    SplicePat{}                -> []
#if MIN_VERSION_ghc(8,2,0)
    SumPat{}                   -> missingImp "SumPat"
#endif

instance (HasTags arg, HasTags recc) => HasTags (HsConDetails arg recc) where
  tags d = case d of
    PrefixCon as   -> tags as
    RecCon r       -> tags r
    InfixCon a1 a2 -> tags [a1, a2]

instance HasTags arg => HasTags (HsRecFields name arg) where
  tags (HsRecFields fs _) = tags fs

instance HasTags arg => HasTags (HsRecField name arg) where
  tags (HsRecField _ a _) = tags a

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (Sig pass) where
#else
instance TagName name => HasTags (Sig name) where
#endif
  tags d = case d of
#if MIN_VERSION_ghc(8,6,1)
    TypeSig _ x _       -> concatMap tagsLN x
#else
    TypeSig x _         -> concatMap tagsLN x
#endif
#if MIN_VERSION_ghc(8,6,1)
    PatSynSig _ x _      -> concatMap tagsLN x
#elif MIN_VERSION_ghc(8,2,0)
    PatSynSig x _       -> concatMap tagsLN x
#else
    PatSynSig x _       -> tagsLN x
#endif
#if MIN_VERSION_ghc(8,6,1)
    ClassOpSig _ _ x _   -> concatMap tagsLN x
#else
    ClassOpSig _ x _    -> concatMap tagsLN x
#endif
    FixSig{}            -> []
    InlineSig{}         -> []
    SpecSig{}           -> []
    SpecInstSig{}       -> []
    IdSig{}             -> []
    MinimalSig{}        -> []
#if MIN_VERSION_ghc(8,2,0)
    SCCFunSig{}         -> []
    CompleteMatchSig{}  -> []
#endif
#if MIN_VERSION_ghc(8,6,1)
    XSig{}              -> missingImp "XSig"
#endif

#if MIN_VERSION_ghc(8,4,0)
instance (IdP pass ~ name, TagName name) => HasTags (ForeignDecl pass) where
#else
instance TagName name => HasTags (ForeignDecl name) where
#endif
  tags d = case d of
#if MIN_VERSION_ghc(8,6,1)
    ForeignImport _ x _ _ -> tagsLN x
    XForeignDecl _        -> missingImp "XForeignDecl"
#else
    ForeignImport x _ _ _ -> tagsLN x
#endif
    ForeignExport{}       -> []

missingImp :: String -> a
missingImp x = error $ "Missing implementation: " ++ x
