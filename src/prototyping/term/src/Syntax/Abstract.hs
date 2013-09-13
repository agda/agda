
module Syntax.Abstract where

data SrcLoc = SrcLoc { pLine :: Int, pCol :: Int }

noSrcLoc = SrcLoc 0 0

instance Show SrcLoc where
  show (SrcLoc line col) = concat [show line, ":", show col]

data Name = Name SrcLoc String
  deriving Show

data Decl = TypeSig TypeSig
          | FunDef  Name [Pattern] Expr
          | DataDef Name [Name] [TypeSig]
          | RecDef  Name [Name] Name [TypeSig]
  deriving Show

data TypeSig = Sig Name Expr
  deriving Show

data Expr = Lam Name Expr
          | Pi Name Expr Expr
          | Fun Expr Expr
          | Equal Expr Expr Expr
          | App Head [Elim]
          | Set SrcLoc
          | Meta SrcLoc
  deriving Show

data Head = Var Name
          | Def Name
          | Con Name
  deriving Show

data Elim = Apply Expr
          | Proj Name
  deriving Show

data Pattern = VarP Name
             | WildP SrcLoc
             | ConP Name [Pattern]
  deriving Show

class HasSrcLoc a where
  srcLoc :: a -> SrcLoc

instance HasSrcLoc SrcLoc where
  srcLoc = id

instance HasSrcLoc Name where
  srcLoc (Name p _) = p

instance HasSrcLoc Decl where
  srcLoc d = case d of
    TypeSig sig    -> srcLoc sig
    FunDef x _ _   -> srcLoc x
    DataDef x _ _  -> srcLoc x
    RecDef x _ _ _ -> srcLoc x

instance HasSrcLoc TypeSig where
  srcLoc (Sig x _) = srcLoc x

instance HasSrcLoc Expr where
  srcLoc e = case e of
    Lam x _     -> srcLoc x
    Pi x _ _    -> srcLoc x
    Fun a _     -> srcLoc a
    Equal _ a _ -> srcLoc a
    App h _     -> srcLoc h
    Set p       -> p
    Meta p      -> p

instance HasSrcLoc Head where
  srcLoc h = case h of
    Var x -> srcLoc x
    Def x -> srcLoc x
    Con x -> srcLoc x

instance HasSrcLoc Pattern where
  srcLoc p = case p of
    WildP p  -> p
    VarP x   -> srcLoc x
    ConP c _ -> srcLoc c

