{-# OPTIONS -fglasgow-exts #-}

module Syntax.Internal where

data Value = Var Nat Expl
	   | App Value Value Hidden Expl
	   | Lam Type (Abs Value) Expl
	   | Lit Literal Expl
	   | Def Name Expl
	   | MetaV MId Expl

data Type = El Value Sort Expl
	  | Pi Type (Abs Type) Expl
	  | Sort Sort Expl
	  | MetaT MId Expl

data Sort = Type Nat Expl
	  | Prop Expl
	  | MetaS MId Expl 
	  | Lub Sort Sort Expl

data Abs a = Abs Name a

data Expl = InCode Range
	  | DefinedAt Range
	  | Expl :+: Expl
	  | Duh -- this is a default for development which should disappear

--
-- Basic view without explanations
--
data BasicValue = VarBV Nat 
		| AppBV Value Value 
		| LamBV Type (Abs Value)
		| LitBV Literal 
		| DefBV Name 
		| MetaVBV MId

data BasicType = ElBT Value Sort
	       | PiBT Type (Abs Type)
	       | SortBT Sort
	       | MetaTBT MId

data BasicSort = TypeBS Nat
	       | PropBS 
	       | MetaSBS MId
	       | LubBS Sort Sort

basicValue :: Value -> BasicValue
basicValue v = case v of
    Var i _ -> VarBV i
    App v1 v2 -> AppBV v1 v2
    Lam a v _ -> LamBV a v
    Lit l _ -> LitBV l
    Def f _ -> DefBV f
    MetaV x _ -> MetaBV x

basicType :: Type -> BasicType
basicType a = case a of
    El v s _ -> ElBT
    Pi a b _ -> PiBT a b
    Sort s _ -> SortBT s
    MetaT x _ -> MetaTBT x
				  
basicSort :: Sort -> BasicSort
basicSort s = case s of
    Type n _ -> TypeBS n
    Prop _ -> PropBS
    MetaS x _ -> MetaSBS x
    Lub s1 s2 _ -> LubBS s1 s2

--
-- View as a spine, where head is always visible
--
data SpineValue = VarSV Nat [Value]
		| LamSV Type (Abs Value) [Value]
		| LitSV Literal -- literals can't be applied
		| DefSV Name [Value]
		| MetaVSV MId [Value]

spineValue :: Value -> SpineValue
spineValue v = app [] $ basicValue v where
    app args v = case v of
        VarBV i -> VarSV i args
	AppBV v1 v2 -> app (v2 : args) (spineValue v1) v2
	LamBV a v -> LamSV a v args
	LitBV l -> case args of [] -> LitSV l
	DefBV f -> DefSV f args
	MetaVBV x -> MetaVSV x args
