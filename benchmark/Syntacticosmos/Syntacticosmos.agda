module Syntacticosmos (Gnd : Set)(U : Set)(El : U -> Set) where

open import Basics
open import Pr
open import Nom
import Kind
open module KindGUEl = Kind Gnd U El public
import Cxt
open module CxtK = Cxt Kind public
import Loc
open module LocK = Loc Kind public
import Term
open module TermGUEl = Term Gnd U El public
import Shift
open module ShiftGUEl = Shift Gnd U El public
import Eta
open module EtaGUEl = Eta Gnd U El public
import Inst
open module InstGUEl = Inst Gnd U El public
import Subst
open module SubstGUEl = Subst Gnd U El public

