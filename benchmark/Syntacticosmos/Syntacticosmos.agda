module Syntacticosmos (Gnd : Set)(U : Set)(El : U -> Set) where

open import Basics
open import Pr
open import Nom
import Kind
open Kind Gnd U El public
import Cxt
open Cxt Kind public
import Loc
open Loc Kind public
import Term
open Term Gnd U El public
import Shift
open Shift Gnd U El public
import Eta
open Eta Gnd U El public
import Inst
open Inst Gnd U El public
import Subst
open Subst Gnd U El public

