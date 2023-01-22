-- | Aspects, used for annotations in pretty-printing and syntax
-- highlighting.
module Agda.Utils.Pretty.Aspect where

import Control.DeepSeq

import GHC.Generics

-- | To avoid nasty import cycles, this type is parameterised over the
-- type Common.Induction.
data Aspect' induction
  = Comment
  | Keyword
  | String
  | Number
  | Hole
  | Symbol                     -- ^ Symbols like forall, =, ->, etc.
  | PrimitiveType              -- ^ Things like Set and Prop.
  | Name (Maybe (NameKind' induction)) Bool -- ^ Is the name an operator part?
  | Pragma                     -- ^ Text occurring in pragmas that
                               --   does not have a more specific
                               --   aspect.
  | Background                 -- ^ Non-code contents in literate Agda
  | Markup
    -- ^ Delimiters used to separate the Agda code blocks from the
    -- other contents in literate Agda
  | Interaction
    -- ^ A string of interactive text in the pretty-printed output.
    deriving (Eq, Show, Generic, Functor)

data NameKind' induction
  = Bound                  -- ^ Bound variable.
  | Generalizable          -- ^ Generalizable variable.
                           --   (This includes generalizable
                           --   variables that have been
                           --   generalized).
  | Constructor induction  -- ^ Inductive or coinductive constructor.
  | Datatype
  | Field                  -- ^ Record field.
  | Function
  | Module                 -- ^ Module name.
  | Postulate
  | Primitive              -- ^ Primitive.
  | Record                 -- ^ Record type.
  | Argument               -- ^ Named argument, like x in {x = v}
  | Macro                  -- ^ Macro.
    deriving (Eq, Show, Generic, Functor)

data PrintingAspect
  = Highlight (Aspect' ())
  | TriggerCallback Int
  | WithTooltip String
  deriving (Eq, Show, Generic)

instance NFData a => NFData (Aspect' a)
instance NFData a => NFData (NameKind' a)
instance NFData PrintingAspect

boundName, generalizableName, conName, datatypeName, fieldName,
  functionName, moduleName, macroName, recordName, postulatedName, primitiveName :: PrintingAspect
boundName          = Highlight $ Name (Just Bound) False
generalizableName  = Highlight $ Name (Just Generalizable) False
conName            = Highlight $ Name (Just (Constructor ())) False
datatypeName       = Highlight $ Name (Just Datatype) False
recordName         = Highlight $ Name (Just Record) False
fieldName          = Highlight $ Name (Just Field) False
functionName       = Highlight $ Name (Just Function) False
moduleName         = Highlight $ Name (Just Module) False
macroName          = Highlight $ Name (Just Macro) False
postulatedName     = Highlight $ Name (Just Postulate) False
primitiveName      = Highlight $ Name (Just Primitive) False
