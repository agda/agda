open import Agda.Primitive

variable
  A : Set _

levelOf : A → Level
levelOf {a} _ = a
