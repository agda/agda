-- Andreas, 2018-06-03, issue #3102
-- Regression: slow reduce with lots of module parameters and an import.

-- {-# OPTIONS -v tc.cc:30 -v tc.cover.top:30 --profile=internal #-}

open import Agda.Builtin.Bool

module _ (A B C D E F G H I J K L M O P Q R S T U V W X Y Z
          A₁ B₁ C₁ D₁ E₁ F₁ G₁ H₁ I₁ J₁ K₁ L₁ M₁ O₁ P₁ Q₁ R₁ S₁ T₁ U₁ V₁ W₁ X₁ Y₁ Z₁
          A₂ B₂ C₂ D₂ E₂ F₂ G₂ H₂ I₂ J₂ K₂ L₂ M₂ O₂ P₂ Q₂ R₂ S₂ T₂ U₂ V₂ W₂ X₂ Y₂ Z₂
          A₃ B₃ C₃ D₃ E₃ F₃ G₃ H₃ I₃ J₃ K₃ L₃ M₃ O₃ P₃ Q₃ R₃ S₃ T₃ U₃ V₃ W₃ X₃ Y₃ Z₃
          A₄ B₄ C₄ D₄ E₄ F₄ G₄ H₄ I₄ J₄ K₄ L₄ M₄ O₄ P₄ Q₄ R₄ S₄ T₄ U₄ V₄ W₄ X₄ Y₄ Z₄
          : Set) where

test : Bool → Bool
test true  = false
test false = false

-- Should succeed instantaneously.
