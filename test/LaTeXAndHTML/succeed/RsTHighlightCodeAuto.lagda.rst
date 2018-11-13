********************
RsTHighlightCodeAuto
********************

..

::
   module RsTHighlightCodeAuto where

Mokou:
    So, what are you doing out this late?

::
   open import Agda.Builtin.Size
   open import Agda.Primitive

Marisa:
    Harvesting bamboo shoots.
::
   variable
     i : Size

   -- Alice:
   --    A trial of guts.

     ℓ : Level

   -- Mokou:
   --    Uh, which one is it?

Comment tests ↑

::
     A : Set ℓ
   -- Marisa:
   --   That should've been obvious...

::
   record Thunk {ℓ} (F : Size → Set ℓ) (i : Size) : Set ℓ where
     coinductive

Mokou:
    The medicine? You mean the Hourai Elixir?
    I consumed it a long time ago.
    Thanks to the elixir, I am immortal even now.
    Kaguya still tries to kill me.
    But it's impossible.
    This meaningless conflict has dragged on for over a thousand years.

::
     field force : {j : Size< i} → F j
   open Thunk public

Marisa:
    I get it. I understand now...
    So, you're playing the role of the ghost in the haunted house.
    I was suspicious when I first heard about this "trial of guts" thing from Kaguya.
    She must have thought that I, who defeated her, might be able to crush you.

::
   data Conat (i : Size) : Set where
     zero : Conat i
     suc : Thunk Conat i → Conat i

Alice:
    Wait, aren't you stealing all the credit for yourself?
    Besides, crushing humans is a youkai's role.
    The human before us is obviously mine to crush.

::
   infinity : Conat i
   infinity = suc λ where .Thunk.force → infinity

Mokou:
    What, Kaguya was defeated?
    By the two of you who stand before me?
    That's quite surprising. That troublesome Lunarian was defeated by such a team...
    It's been a long time since I've confronted such tough assassins.
    Or maybe the only thing that's tough about them is their guts?

::
   open import Agda.Builtin.Nat

   fromℕ : Nat → Conat ∞
   fromℕ zero    = zero
   fromℕ (suc n) = suc λ where .Thunk.force → fromℕ n

Alice:
    It's too bad about that Hourai Elixir.
    I wanted it for my collection.

::
   -- Why can't we have goals in literate Agda mode?
