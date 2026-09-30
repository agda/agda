?bug : Set
?bug = ?

-- Andreas, 2014-04-16
-- Issue 1104 reported by Fabien Renaud.
-- Emacs mode got confused by identifiers containing --

-- Problem: {!!} is not turned into hole

bug-- : Set
bug-- = ?

another : Set
another = (-- Senfgurke ?
           {!!})-- Noch eine Senfgurke ?

_:--_ : Set → Set → Set
_:--_ = {!!}

bla = let x = Set ;-- bla ?
                   y = Set in  Set

bug? : Set
bug? = {!!}
