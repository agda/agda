-- Andreas, 2016-06-11, issue reported by Mietek Bak

data Record : Foo → Set where

-- WAS: Panic: unbound name Foo

-- NOW: Not in scope: Foo
