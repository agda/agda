-- Andreas, 2016-03-28, Issue 1920
-- Improve error message when user puts where clause in hole.

infix 3 _∎

postulate
  A : Set
  begin : A
  _∎ : A → A

works : A
works = begin
  ∎
  where b = begin

test : A
test = {!begin
  ∎
  where b = begin
!}
