-- Andreas, 2019-08-08, issue #3962 reported (+ test case) by guillaumebrunerie

-- Don't lex "{{" as instance braces if followed by "-", as this will confuse Emacs.
-- Rather lex "{{-" as "{" "{-".

postulate
  A : Set
  f : {{_ : A}} → Set
  -x : A

B : Set
B = f {{-x}}

C : Set
C = ?

-- WAS: passes parser but confuses emacs, which treats everything following {- as comment.

-- Expected error: Unterminated '{-'
