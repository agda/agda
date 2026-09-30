-- Andreas, 2016-11-18, issue #2174
-- report and test case by Nisse

postulate
  F : Set → Set → Set

G : Set
G = {!!}

-- WAS: giving first F ? and then F ? ? lead to one of the metas not goalified.

-- Should succeed now, see script Issue2174a.sh
