-- Andreas, 2016-07-29 issue #707

-- {-# OPTIONS -v tc.ip:20 #-}

postulate A B : {!!}

-- Should not create two interaction points!
-- Also not two sort metas!
