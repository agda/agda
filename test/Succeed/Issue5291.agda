-- Andreas, 2021-08-19, issue #5291 reported by gergoerdi
-- https://stackoverflow.com/q/66816547/477476

open import Agda.Builtin.Char
open import Agda.Builtin.String

works : Char
works = '\SOH'

-- This used to fail as the matcher was committed to finding SOH after SO.
-- (Worked only for prefix-free matching.)

test : Char
test = '\SO'

-- Here, all the silly legacy ASCII escape sequences in their glorious detail...

all : String
all = "\NUL\SOH\STX\ETX\EOT\ENQ\ACK\BEL\BS\HT\LF\VT\FF\CR\SO\SI\DEL\DLE\DC1\DC2\DC3\DC4\NAK\SYN\ETB\CAN\EM\SUB\ESC\FS\GS\RS\US"
