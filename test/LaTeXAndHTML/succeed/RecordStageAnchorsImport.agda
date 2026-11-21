module RecordStageAnchorsImport where

import RecordStageAnchors as Original

module Copy = Original.R
open Copy renaming (X to Renamed)

use : (r : Original.R) → Set
use r = Renamed r
