{-| Minimal redefine + re-export of a lens package, restricting to the needs of the library(s) using it
-}

module CHR.Data.Lens
  ( -- dispatch on desired lens system
    -- module CHR.Data.Lens.FCLabels
    module CHR.Data.Lens.MicroLens

  )
  where

-- import CHR.Data.Lens.FCLabels
import CHR.Data.Lens.MicroLens

