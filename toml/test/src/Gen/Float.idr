module Gen.Float

import Gen.Time

%default total

--------------------------------------------------------------------------------
--          Float
--------------------------------------------------------------------------------

anyDbl : Gen Double
anyDbl = double (exponentialDoubleFrom 0 (-1.0e50) 1.0e50)

export
anyFloat : Gen TomlFloat
anyFloat =
  frequency [(1, pure NaN), (1, map Infty (maybe sign)), (5, Float <$> anyDbl)]

export
encodedFloat : Gen (Encoded TomlFloat)
encodedFloat = map (\t => Enc "\{t}" t) anyFloat
