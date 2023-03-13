module Gen.Int

import public Gen.Util

%default total

--------------------------------------------------------------------------------
--          Integer
--------------------------------------------------------------------------------

MaxInt : Integer
MaxInt = 0xffff_ffff_ffff_ffff_ffff

export
anyInteger : Gen Integer
anyInteger = integer (exponentialFrom 0 (negate MaxInt) MaxInt)

export
encodedInteger : Gen (Encoded Integer)
encodedInteger = choice
  [ map (\t => Enc (show t) t) anyInteger
  ]
