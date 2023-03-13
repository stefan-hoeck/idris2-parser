module Gen.Bool

import public Gen.Util

%default total

export
bool : Gen (Encoded TomlValue)
bool = element [Enc "true" $ TBool True, Enc "false" $ TBool False]
