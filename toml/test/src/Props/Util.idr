module Props.Util

import Text.FC
import Text.ParseError
import Text.TOML.Parser
import Gen.Util

%default total

export
parseProp : Gen (Encoded TomlValue) -> Property
parseProp val = property $ do
  Enc c v <- forAll val
  footnote "Encoded: \{c}"
  parse Virtual c === Right v
