module Parser

import Text.FC
import Text.ParseError
import public Generators

%default total

parseProp : Gen (Encoded TomlValue) -> Property
parseProp val = property $ do
  Enc c v <- forAll val
  footnote "Encoded: \{c}"
  parse Virtual c === Right v

prop_bool : Property
prop_bool = parseProp $ keyValTbl bool

export
properties : Group
properties = MkGroup "Parser"
  [ ("prop_bool", prop_bool)
  ]
