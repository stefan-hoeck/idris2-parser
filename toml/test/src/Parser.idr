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

prop_keyval : Property
prop_keyval = parseProp $ keyValTbl primVal

prop_array : Property
prop_array = parseProp $ keyValTbl (array 3)

export
properties : Group
properties = MkGroup "Parser"
  [ ("prop_keyval", prop_keyval)
  , ("prop_array", prop_array)
  ]
