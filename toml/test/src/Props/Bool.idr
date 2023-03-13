module Props.Bool

import Gen.Value
import Props.Util

%default total

prop_bool : Property
prop_bool = parseProp (keyValTbl bool)

export
props : Group
props = MkGroup "Text.TOML.Parser bool" [("prop_bool", prop_bool)]
