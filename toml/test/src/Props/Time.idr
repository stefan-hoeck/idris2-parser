module Props.Time

import Gen.Value
import Props.Util

%default total

prop_localTime : Property
prop_localTime =
  parseProp
    (keyValTbl $ (\t => Enc "\{t}" (TTime $ ATLocalTime t)) <$> localTime)

prop_localDate : Property
prop_localDate =
  parseProp (keyValTbl $ map (TTime . ATDate) <$> allEncodings interpolate date)

prop_localDateTime : Property
prop_localDateTime =
  parseProp (keyValTbl $ map TTime <$> allEncodings interpolate localDateTime)

prop_offsetDateTime : Property
prop_offsetDateTime =
  parseProp (keyValTbl $ map TTime <$> allEncodings interpolate offsetDateTime)

prop_anyTime : Property
prop_anyTime = parseProp (keyValTbl $ map TTime <$> anyTime)

prop_anyTime0 : Property
prop_anyTime0 = parseProp (keyValTbl $ map TTime <$> anyTime0)

export
props : Group
props =
  MkGroup
    "Text.TOML.Parser time"
    [ ("prop_localTime", prop_localTime)
    , ("prop_localDate", prop_localDate)
    , ("prop_localDateTime", prop_localDateTime)
    , ("prop_offsetDateTime", prop_offsetDateTime)
    , ("prop_anyTime", prop_anyTime)
    , ("prop_anyTime0", prop_anyTime0)
    ]
