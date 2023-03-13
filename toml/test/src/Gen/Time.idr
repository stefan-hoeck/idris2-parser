module Gen.Time

import public Gen.Util

%default total

noT : String -> String
noT = pack . map adj . unpack
  where
    adj : Char -> Char
    adj 'T' = ' '
    adj 't' = ' '
    adj c   = c

export
allEncodings : (a -> String) -> Gen a -> Gen (Encoded a)
allEncodings f g = choice
  [ encoded f g
  , encoded (toLower .  f) g
  , encoded (noT . f) g
  , encoded (toLower . noT . f) g
  ]

export
year : Gen Year
year = fromMaybe 0 . refineYear <$> integer (exponential 0 9999)

export
month : Gen Month
month = fromMaybe JAN . intToMonth <$> integer (linear 1 12)

export
date : Gen Date
date = [| toDate year month (integer $ linear 1 31) |]
  where
    toDate : Year -> Month -> Integer -> Date
    toDate y m i = case refineDay {m} i of
      Just d  => MkDate y m d
      Nothing => MkDate y JAN 1

export
hour : Gen Hour
hour = fromMaybe 0 . refineHour <$> integer (linear 0 23)

export
minute : Gen Minute
minute = fromMaybe 0 . refineMinute <$> integer (linear 0 59)

export
second : Gen Second
second = fromMaybe 0 . refineSecond <$> integer (linear 0 60)

export
microsecond : Gen MicroSecond
microsecond = fromMaybe 0 . refineMicroSecond <$> integer (exponential 0 999_999)

export
localTime : Gen LocalTime
localTime = [| LT hour minute second (maybe microsecond) |]

export
sign : Gen Sign
sign = element [Minus,Plus]

export
offset : Gen Offset
offset = frequency
  [ (5, [| O sign hour minute |])
  , (1, constant Z)
  ]

export
offsetTime : Gen OffsetTime
offsetTime = [| OT localTime offset |]

export
localDateTime : Gen AnyTime
localDateTime = ATLocalDateTime <$> [| LDT date localTime |]

export
offsetDateTime : Gen AnyTime
offsetDateTime = ATOffsetDateTime <$> [| ODT date offsetTime |]

export
anyTime : Gen (Encoded AnyTime)
anyTime = allEncodings interpolate $ choice
  [ map ATDate date
  , map ATLocalTime localTime
  , localDateTime
  , offsetDateTime
  ]

--------------------------------------------------------------------------------
--          No seconds
--------------------------------------------------------------------------------

noSecsLT : LocalTime -> String
noSecsLT (LT h m _ _) = "\{h}:\{m}"

noSecsLDT : LocalDateTime -> String
noSecsLDT (LDT d t) = "\{d}T\{noSecsLT t}"

noSecsOT : OffsetTime -> String
noSecsOT (OT t o) = "\{noSecsLT t}\{o}"

noSecsODT : OffsetDateTime -> String
noSecsODT (ODT d t) = "\{d}T\{noSecsOT t}"

noSecsAT : AnyTime -> String
noSecsAT (ATDate x) = "\{x}"
noSecsAT (ATLocalTime x) = noSecsLT x
noSecsAT (ATLocalDateTime x) = noSecsLDT x
noSecsAT (ATOffsetDateTime x) = noSecsODT x

export
localTime0 : Gen LocalTime
localTime0 = [| Time.LT hour minute (pure 0) (pure Nothing) |]

export
offsetTime0 : Gen OffsetTime
offsetTime0 = [| OT localTime0 offset |]

export
localDateTime0 : Gen AnyTime
localDateTime0 = ATLocalDateTime <$> [| LDT date localTime0 |]

export
offsetDateTime0 : Gen AnyTime
offsetDateTime0 = ATOffsetDateTime <$> [| ODT date offsetTime0 |]

export
anyTime0 : Gen (Encoded AnyTime)
anyTime0 = allEncodings noSecsAT $ choice
  [ map ATLocalTime localTime0
  , localDateTime0
  , offsetDateTime0
  ]
