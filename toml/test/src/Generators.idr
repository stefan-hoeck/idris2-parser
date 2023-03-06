module Generators

import Data.List1
import Data.String
import Data.Vect
import Derive.Prelude
import public Hedgehog
import public Text.TOML

%default total
%language ElabReflection

public export
record Encoded a where
  constructor Enc
  code  : String
  value : a

public export
Functor Encoded where
  map f (Enc c v) = Enc c $ f v

%runElab derive "Encoded" [Show,Eq]

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

%inline
linList : Nat -> Gen a -> Gen (List a)
linList = list . linear 0

%inline
linList1 : Nat -> Gen a -> Gen (List a)
linList1 = list . linear 1

%inline
linString : Nat -> Gen Char -> Gen String
linString n = map pack . linList n

%inline
linString1 : Nat -> Gen Char -> Gen String
linString1 n = map pack . linList1 n

--------------------------------------------------------------------------------
--          Comment
--------------------------------------------------------------------------------

isCommentControl : Char -> Bool
isCommentControl c =
  let n := the Nat $ cast c
   in n <= 0x8 || (n >= 0xa && n <= 0x1f) || n == 0x7f

-- from the spec
-- Control characters other than tab (U+0000 to U+0008,
-- U+000A to U+001F, U+007F) are not permitted in comments.
comment : Gen String
comment = ("#" ++) <$> linString 10 (map toCommentChar unicode)
  where toCommentChar : Char -> Char
        toCommentChar c = if isCommentControl c then ' ' else c

--------------------------------------------------------------------------------
--          Space
--------------------------------------------------------------------------------

lineSpace : Gen String
lineSpace = linString 3 (element [' ', '\t'])

spaced : Gen (Encoded a) -> Gen (Encoded a)
spaced g = [| adj lineSpace g lineSpace |]
  where adj : String -> Encoded a -> String -> Encoded a
        adj s1 (Enc c v) s2 = Enc (s1 ++ c ++ s2) v

--------------------------------------------------------------------------------
--          Key
--------------------------------------------------------------------------------

bareKey : Gen (Encoded String)
bareKey = (\s => Enc s s) <$> linString1 10 keyChar
  where keyChar : Gen Char
        keyChar = choice [alphaNum, element ['-', '_']]

singleKey : Gen (Encoded String)
singleKey = bareKey

key : Gen (Encoded Key)
key = [| acc (spaced singleKey) (linList 2 $ spaced singleKey) |]
  where
    acc : Encoded String -> List (Encoded String) -> Encoded Key
    acc k ks =
      Enc
        (concat . intersperse "." $ k.code :: map code ks)
        (k.value ::: map value ks)

--------------------------------------------------------------------------------
--          Bool
--------------------------------------------------------------------------------

export
bool : Gen (Encoded TomlValue)
bool = element [Enc "true" $ TBool True, Enc "false" $ TBool False]

--------------------------------------------------------------------------------
--          Date/Time
--------------------------------------------------------------------------------

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
localDateTime : Gen LocalDateTime
localDateTime = [| LDT date localTime |]

export
offsetDateTime : Gen OffsetDateTime
offsetDateTime = [| ODT date offsetTime |]

export
anyTime : Gen AnyTime
anyTime = choice
  [ map ATDate date
  , map ATLocalTime localTime
  , map ATLocalDateTime localDateTime
  , map ATOffsetDateTime offsetDateTime
  ]

noZ : String -> String
noZ = pack . map adj . unpack
  where
    adj : Char -> Char
    adj 'T' = ' '
    adj c   = c

export
encodedTime : Gen (Encoded AnyTime)
encodedTime = choice
 [ map (\t => Enc "\{t}" t) anyTime
 , map (\t => Enc (toLower "\{t}") t) anyTime
 ]

--------------------------------------------------------------------------------
--          Inline Values
--------------------------------------------------------------------------------

inlineValue : Gen (Encoded TomlValue)
inlineValue = choice
  [ bool
  , map TTime <$> encodedTime
  ]

export
keyVal : Gen (Encoded a) -> Gen (Encoded (Key, a))
keyVal val = [| acc key val |]
  where
    acc : Encoded Key -> Encoded a -> Encoded (Key,a)
    acc k v = Enc (k.code ++ "=" ++ v.code) (k.value,v.value)

export
keyValTbl : Gen (Encoded TomlValue) -> Gen (Encoded TomlValue)
keyValTbl val = map toTable <$> keyVal val
  where
    toTable : (Key,TomlValue) -> TomlValue
    toTable (k,v) = TTbl Table $ singleton k.head (go k.tail)
      where
        go : List String -> TomlValue
        go []        = v
        go (x :: xs) = TTbl None $ singleton x (go xs)
