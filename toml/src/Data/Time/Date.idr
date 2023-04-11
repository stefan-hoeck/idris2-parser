module Data.Time.Date

import Data.String
import Data.Refined.Integer
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Year
--------------------------------------------------------------------------------

public export
record Year where
  constructor Y
  year : Integer
  {auto 0 valid : FromTo 0 9999 year}

%runElab derive "Year" [Show, Eq, Ord, RefinedInteger]

export
Interpolation Year where
  interpolate (Y y) = padLeft 4 '0' $ show y

--------------------------------------------------------------------------------
--          Month
--------------------------------------------------------------------------------

public export
data Month : Type where
  JAN : Month
  FEB : Month
  MAR : Month
  APR : Month
  MAY : Month
  JUN : Month
  JUL : Month
  AUG : Month
  SEP : Month
  OCT : Month
  NOV : Month
  DEC : Month

%runElab derive "Month" [Show, Eq, Ord]

export
Interpolation Month where
  interpolate m = padLeft 2 '0' $ show (conIndexMonth m + 1)

public export
DaysInMonth : Month -> Integer
DaysInMonth JAN = 31
DaysInMonth FEB = 29
DaysInMonth MAR = 31
DaysInMonth APR = 30
DaysInMonth MAY = 31
DaysInMonth JUN = 30
DaysInMonth JUL = 31
DaysInMonth AUG = 31
DaysInMonth SEP = 30
DaysInMonth OCT = 31
DaysInMonth NOV = 30
DaysInMonth DEC = 31

public export
intToMonth : Integer -> Maybe Month
intToMonth 1  = Just JAN
intToMonth 2  = Just FEB
intToMonth 3  = Just MAR
intToMonth 4  = Just APR
intToMonth 5  = Just MAY
intToMonth 6  = Just JUN
intToMonth 7  = Just JUL
intToMonth 8  = Just AUG
intToMonth 9  = Just SEP
intToMonth 10 = Just OCT
intToMonth 11 = Just NOV
intToMonth 12 = Just DEC
intToMonth _  = Nothing

--------------------------------------------------------------------------------
--          Day
--------------------------------------------------------------------------------

public export
record Day (m : Month) where
  constructor D
  day : Integer
  {auto 0 valid : FromTo 1 (DaysInMonth m) day}

%runElab deriveIndexed "Day" [Show, Eq, Ord]

public export
refineDay : {m : _} -> Integer -> Maybe (Day m)
refineDay n = case hdec0 {p = FromTo 1 (DaysInMonth m)} n of
  Nothing0 => Nothing
  Just0 v  => Just $ D n

namespace Day
  public export
  fromInteger :
       {m : _}
    -> (n : Integer)
    -> {auto 0 p : IsJust (refineDay {m} $ cast n)}
    -> Day m
  fromInteger n = fromJust $ refineDay (cast n)

export
Interpolation (Day m) where
  interpolate (D d) = padLeft 2 '0' $ show d

--------------------------------------------------------------------------------
--          Date
--------------------------------------------------------------------------------

public export
record Date where
  constructor MkDate
  year  : Year
  month : Month
  day   : Day month

public export
Eq Date where
  MkDate y1 m1 d1 == MkDate y2 m2 d2 =
    y1 == y2 && m1 == m2  && d1.day == d2.day

public export
Ord Date where
  compare (MkDate y1 m1 d1) (MkDate y2 m2 d2) =
    if y1 /= y2 then compare y1 y2
    else if m1 /= m2 then compare m1 m2
    else compare d1.day d2.day

%runElab derive "Date" [Show]

export
Interpolation Date where
  interpolate (MkDate y m d) = "\{y}-\{m}-\{d}"

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

testYear : Year
testYear = 2022
