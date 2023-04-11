module Data.Time.Time

import public Data.Nat
import public Data.Refined
import public Data.Time.Date
import public Data.Refined.Integer
import Data.String
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Hour
--------------------------------------------------------------------------------

public export
record Hour where
  constructor H
  hour : Integer
  {auto 0 valid : FromTo 0 23 hour}

namespace Hour
  %runElab derive "Hour" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation Hour where
    interpolate (H h) = padLeft 2 '0' $ show h

--------------------------------------------------------------------------------
--          Minute
--------------------------------------------------------------------------------

public export
record Minute where
  constructor M
  minute : Integer
  {auto 0 valid : FromTo 0 59 minute}

namespace Minute
  %runElab derive "Minute" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation Minute where
    interpolate (M m) = padLeft 2 '0' $ show m

--------------------------------------------------------------------------------
--          Second
--------------------------------------------------------------------------------

public export
record Second where
  constructor S
  second : Integer
  {auto 0 valid : FromTo 0 60 second}

namespace Second
  %runElab derive "Second" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation Second where
    interpolate (S s) = padLeft 2 '0' $ show s

--------------------------------------------------------------------------------
--          MicroSecond
--------------------------------------------------------------------------------

public export
record MicroSecond where
  constructor MS
  us : Integer
  {auto 0 valid : FromTo 0 999_999 us}

namespace MicroSecond
  %runElab derive "MicroSecond" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation MicroSecond where
    interpolate (MS n) = padLeft 6 '0' $ show n

--------------------------------------------------------------------------------
--          LocalTime
--------------------------------------------------------------------------------

public export
record LocalTime where
  constructor LT
  hour   : Hour
  minute : Minute
  second : Second
  prec   : Maybe MicroSecond

%runElab derive "LocalTime" [Show, Eq, Ord]

export
Interpolation LocalTime where
  interpolate (LT h m s ms) =
    let mss := maybe "" (\x => ".\{x}") ms
     in "\{h}:\{m}:\{s}\{mss}"

--------------------------------------------------------------------------------
--          Sign
--------------------------------------------------------------------------------

public export
data Sign = Minus | Plus

%runElab derive "Sign" [Show, Eq, Ord]

export
Interpolation Sign where
  interpolate Minus = "-"
  interpolate Plus  = "+"

--------------------------------------------------------------------------------
--          Offset
--------------------------------------------------------------------------------

public export
data Offset : Type where
  Z : Offset
  O : (sign : Sign) -> (h : Hour) -> (m : Minute) -> Offset

%runElab derive "Offset" [Show, Eq]

export
Interpolation Offset where
  interpolate Z = "Z"
  interpolate (O sign h m) = "\{sign}\{h}:\{m}"

--------------------------------------------------------------------------------
--          OffsetTime
--------------------------------------------------------------------------------

public export
record OffsetTime where
  constructor OT
  time   : LocalTime
  offset : Offset

%runElab derive "OffsetTime" [Show, Eq]

export
Interpolation OffsetTime where
  interpolate (OT t o) = "\{t}\{o}"

--------------------------------------------------------------------------------
--          DateTime
--------------------------------------------------------------------------------

public export
record LocalDateTime where
  constructor LDT
  date : Date
  time : LocalTime

%runElab derive "LocalDateTime" [Show, Eq]

export
Interpolation LocalDateTime where
  interpolate (LDT d t) = "\{d}T\{t}"

public export
record OffsetDateTime where
  constructor ODT
  date : Date
  time : OffsetTime

%runElab derive "OffsetDateTime" [Show, Eq]

export
Interpolation OffsetDateTime where
  interpolate (ODT d t) = "\{d}T\{t}"

--------------------------------------------------------------------------------
--          AnyTime
--------------------------------------------------------------------------------

public export
data AnyTime : Type where
  ATDate : Date -> AnyTime
  ATLocalTime      : LocalTime -> AnyTime
  ATLocalDateTime  : LocalDateTime -> AnyTime
  ATOffsetDateTime : OffsetDateTime -> AnyTime

%runElab derive "AnyTime" [Show, Eq]

export
Interpolation AnyTime where
  interpolate (ATDate x)           = interpolate x
  interpolate (ATLocalTime x)      = interpolate x
  interpolate (ATLocalDateTime x)  = interpolate x
  interpolate (ATOffsetDateTime x) = interpolate x
