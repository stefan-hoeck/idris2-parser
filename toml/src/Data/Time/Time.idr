module Data.Time.Time

import public Data.Nat
import public Data.Refined
import public Data.Time.Date
import Data.String
import Derive.Prelude
import Derive.Refined
import Text.PrettyPrint.Bernardy

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Hour
--------------------------------------------------------------------------------

public export
record Hour where
  constructor H
  hour : Nat
  {auto 0 valid : Holds (< 24) hour}

namespace Hour
  %runElab derive "Hour" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation Hour where
    interpolate (H h) = padLeft 2 '0' $ show h

  export
  Pretty Hour where prettyPrec _ = line . interpolate

--------------------------------------------------------------------------------
--          Minute
--------------------------------------------------------------------------------

public export
record Minute where
  constructor M
  minute : Nat
  {auto 0 valid : Holds (< 60) minute}

namespace Minute
  %runElab derive "Minute" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation Minute where
    interpolate (M m) = padLeft 2 '0' $ show m

  export
  Pretty Minute where prettyPrec _ = line . interpolate

--------------------------------------------------------------------------------
--          Second
--------------------------------------------------------------------------------

public export
record Second where
  constructor S
  second : Nat
  {auto 0 valid : Holds (<= 60) second}

namespace Second
  %runElab derive "Second" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation Second where
    interpolate (S s) = padLeft 2 '0' $ show s

  export
  Pretty Second where prettyPrec _ = line . interpolate

--------------------------------------------------------------------------------
--          Milliseconds
--------------------------------------------------------------------------------

public export
record MilliSecond where
  constructor MS
  milliseconds : Nat
  {auto 0 valid : Holds (< 1000) milliseconds}

namespace MilliSecond
  %runElab derive "MilliSecond" [Show, Eq, Ord, RefinedInteger]

  export
  Interpolation MilliSecond where
    interpolate (MS s) = padLeft 3 '0' $ show s

  export
  Pretty MilliSecond where prettyPrec _ = line . interpolate

--------------------------------------------------------------------------------
--          LocalTime
--------------------------------------------------------------------------------

public export
record LocalTime where
  constructor LT
  hour   : Hour
  minute : Minute
  second : Second
  prec   : Maybe MilliSecond

%runElab derive "LocalTime" [Show, Eq, Ord]

export
Interpolation LocalTime where
  interpolate (LT h m s ms) =
    let mss := maybe "" (\x => ".\{x}") ms
     in "\{h}:\{m}:\{s}\{mss}"

export %inline
Pretty LocalTime where prettyPrec _ = line . interpolate

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

export %inline
Pretty Sign where prettyPrec _ = line . interpolate

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

export %inline
Pretty Offset where prettyPrec _ = line . interpolate

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

export %inline
Pretty OffsetTime where prettyPrec _ = line . interpolate

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

export %inline
Pretty LocalDateTime where prettyPrec _ = line . interpolate

public export
record OffsetDateTime where
  constructor ODT
  date : Date
  time : OffsetTime

%runElab derive "OffsetDateTime" [Show, Eq]

export
Interpolation OffsetDateTime where
  interpolate (ODT d t) = "\{d}T\{t}"

export %inline
Pretty OffsetDateTime where prettyPrec _ = line . interpolate
