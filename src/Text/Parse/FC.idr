module Text.Parse.FC

import Text.Lex.Bounded
import Derive.Prelude

%default total
%language ElabReflection

public export
data Origin : Type where
  FileSrc : (path : String) -> Origin
  Virtual : Origin

%runElab derive "Origin" [Show,Eq]

public export
Interpolation Origin where
  interpolate (FileSrc p) = p
  interpolate Virtual     = "virtual"

public export
record FileContext where
  constructor FC
  origin : Origin
  bounds : Bounds

public export
fromBounded : String -> Bounded a -> (FileContext, a)
fromBounded s (MkBounded val bounds) = (FC (FileSrc s) bounds, val)

public export
virtualFromBounded : Bounded a -> (FileContext, a)
virtualFromBounded (MkBounded val bounds) = (FC Virtual bounds, val)

%runElab derive "FileContext" [Show,Eq]

export
Interpolation FileContext where
  interpolate (FC o NoBounds) = interpolate o
  interpolate (FC o b)        = "\{o}: \{b}"
