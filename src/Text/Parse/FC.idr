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
  bounds : Maybe Bounds

%runElab derive "FileContext" [Show,Eq]

export
Interpolation FileContext where
  interpolate (FC o $ Just b) = "\{o}: \{b}"
  interpolate (FC o Nothing)  = interpolate o
