module Text.WebIDL.Types.StringLit

import Derive.Prelude

%default total

%language ElabReflection

||| A quoted string literal
public export
record StringLit where
  constructor MkStrLit
  value : String

%runElab derive "StringLit" [Eq,Ord,Show]

export %inline
Interpolation StringLit where
  interpolate v = #""\#{v.value}""#
