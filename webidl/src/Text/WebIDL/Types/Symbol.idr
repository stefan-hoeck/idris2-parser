module Text.WebIDL.Types.Symbol

import Derive.Prelude

%default total

%language ElabReflection

||| A single non-alphanumeric character that is not
||| part of another recognized text token like a comment
||| or floating point literal.
public export
data Symbol : Type where
  ||| An ellipsis : ...
  Ellipsis : Symbol

  ||| A single non-alphanumeric character like '=' or '{'.
  Symb     : (symb : Char) -> Symbol

%runElab derive "Symbol" [Eq,Show]

export %inline
Interpolation Symbol where
  interpolate Ellipsis = "..."
  interpolate (Symb c) = singleton c
