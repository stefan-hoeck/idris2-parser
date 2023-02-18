module Text.TOML.Types

import Data.SortedMap
import Derive.Prelude
import Derive.Pretty
import Text.Bounds
import Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

%runElab derive "Text.Bounds.Position" [Pretty]
%runElab derive "Text.Bounds.Bounds" [Pretty]
%runElab derive "Text.Bounds.Bounded" [Pretty]

public export
Pretty k => Pretty v => Pretty (SortedMap k v) where
  prettyPrec p m = prettyCon p "fromList" [prettyArg $ SortedMap.toList m]

public export
Pretty a => Pretty (List1 a) where
  prettyPrec p (v ::: vs) =
    let pv  := prettyPrec (User 7) v
        pvs := prettyPrec (User 7) vs
        opstyle := parenthesise (p >= User 7) $ hsep [pv, line ":::", pvs]
     in ifMultiline opstyle (parenthesise (p >= App) constyle )
       where
         constyle : Doc opts
         constyle = prettyCon p "(:::)" [prettyArg v, prettyArg vs]

public export
0 Key : Type
Key = List1 String

||| Data type for trees of TOML data.
public export
data TomlValue : Type where
  ||| A string literal
  TStr  : String  -> TomlValue

  ||| A boolean literal
  TBool : Bool  -> TomlValue

  ||| An integer
  TInt  : Integer -> TomlValue

  ||| A floating point number
  TDbl  : Double  -> TomlValue

  ||| An array of values
  TArr  : List TomlValue -> TomlValue

  ||| A table of key-value pairs
  TTbl  : (isValue : Bool) -> SortedMap String TomlValue -> TomlValue

%runElab derive "TomlValue" [Eq,Show,Pretty]

||| Currently, a TOML table is a list of pairs. This might be later
||| changed to some kind of dictionary.
public export
0 TomlTable : Type
TomlTable = SortedMap String TomlValue

--------------------------------------------------------------------------------
--          Tokens
--------------------------------------------------------------------------------

public export
data KeyType = Plain | Quoted | Literal

%runElab derive "KeyType" [Eq,Show,Pretty]

public export
record KeyToken where
  constructor KT
  key    : String
  tpe    : KeyType
  bounds : Bounds

%runElab derive "KeyToken" [Eq,Show,Pretty]

export
Interpolation KeyToken where
  interpolate (KT k t _) = case t of
    Plain   => k
    Quoted  => show k
    Literal => "'" ++ k ++ "'"

||| Type of TOML lexemes
public export
data TomlToken : Type where
  ||| A path of dot-separated keys
  TKey    : List1 KeyToken -> TomlToken

  ||| A (literal) value
  TVal    : TomlValue -> TomlToken

  ||| A single character symbol like '[' or '.'
  TSym    : Char -> TomlToken

  ||| Whitespace containing at least one line break
  NL      : TomlToken

  ||| Whitespace without line breaks (tabs and spaces)
  Space   : TomlToken

  ||| A line comment
  Comment : TomlToken

%runElab derive "TomlToken" [Eq,Show,Pretty]

public export %inline
key1 : KeyToken -> TomlToken
key1 = TKey . singleton

export
interpolateKey : List KeyToken -> String
interpolateKey = concat . intersperse "." . map interpolate

export
Interpolation TomlToken where
  interpolate NL       = "<lf>"
  interpolate Space    = "<space>"
  interpolate Comment  = "<comment>"
  interpolate (TKey s) = interpolateKey $ forget s
  interpolate (TVal v) = show v
  interpolate (TSym c) = show c

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

public export
data TomlParseError : Type where
  KeyExists : List KeyToken -> TomlParseError

export
Interpolation TomlParseError where
  interpolate (KeyExists k) =
    "Trying to overwrite existing key: \{interpolateKey k}"

||| Error type when lexing and parsing TOML files
public export
0 TomlErr : Type
TomlErr = ParseError TomlToken TomlParseError
