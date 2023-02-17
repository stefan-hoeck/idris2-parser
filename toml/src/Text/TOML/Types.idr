module Text.TOML.Types

import Data.SortedMap
import Derive.Prelude
import Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

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
  TTbl  : SortedMap String TomlValue -> TomlValue

%runElab derive "TomlValue" [Eq,Show]

||| Currently, a TOML table is a list of pairs. This might be later
||| changed to some kind of dictionary.
public export
0 TomlTable : Type
TomlTable = SortedMap String TomlValue

--------------------------------------------------------------------------------
--          Tokens
--------------------------------------------------------------------------------

||| Type of TOML lexemes
public export
data TomlToken : Type where
  ||| A path of dot-separated keys
  TKey    : List1 String -> TomlToken

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

%runElab derive "TomlToken" [Eq,Show]

export
interpolateKey : Key -> String
interpolateKey = concat . intersperse "." . forget . map show

export
Interpolation TomlToken where
  interpolate NL       = "<lf>"
  interpolate Space    = "<space>"
  interpolate Comment  = "<comment>"
  interpolate (TKey s) = interpolateKey s
  interpolate (TVal v) = show v
  interpolate (TSym c) = show c

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

public export
data TomlParseError : Type where
  KeyExists : Key -> TomlParseError

export
Interpolation TomlParseError where
  interpolate (KeyExists k) =
    "Trying to overwrite existing key: \{interpolateKey k}"

||| Error type when lexing and parsing TOML files
public export
0 TomlErr : Type
TomlErr = ParseError TomlToken TomlParseError
