module Text.TOML.Types

import Text.ParseError
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

||| Data type for trees of TOML data.
public export
data TomlValue : Type where
  ||| A string literal
  TStr  : String  -> TomlValue

  ||| A boolean literal
  TBool : Bool  -> TomlValue

  ||| A negative interger
  TNeg  : Nat -> TomlValue

  ||| A natural number
  TNat  : Nat -> TomlValue

  ||| A floating point number
  TDbl  : Double  -> TomlValue

  ||| An array of values
  TArr  : List TomlValue -> TomlValue

  ||| An table of key-value pairs
  TTbl  : List (String,TomlValue) -> TomlValue

%runElab derive "TomlValue" [Eq,Show]

||| Currently, a TOML table is a list of pairs. This might be later
||| changed to some kind of dictionary.
public export
0 TomlTable : Type
TomlTable = List (String,TomlValue)

--------------------------------------------------------------------------------
--          Tokens
--------------------------------------------------------------------------------

||| Type of TOML lexemes
public export
data TomlToken : Type where
  ||| A path of dot-separated keys
  TKey    : List String -> TomlToken

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
Interpolation TomlToken where
  interpolate NL       = "<lf>"
  interpolate Space    = "<space>"
  interpolate Comment  = "<comment>"
  interpolate (TKey s) = concat . intersperse "." $ map show s
  interpolate (TVal v) = show v
  interpolate (TSym c) = show c

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

||| Error type when lexing and parsing TOML files
public export
0 TOMLErr : Type
TOMLErr = ParseError TomlToken Void
