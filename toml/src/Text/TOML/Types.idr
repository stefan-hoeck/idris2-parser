module Text.TOML.Types

import public Data.Time.Time
import public Data.SortedMap
import Derive.Prelude
import Text.Bounds
import Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Floating Point Literals
--------------------------------------------------------------------------------

public export
data TomlFloat : Type where
  NaN   : TomlFloat
  Infty : Maybe Sign -> TomlFloat
  Float : Double -> TomlFloat

%runElab derive "TomlFloat" [Eq,Show]

export
Interpolation TomlFloat where
  interpolate NaN = "nan"
  interpolate (Infty x) =
    let s = maybe "" interpolate x
     in "\{s}inf"
  interpolate (Float dbl) = show dbl

--------------------------------------------------------------------------------
--          Table Type
--------------------------------------------------------------------------------

public export
data TableType = None | Inline | Table

%runElab derive "TableType" [Show,Eq,Ord]

public export
data ArrayType = Static | OfTables

%runElab derive "ArrayType" [Show,Eq,Ord]

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
  TStr  : String -> TomlValue

  ||| A boolean literal
  TBool : Bool -> TomlValue

  ||| A date-time literal
  TTime : AnyTime -> TomlValue

  ||| An integer
  TInt  : Integer -> TomlValue

  ||| A floating point number
  TDbl  : TomlFloat  -> TomlValue

  ||| An array of values
  TArr  : ArrayType -> SnocList TomlValue -> TomlValue

  ||| A table of key-value pairs
  TTbl  : TableType -> SortedMap String TomlValue -> TomlValue

%runElab derive "TomlValue" [Eq,Show]

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

%runElab derive "KeyType" [Eq,Show]

public export
record KeyToken where
  constructor KT
  key    : String
  tpe    : KeyType
  bounds : Bounds

%runElab derive "KeyToken" [Eq,Show]

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

  ||| A single or multi-character symbol like "[", "[[" or "."
  TSym    : String -> TomlToken

  ||| Whitespace containing at least one line break
  NL      : TomlToken

  ||| Whitespace without line breaks (tabs and spaces)
  Space   : TomlToken

  ||| A line comment
  Comment : TomlToken

%runElab derive "TomlToken" [Eq,Show]

public export %inline
key1 : KeyToken -> TomlToken
key1 = TKey . singleton

export
interpolateKey : List KeyToken -> String
interpolateKey = concat . intersperse "." . map interpolate

export
Interpolation TomlToken where
  interpolate NL       = "<line break>"
  interpolate Space    = "<space>"
  interpolate Comment  = "<comment>"
  interpolate (TKey s) = interpolateKey $ forget s
  interpolate (TVal v) = case v of
    TStr str => "string literal"
    TBool x  => toLower $ show x
    TInt i   => show i
    TTime i  => interpolate i
    TDbl dbl => interpolate dbl
    TArr _ _ => "array"
    TTbl _ x => "table"
  interpolate (TSym c) = show c

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

public export
data TomlParseError : Type where
  ValueExists       : List KeyToken -> TomlParseError
  InlineTableExists : List KeyToken -> TomlParseError
  TableExists       : List KeyToken -> TomlParseError
  StaticArray       : List KeyToken -> TomlParseError
  ExpectedKey       : TomlParseError

%runElab derive "TomlParseError" [Eq,Show]

export
Interpolation TomlParseError where
  interpolate ExpectedKey = "Expected a key"
  interpolate (ValueExists k) =
    "Trying to overwrite existing value: \{interpolateKey k}"
  interpolate (InlineTableExists k) =
    "Trying to modify existing inline table: \{interpolateKey k}"
  interpolate (TableExists k) =
    "Trying to overwrite existing table: \{interpolateKey k}"
  interpolate (StaticArray k) =
    "Trying to modify a static array: \{interpolateKey k}"

||| Error type when lexing and parsing TOML files
public export
0 TomlErr : Type
TomlErr = ParseError TomlToken TomlParseError
