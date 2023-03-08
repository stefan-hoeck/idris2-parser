module JSON.Value

import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          String Encoding
--------------------------------------------------------------------------------

public export
hexChar : Integer -> Char
hexChar 0 = '0'
hexChar 1 = '1'
hexChar 2 = '2'
hexChar 3 = '3'
hexChar 4 = '4'
hexChar 5 = '5'
hexChar 6 = '6'
hexChar 7 = '7'
hexChar 8 = '8'
hexChar 9 = '9'
hexChar 10 = 'a'
hexChar 11 = 'b'
hexChar 12 = 'c'
hexChar 13 = 'd'
hexChar 14 = 'e'
hexChar _  = 'f'

public export
escape : SnocList Char -> Char -> SnocList Char
escape sc '"'  = sc :< '\\' :< '"'
escape sc '\n' = sc :< '\\' :< 'n'
escape sc '\f' = sc :< '\\' :< 'f'
escape sc '\b' = sc :< '\\' :< 'b'
escape sc '\r' = sc :< '\\' :< 'r'
escape sc '\t' = sc :< '\\' :< 't'
escape sc '\\' = sc :< '\\' :< '\\'
escape sc '/'  = sc :< '\\' :< '/'
escape sc c =
  let x := the Integer $ cast c
   in
     if x >= 0x20
       then sc :< c
       else
         let d1 := hexChar $ x `div` 0x1000
             d2 := hexChar $ (x `mod` 0x1000) `div` 0x100
             d3 := hexChar $ (x `mod` 0x100)  `div` 0x10
             d4 := hexChar $ x `mod` 0x10
          in sc :< '\\' :< 'u' :< d1 :< d2 :< d3 :< d4

public export
encode : String -> String
encode s = pack (foldl escape [<'"'] (unpack s) <>> ['"'])

--------------------------------------------------------------------------------
--          JSON
--------------------------------------------------------------------------------

public export
data JSON : Type where
  JNull   : JSON
  JNumber : Double -> JSON
  JBool   : Bool   -> JSON
  JString : String -> JSON
  JArray  : List JSON -> JSON
  JObject : List (String, JSON) -> JSON

%runElab derive "JSON" [Eq]

showValue : SnocList String -> JSON -> SnocList String

showPair : SnocList String -> (String,JSON) -> SnocList String

showArray : SnocList String -> List JSON -> SnocList String

showObject : SnocList String -> List (String,JSON) -> SnocList String

showValue ss JNull              = ss :< "null"
showValue ss (JNumber dbl)      = ss :< show dbl
showValue ss (JBool True)       = ss :< "true"
showValue ss (JBool False)      = ss :< "false"
showValue ss (JString str)      = ss :< encode str
showValue ss (JArray [])        = ss :< "[]"
showValue ss (JArray $ h :: t)  =
  let ss' = showValue (ss :< "[") h
   in showArray ss' t
showValue ss (JObject [])       = ss :< "{}"
showValue ss (JObject $ h :: t) =
  let ss' = showPair (ss :< "{") h
   in showObject ss' t

showPair ss (s,v) = showValue (ss :< encode s :< ":") v

showArray ss [] = ss :< "]"
showArray ss (h :: t) =
  let ss' = showValue (ss :< ",") h in showArray ss' t

showObject ss [] = ss :< "}"
showObject ss (h :: t) =
  let ss' = showPair (ss :< ",") h in showObject ss' t

showImpl : JSON -> String
showImpl v = concat $ showValue Lin v <>> Nil

export %inline
Show JSON where
  show = showImpl
