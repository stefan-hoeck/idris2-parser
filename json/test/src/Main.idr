module Main

import Data.Vect
import Hedgehog
import JSON.Parser

%default total

key : Gen String
key = string (linear 1 10) printableAscii

prim : Gen JSON
prim = frequency
  [ (1, element [JNull, JBool True, JBool False])
  , (5, JNumber <$> double (exponentialDouble 0 1.0e50))
  , (5, JString <$> string (linear 0 10) unicode)
  ]

json_ : (depth : Nat) -> Gen JSON
json_ Z     = prim
json_ (S k) = frequency
  [ (1, prim)
  , (5, JArray <$> list (linear 0 10) (json_ k))
  , (5, JObject <$> list (linear 0 10) [| MkPair key (json_ k)|])
  ]

prop_roundTrip : Property
prop_roundTrip = property $ do
  v <- forAll (json_ 3)
  let str : String
      str = show v
  
      len : Nat
      len = length str

  classify "Length in (0000,10]"    (len <= 10)
  classify "Length in (0010,50]"    (len > 10 && len <= 50)
  classify "Length in (0050,100]"   (len > 50 && len <= 100)
  classify "Length in (0100,500]"   (len > 100 && len <= 500)
  classify "Length > 500"           (len > 500)

  parseJSON Virtual str === Right v

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

testErr : String -> String -> Property
testErr s exp =
  let res := case parseJSON Virtual s of
        Left (fc,e) => printParseError s fc e
        Right v     => show v
   in property1 $ res === exp

prop_err1 : Property
prop_err1 = testErr #"{"foo?" : nlul}"#
  """
  Error: Unknown or invalid token: nlul

  virtual: 1:11--1:15
   1 | {"foo?" : nlul}
                 ^^^^

  """

prop_err2 : Property
prop_err2 = testErr #"{"foo?" : }"#
  """
  Error: Unexpected '}'

  virtual: 1:11--1:12
   1 | {"foo?" : }
                 ^

  """

prop_err3 : Property
prop_err3 = testErr #"{"foo?" : 12"#
  """
  Error: Unclosed '{'

  virtual: 1:1--1:2
   1 | {"foo?" : 12
       ^

  """

prop_err4 : Property
prop_err4 = testErr "[true,false,"
  """
  Error: Unclosed '['

  virtual: 1:1--1:2
   1 | [true,false,
       ^

  """

prop_err5 : Property
prop_err5 = testErr "[true,false, ?"
  """
  Error: Unknown or invalid token: ?

  virtual: 1:14--1:15
   1 | [true,false, ?
                    ^

  """

prop_err6 : Property
prop_err6 = testErr "1.false"
  """
  Error: Expected a decimal digit ('0' to '9')

  virtual: 1:3--1:4
   1 | 1.false
         ^

  """

prop_err7 : Property
prop_err7 = testErr "1."
  """
  Error: Unexpected end of input

  virtual: 1:3--1:3
   1 | 1.
         ^

  """

prop_err8 : Property
prop_err8 = testErr "0012"
  """
  Error: Unknown or invalid token: 00

  virtual: 1:1--1:3
   1 | 0012
       ^^

  """

 
prop_err9 : Property
prop_err9 = testErr "-0012"
  """
  Error: Unknown or invalid token: -00

  virtual: 1:1--1:4
   1 | -0012
       ^^^

  """

--------------------------------------------------------------------------------
--          main Function
--------------------------------------------------------------------------------

properties : Group
properties = MkGroup "JSON.Parser"
  [ ("prop_roundTrip", prop_roundTrip)
  , ("prop_err1", prop_err1)
  , ("prop_err2", prop_err2)
  , ("prop_err3", prop_err3)
  , ("prop_err4", prop_err4)
  , ("prop_err5", prop_err5)
  , ("prop_err6", prop_err6)
  , ("prop_err7", prop_err7)
  , ("prop_err8", prop_err8)
  , ("prop_err9", prop_err9)
  ]

main : IO ()
main = test [ properties ]
