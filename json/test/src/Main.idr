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


main : IO ()
main = test [ MkGroup "JSON.Parser" [("prop_roundTrip", prop_roundTrip)] ]
