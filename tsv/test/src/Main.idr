module Main

import Derive.TSV
import Hedgehog

%default total
%language ElabReflection

data Gender = Male | Female | Other

%runElab derive "Gender" [Show, Eq, TSVEncoder, TSVDecoder]

record Address where
  constructor A
  street : String
  zip    : Nat
  city   : String
  state  : String

%runElab derive "Address" [Show, Eq, TSVEncoder, TSVDecoder]

record User where
  constructor U
  id      : Nat
  name    : String
  gender  : Gender
  salary  : Double
  bonus   : Maybe Double
  address : Address

%runElab derive "User" [Show, Eq, TSVEncoder, TSVDecoder]

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

genders : Gen Gender
genders = element [Male, Female, Other]

text : Gen String
text = string (linear 0 10) printableUnicode

smallNats : Gen Nat
smallNats = nat $ exponential 0 10000

addresses : Gen Address
addresses = [| A text smallNats text text |]

salaries : Gen Double
salaries = double $ exponentialDouble 0.0 1.0e6

users : Gen User
users = [| U smallNats text genders salaries (maybe salaries) addresses |]

strings : Gen String
strings = string (linear 0 10) printableUnicode

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

roundTrip : Show a => Eq a => TSVEncoder a => TSVDecoder a => Gen a -> Property
roundTrip values = property $ do
  vs <- forAll (list (linear 0 30) values)
  readTable {a} {e = Void} Virtual (toTable vs) === Right vs

main : IO ()
main = test [ MkGroup "Text.TSV"
  [ ("prop_gender", roundTrip genders)
  , ("prop_address", roundTrip addresses)
  , ("prop_user", roundTrip users)
  , ("prop_string", roundTrip strings)
  ] ]
