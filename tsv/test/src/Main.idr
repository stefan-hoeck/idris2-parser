module Main

import Derive.TSV

%default total
%language ElabReflection

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
  salary  : Double
  address : Address

%runElab derive "User" [Show, Eq, TSVEncoder, TSVDecoder]

users : List User
users =
  [ U 1 "Stefan" 1000.13 (A "my street" 8000 "Zurich" "Switzerland")
  , U 2 "Sarah" 2000.13 (A "her street" 3000 "Bern" "Switzerland")
  ]

main : IO ()
main = putStrLn $ toTable users
