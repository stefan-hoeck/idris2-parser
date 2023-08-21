module Main

import Derive.Prelude
import Hedgehog
import Text.Show.PrettyVal.Derive
import Text.Show.Value
import Text.Show.PrettyVal

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Primitives
--------------------------------------------------------------------------------

prop_decnat : Property
prop_decnat = property $ do
  n <- forAll (integer $ exponential 0 0xffffffffffffffff)
  parseValue (show n) === Just (Natural $ show n)

prop_binnat : Property
prop_binnat = property $ do
  cs <- forAll (list (linear 1 20) binit)
  let enc := "0b" ++ pack cs
  parseValue enc === Just (Natural enc)

prop_octnat : Property
prop_octnat = property $ do
  cs <- forAll (list (linear 1 20) octit)
  let enc := "0o" ++ pack cs
  parseValue enc === Just (Natural enc)

prop_hexnat : Property
prop_hexnat = property $ do
  cs <- forAll (list (linear 1 20) hexit)
  let enc := "0x" ++ pack cs
  parseValue enc === Just (Natural enc)

prop_char : Property
prop_char = property $ do
  c <- forAll unicode
  parseValue (show c) === Just (Chr $ show c)

prop_double : Property
prop_double = property $ do
  c <- forAll (double $ exponentialDouble 0.0 1.0e100)
  parseValue (show c) === Just (Dbl $ show c)

prop_string : Property
prop_string = property $ do
  c <- forAll (string (linear 0 10) unicode)
  parseValue (show c) === Just (Str $ show c)

--------------------------------------------------------------------------------
--          Records
--------------------------------------------------------------------------------

public export
record Address where
  constructor MkAddress
  street : String
  zip    : Nat
  city   : String

%runElab derive "Address" [Show, Eq, PrettyVal]

address : Gen Address
address =
  [| MkAddress
     (string (linear 1 10) printableAscii)
     (nat $ exponential 0 1000)
     (string (linear 1 10) printableAscii)
  |]

data Gender = Male | Female | Other

gender : Gen Gender
gender = element [Male,Female,Other]

%runElab derive "Gender" [Show, Eq, PrettyVal]

public export
record User where
  constructor MkUser
  id      : Nat
  name    : String
  age     : Nat
  gender  : Gender
  address : Address

%runElab derive "User" [Show, Eq, PrettyVal]

user : Gen User
user =
  [| MkUser
      (nat $ exponential 0 0xffffffff)
      (string (linear 0 10) unicode)
      (nat $ linear 18 100)
      gender
      address
  |]

prop_gender : Property
prop_gender = property $ do
  u <- forAll gender
  parseValue (show u) === Just (prettyVal u)

prop_address : Property
prop_address = property $ do
  u <- forAll address
  parseValue (show u) === Just (prettyVal u)

prop_user : Property
prop_user = property $ do
  u <- forAll user
  parseValue (show u) === Just (prettyVal u)

--------------------------------------------------------------------------------
--          Sum Types
--------------------------------------------------------------------------------

data ASum : Type where
  AnAddress    : Address -> ASum
  AUserAndBool : User -> Bool -> ASum
  SomeGenders  : List Gender -> ASum

%runElab derive "ASum" [Show,Eq,PrettyVal]

asum : Gen ASum
asum = choice
  [ map AnAddress address
  , [| AUserAndBool user bool |]
  , SomeGenders <$> list (linear 0 10) gender
  ]

prop_asum : Property
prop_asum = property $ do
  u <- forAll asum
  parseValue (show u) === Just (prettyVal u)

--------------------------------------------------------------------------------
--          Tuples
--------------------------------------------------------------------------------

showTriple : Show a => Show b => Show c => (a,b,c) -> String
showTriple (va,vb,vc) = "(\{show va}, \{show vb}, \{show vc})"

showQuad : Show a => Show b => Show c => Show d => (a,b,c, d) -> String
showQuad (va,vb,vc,vd) = "(\{show va}, \{show vb}, \{show vc}, \{show vd})"

pair : Gen (Address,Gender)
pair = [| MkPair address gender |]

triple : Gen (Bool,Address,Gender)
triple = [| trpl bool address gender |]
  where
    trpl : a -> b -> c -> (a,b,c)
    trpl a b c = (a,b,c)
 
quadruple : Gen (Bool,Address,Gender,User)
quadruple = [| quad bool address gender user |]
  where
    quad : a -> b -> c -> d -> (a,b,c,d)
    quad a b c d = (a,b,c,d)

prop_unit : Property
prop_unit = withTests 1 $ property $ do
  parseValue (show ()) === Just (prettyVal ())

prop_pair : Property
prop_pair = property $ do
  u <- forAll pair
  parseValue (show u) === Just (prettyVal u)

prop_triple : Property
prop_triple = property $ do
  u <- forAll triple
  parseValue (showTriple u) === Just (prettyVal u)

prop_quadruple : Property
prop_quadruple = property $ do
  u <- forAll quadruple
  parseValue (showQuad u) === Just (prettyVal u)

--------------------------------------------------------------------------------
--          main Function
--------------------------------------------------------------------------------


properties : Group
properties =
  MkGroup
    "Text.Show.Value"
    [ ("prop_decnat", prop_decnat)
    , ("prop_binnat", prop_binnat)
    , ("prop_octnat", prop_octnat)
    , ("prop_hexnat", prop_hexnat)
    , ("prop_char", prop_char)
    , ("prop_string", prop_string)
    , ("prop_double", prop_double)
    , ("prop_gender", prop_gender)
    , ("prop_address", prop_address)
    , ("prop_user", prop_user)
    , ("prop_asum", prop_asum)
    , ("prop_pair", prop_pair)
    , ("prop_triple", prop_triple)
    , ("prop_quadruple", prop_quadruple)
    , ("prop_unit", prop_unit)
    ]

main : IO ()
main = test [ properties ]
