module Parser

import Text.WebIDL.Encoder
import Text.WebIDL.Parser
import Text.WebIDL.Parser.Util
import Generators

prp : Eq a => Show a => Encoder a -> Gen a -> Rule b a -> Property
prp enc gen p = property $ do
  v <- forAll gen
  let str : String
      str = enc v
  
      len : Integer
      len = natToInteger $ length str
  
  classify "Length in (0000,10]"       (len <= 10)
  classify "Length in (0010,50]"    (len > 10 && len <= 50)
  classify "Length in (0050,100]"   (len > 50 && len <= 100)
  classify "Length in (0100,500]"   (len > 100 && len <= 500)
  classify "Length in (0500,1000]"  (len > 500 && len <= 1000)
  classify "Length in (1000,10000]" (len > 1000 && len <= 10000)
  
  footnote ("Encoded: " ++ str)
  
  parseIdl p str === Right v

prop_extAttributes : Property
prop_extAttributes = prp extAttribute (extAttribute 4) extAttribute

prop_primitiveType : Property
prop_primitiveType = prp primitive primitive primitive

prop_idlType : Property
prop_idlType = prp idlType (idlType 5) idlType

prop_partOrDef : Property
prop_partOrDef = prp partOrDef partOrDef partOrDef

export
props : Group
props = MkGroup "Parser Properties"
  [ ("prop_extAttributes", prop_extAttributes)
  , ("prop_primitiveType", prop_primitiveType)
  , ("prop_idlType", prop_idlType)
  , ("prop_part", prop_partOrDef)
  ]
