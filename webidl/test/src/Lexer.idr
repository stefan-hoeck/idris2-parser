module Lexer

import Generators
import Text.Parse.Manual
import Text.WebIDL.Lexer

%default total

lex : String -> Either (Bounded ParseErr) (List IdlToken)
lex s = map (map val) $ lexIdl s

lexProp : Show a => Interpolation a => Gen a -> (a -> List IdlToken) -> Property
lexProp gen f = property $ do
  v <- forAll gen
  footnote "Encoded: \{v}"
  lex "\{v}" === Right (f v)

prop_identifier : Property
prop_identifier = lexProp identifier (pure . Ident)

prop_space : Property
prop_space = lexProp space (const [])

prop_stringLit : Property
prop_stringLit = lexProp stringLit (pure . SLit)

prop_intLit : Property
prop_intLit = lexProp intLit (pure . ILit)

prop_floatLit : Property
prop_floatLit = lexProp floatLit (pure . FLit)

prop_comment : Property
prop_comment = lexProp comment (const [])

prop_other : Property
prop_other = lexProp symbol (pure . Other)

export
props : Group
props =
  MkGroup
    "Lexer Properties"
    [ ("prop_identifier", prop_identifier)
    , ("prop_space", prop_space)
    , ("prop_stringLit", prop_stringLit)
    , ("prop_intLit", prop_intLit)
    , ("prop_floatLit", prop_floatLit)
    , ("prop_comment", prop_comment)
    , ("prop_other", prop_other)
    ]
