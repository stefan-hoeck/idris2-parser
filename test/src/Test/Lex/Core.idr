module Test.Lex.Core

import Data.Vect
import Test.Lex.Util

%default total

newlineStr : Gen String
newlineStr = string (linear 0 20) $ element ['\n', '\r']

digitStr : Gen String
digitStr = string (linear 0 20) digit

asciiStr : Gen String
asciiStr = string (linear 0 20) printableAscii

prop_is : Property
prop_is = property $ do
  str <- forAll $ choice [asciiStr, ("=" ++) <$> asciiStr]
  testLex str (is '=') (is '=')

prop_exact : Property
prop_exact = property $ do
  str <- forAll $ choice [asciiStr, ("foo" ++) <$> asciiStr]
  testLex str (exact "foo") (exact "foo")

prop_approx : Property
prop_approx = property $ do
  str <- forAll $ choice [asciiStr, ("fOo" ++) <$> asciiStr]
  testLex str (approx "Foo") (approx "Foo")

prop_newline : Property
prop_newline = property $ do
  str <- forAll [| newlineStr ++ asciiStr |]
  testLex str newline newline

prop_digits : Property
prop_digits = property $ do
  str <- forAll [| digitStr ++ asciiStr |]
  testLex str digits digits

prop_someOf : Property
prop_someOf = property $ do
  str <- forAll asciiStr
  testLex str (someOf "abcdefghijklmnop") (some $ oneOf "abcdefghijklmnop")


export
props : Group
props = MkGroup "Lex.Core" [
    ("prop_is", prop_is)
  , ("prop_exact", prop_exact)
  , ("prop_approx", prop_approx)
  , ("prop_newline", prop_newline)
  , ("prop_digits", prop_digits)
  , ("prop_someOf", prop_someOf)
  ]
