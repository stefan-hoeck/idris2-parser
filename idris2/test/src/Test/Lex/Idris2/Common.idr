module Test.Lex.Idris2.Common

import Data.String
import Parser.Lexer.Common
import Test.Lex.Util
import Text.Lex.Idris2.Common

%default total

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

unicode : Gen String
unicode = string (linear 0 20) latin

comment : Gen String
comment = [| string (linear 0 5) (pure '-') ++ unicode |]

comments : Gen String
comments = unlines <$> list (linear 0 5) comment

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

prop_comment : Property
prop_comment = property $ do
  str <- forAll comments
  testLex str comment comment

export
props : Group
props = MkGroup "Lex.Idris2.Common" [
    ("prop_comment", prop_comment)
  ]
