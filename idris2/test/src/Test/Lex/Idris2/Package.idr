module Test.Lex.Idris2.Package

import Data.Either
import Data.Maybe
import Data.String
import Data.Vect
import Parser.Lexer.Package
import Test.Lex.Idris2.Gen
import Text.Lex.Idris2.Package
import Test.Lex.Util

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

0 PToken : Type
PToken = Idris2.Package.Token

0 IToken : Type
IToken = Lexer.Package.Token

toToken : IToken -> PToken
toToken (Comment str) = Comment str
toToken EndOfInput = EndOfInput
toToken Equals = Equals
toToken (DotSepIdent mmi str) = DotSepIdent mmi str
toToken Separator = Separator
toToken Dot = Dot
toToken LTE = LTE
toToken GTE = GTE
toToken LT = LT
toToken GT = GT
toToken EqOp = EqOp
toToken AndOp = AndOp
toToken Space = Space
toToken (StringLit str) = StringLit str
toToken (IntegerLit i) = IntegerLit i

toRes :
     Either (Int,Int,String) (List (IBounded IToken))
  -> Either (Nat,Nat,String) (List (PBounded PToken))
toRes (Left (l,c,s)) = Left (cast l, cast c, s)
toRes (Right x) = Right $ map (toWithBounds . map toToken) x

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

prop_package : Property
prop_package = property $ do
  str <- forAll package
  lex str === toRes (lex str)

prop_success : Property
prop_success = property $ do
  str <- forAll package
  let res := Idris2.Package.lex str
  footnote (show res)
  assert (isRight res)

export
props : Group
props = MkGroup "Lex.Idris2.Package" [
    ("prop_package", prop_package)
  , ("prop_success", prop_success)
  ]
