module Test.Lex.Idris2.Package

import Data.Either
import Data.Maybe
import Data.String
import Data.Vect
import Parser.Lexer.Package
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
     Either (Int,Int,String) (List (IWithBounds IToken))
  -> Either (Nat,Nat,String) (List (PWithBounds PToken))
toRes (Left (l,c,s)) = Left (cast l, cast c, s)
toRes (Right x) = Right $ map (toWithBounds . map toToken) x

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

spaces : Gen String
spaces = pack <$> list (linear 1 3) (element [' ', '\t', '\n', '\r'])

optSpaces : Gen String
optSpaces = choice [spaces, pure ""]

spaced : List (Gen String) -> Gen String
spaced gs = concat <$> sequence (intersperse spaces gs)

maybeSpaced : List (Gen String) -> Gen String
maybeSpaced gs = concat <$> sequence (intersperse optSpaces gs)

name : Gen String
name = [| (\c,s => singleton c ++ s) lower (string (linear 0 5) alphaNum) |]

hident : Gen String
hident = concat . intersperse "-" <$> list (linear 1 3) name

pkgName : Gen String
pkgName = spaced [pure "package", hident]

version : Gen String
version = choice [lower, upper, between, exact, pure ""]
  where lower, upper, between,exact,vers : Gen String

        prefixVersion : String -> Maybe String -> String -> String
        prefixVersion a b c = a ++ fromMaybe "" b ++ c

        vv : String -> Gen String
        vv s = maybeSpaced [pure s, vers]

        vers = concat . intersperse "." . map show <$>
               list (linear 1 4) (nat $ linear 0 100)

        lower = choice [ vv ">", vv ">=" ]
        upper = choice [ vv "<", vv "<=" ]
        between = maybeSpaced [lower, pure "&&", upper]
        exact =  vv "=="

fld : String -> Gen String -> Gen String
fld nm g =
  [| (\s1,s2,s3,s => s1 ++ nm ++ s2 ++ "=" ++ s3 ++ s) spaces spaces g spaces |]

stringLit : Gen String
stringLit = quote [<'"'] . unpack <$> string (linear 0 20) unicode
  where quote : SnocList Char -> List Char -> String
        quote sc (x :: xs) = case x of
          '\\' => quote (sc :< '\\' :< '\\') xs
          '\n' => quote (sc :< '\\' :< '\n') xs
          '\r' => quote (sc :< '\\' :< '\r') xs
          '\t' => quote (sc :< '\\' :< '\t') xs
          '"'  => quote (sc :< '\\' :< '"') xs
          c    => if isControl c then quote sc xs else quote (sc :< c) xs
        quote sc []        = pack (sc :< '"')

field : Gen String
field = choice [
    fld "author" stringLit
  , fld "maintainers" stringLit
  , fld "license" stringLit
  , fld "brief" stringLit
  , fld "readme" stringLit
  , fld "sourceloc" stringLit
  , fld "bugtracker" stringLit
  , fld "executable" stringLit
  , fld "opts" stringLit
  , fld "sourcedir" stringLit
  , fld "builddir" stringLit
  , fld "outputdir" stringLit
  , fld "prebuild" stringLit
  , fld "postbuild" stringLit
  , fld "preinstall" stringLit
  , fld "postinstall" stringLit
  , fld "preclean" stringLit
  , fld "postclean" stringLit
  , fld "langversion" version
  ]

-- depends =

-- modules = Conflict

-- main =

pkgRest : Gen String
pkgRest = concat <$> list (linear 0 20) field

package : Gen String
package = [| pkgName ++ pkgRest |]

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
