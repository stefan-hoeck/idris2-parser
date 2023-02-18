module Main

import Data.List1
import Data.SortedMap
import Data.String
import System
import System.File
import Text.Parse.Manual
import Text.TOML

%default covering

jsonPath : String -> String
jsonPath s = case split ('.' ==) s of
  h ::: ["toml"] => "\{h}.json"
  _              => s

testValid : String -> IO ()
testValid pth = do
  Right s <- readFile pth | Left err => die "Error when reading \{pth}"
  case parse (FileSrc pth) s of
    Right tbl     => putStrLn "Succesfully read \{pth}"
    Left (fc,err) => die $ printParseError s fc err

testInvalid : String -> IO ()
testInvalid pth = do
  Right s <- readFile pth | Left err => die "Error when reading \{pth}"
  case parse (FileSrc pth) s of
    Right _       => die "Did not fail when parsing \{pth}"
    Left (fc,err) => putStrLn $ printParseError s fc err


main : IO ()
main = do
  _::v::t <- getArgs | _ => die "Invalid args"
  case v of
    "valid"   => for_ t testValid
    "invalid" => for_ t testInvalid
    _         => die "Invalid args"
