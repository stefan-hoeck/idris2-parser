module Main

import JSON
import Data.List1
import Data.SortedMap
import Data.String
import System
import System.File
import Text.Parse.Manual
import Text.TOML

%default covering

--------------------------------------------------------------------------------
--          Converting to JSON
--------------------------------------------------------------------------------

val : (t,v : String) -> JSON
val t v = JObject [("type", JString t), ("value", JString v)]

toJ : TomlValue -> JSON
toJ (TStr s) = val "string" s
toJ (TBool x) = val "bool" (toLower $ show x)
toJ (TInt i) = val "integer" (show i)
toJ (TDbl dbl) = val "float" (show dbl)
toJ (TArr xs) = JArray $ map toJ xs
toJ (TTbl isValue x) = JObject $ mapSnd toJ <$> SortedMap.toList x

--------------------------------------------------------------------------------
--          Test Runners
--------------------------------------------------------------------------------

tryRead : String -> IO String
tryRead pth = do
  Right s <- readFile pth | Left err => die "Error when reading \{pth}"
  pure s

jsonPath : String -> String
jsonPath s = case split ('.' ==) s of
  h ::: ["toml"] => "\{h}.json"
  _              => s

testValid : String -> IO ()
testValid pth = do
  ts <- tryRead pth
  js <- tryRead (jsonPath pth)
  case TTbl False <$> Parser.parse (FileSrc pth) ts of
    Right tbl     => case parseJSON (FileSrc $ jsonPath pth) js of
      Right json    => case toJ tbl == json of
        True  => putStrLn "Successfully parsed \{pth}"
        False => do
          putStrLn "Error when parsing \{pth}"
          putStrLn "Expected \{show json}"
          putStrLn "But got \{show $ toJ tbl}"
          die "Exiting..."
      Left (fc,err) => die $ printParseError ts fc err
    Left (fc,err) => die $ printParseError ts fc err

testInvalid : String -> IO ()
testInvalid pth = do
  s <- tryRead pth
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
