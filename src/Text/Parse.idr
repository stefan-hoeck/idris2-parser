module Text.Parse

import public Text.ParseError
import public Text.FC
import public Text.Parse.Core

%default total

||| Utility for testing a parses and the error messages it produces
||| at the REPL.
export
testParse :
     Show a
  => Interpolation e
  => (Origin -> String -> Either (FileContext,e) a)
  -> String
  -> IO ()
testParse f s = case f Virtual s of
  Right res     => putStrLn "Success: \{show res}"
  Left (fc,err) => putStrLn $ printParseError s fc err
