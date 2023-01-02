module Main

import Data.List
import Data.List1
import Data.String
import Parser.Lexer.Common
import Profile
import System
import Text.Lex.Idris2.Common

%default total

--------------------------------------------------------------------------------
--          Running Lexers
--------------------------------------------------------------------------------

export %inline
plex :
     Text.Lex.Core.Lexer
  -> String
  -> (SnocList (Text.Lex.Bounded.WithBounds String), (Nat,Nat,List Char))
plex l = lex [(l, pack . (<>> []))]

export %inline
ilex :
     Libraries.Text.Lexer.Core.Lexer
  -> String
  -> (List (Libraries.Text.Bounded.WithBounds String), (Int,Int,String))
ilex l = lex [(l, id)]

--------------------------------------------------------------------------------
--          Benchmark Strings
--------------------------------------------------------------------------------

line : Nat -> String
line n = "--" ++ replicate n 'f' ++ "\n"

--------------------------------------------------------------------------------
--          Benchmarks
--------------------------------------------------------------------------------

bench : Benchmark Void
bench = Group "lexer" [
   Group "line comment" [
       Single "parser_1"   (basic (plex comment) $ line 1)
     , Single "idris2_1"   (basic (ilex comment) $ line 1)
     , Single "parser_10"  (basic (plex comment) $ line 10)
     , Single "idris2_10"  (basic (ilex comment) $ line 10)
     , Single "parser_100" (basic (plex comment) $ line 100)
     , Single "idris2_100" (basic (ilex comment) $ line 100)
     ]
  ]

--------------------------------------------------------------------------------
--          main
--------------------------------------------------------------------------------

fromArgs : List String -> String -> Bool
fromArgs [_,p] = case split ('=' ==) p of
  "--only" ::: [s] => isInfixOf s
  _                => const False
fromArgs _ = const True

main : IO ()
main = do
  select <- fromArgs <$> getArgs
  runDefault select Table show bench
