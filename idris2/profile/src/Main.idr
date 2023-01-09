module Main

import Data.List
import Data.List1
import Data.String
import Parser.Lexer.Common
import Parser.Lexer.Package
import Profile
import System
import Text.Lex.Idris2.Common
import Text.Lex.Idris2.Package

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

ident : Nat -> String
ident n = fastConcat (replicate n "Foo.") ++ "bar"

spaces : Nat -> String
spaces n = fastConcat (replicate n " \t\n")

pkg : String
pkg = """
  package conflict
  version = 0.1.0
  authors = "stefan-hoeck"
  maintainers = "stefan-hoeck"
  license = "BSD3"
  brief = "A simple test for a git conflict"
  -- readme =
  -- homepage =
  -- sourceloc =
  -- bugtracker =

  -- the Idris2 version required (e.g. langversion >= 0.5.1)
  langversion >= 0.5.1

  -- packages to add to search path
  depends = elab-util
          , sop
          , hedgehog

  -- modules to install
  modules = Conflict
          , Conflict.A
          , Conflict.B

  -- main file (i.e. file to load at REPL)
  main = Main

  -- name of executable
  executable = "conflict"
  -- opts =
  sourcedir = "src"
  """

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
  , Group "namespacedIdent" [
       Single "parser_0"   (basic (plex namespacedIdent) $ ident 0)
     , Single "idris2_0"   (basic (ilex namespacedIdent) $ ident 0)
     , Single "parser_1"   (basic (plex namespacedIdent) $ ident 1)
     , Single "idris2_1"   (basic (ilex namespacedIdent) $ ident 1)
     , Single "parser_10"  (basic (plex namespacedIdent) $ ident 10)
     , Single "idris2_10"  (basic (ilex namespacedIdent) $ ident 10)
     ]
  , Group "spaces" [
       Single "parser_1"   (basic (plex spaces) $ spaces 1)
     , Single "idris2_1"   (basic (ilex spacesOrNewlines) $ spaces 1)
     , Single "parser_10"  (basic (plex spaces) $ spaces 10)
     , Single "idris2_10"  (basic (ilex spacesOrNewlines) $ spaces 10)
     ]
  , Group "package" [
       Single "parser"   (basic Idris2.Package.lex pkg)
     , Single "idris2"   (basic Lexer.Package.lex pkg)
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
