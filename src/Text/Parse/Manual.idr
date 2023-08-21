||| This module provides utilities for writing parsers by hand (without
||| using the combinators from module `Text.Parse.Core`).
|||
||| Typically, you get the best performance by using direct pattern matches
||| and explicit recursion. However, for those cases where performance is
||| not the main issue, this module provides some combinators for
||| certain reoccuring patterns.
|||
||| It is strongly recommended to use a lexer and probably one or two
||| cleanup passes over the sequence of generated tokens before parsing,
||| as this can significantly simplify the parsers.
|||
||| Example parsers can be found in sub-packages `parser-json` and
||| `parser-toml`.
|||
||| Note: The raison d'etre of this module is that writing provably total
|||       parsers for (recursive) syntax trees is cumbersome or even impossible
|||       when using parser combinators. In such cases, you have to arrange
|||       things manually, using a `SuffixAcc` helper to proof termination.
|||       For everything else, the combinators in here can make your life
|||       easier.
module Text.Parse.Manual

import public Data.Bool.Rewrite
import public Data.List1
import public Data.List.Shift
import public Data.List.Suffix
import public Data.List.Suffix.Result
import public Data.List.Suffix.Result0

import public Text.Bounds
import public Text.FC
import public Text.ParseError

import public Text.Lex.Manual
import public Text.Lex.Shift

%default total

public export
0 Res :
     (strict : Bool)
  -> (t : Type)
  -> (ts : List $ Bounded t)
  -> (e,a : Type)
  -> Type
Res b t ts e a = Result0 b (Bounded t) ts (Bounded $ ParseError t e) a

public export
0 Grammar : (strict : Bool) -> (t,e,a : Type) -> Type
Grammar strict t e a = (ts : List $ Bounded t) -> Res strict t ts e a

public export
0 AccGrammar : (strict : Bool) -> (t,e,a : Type) -> Type
AccGrammar strict t e a =
     (ts : List $ Bounded t)
  -> (0 acc : SuffixAcc ts)
  -> Res strict t ts e a

||| Converts a grammar requiring a proof of accessibility to a regular
||| grammar.
public export %inline
acc : AccGrammar b t e a -> Grammar b t e a
acc f ts = f ts suffixAcc

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Grammar (x || y) t e a -> Grammar (y || x) t e a
swapOr = swapOr (\k => Grammar k t e a)

public export %inline
orSame : {0 x : _} -> Grammar (x || x) t e a -> Grammar x t e a
orSame = orSame (\k => Grammar k t e a)

public export %inline
orTrue : {0 x : _} -> Grammar (x || True) t e a -> Grammar True t e a
orTrue = orTrue (\k => Grammar k t e a)

public export %inline
orFalse : {0 x : _} -> Grammar (x || False) t e a -> Grammar x t e a
orFalse = orFalse (\k => Grammar k t e a)

public export %inline
swapAnd : {0 x,y : _} -> Grammar (x && y) t e a -> Grammar (y && x) t e a
swapAnd = swapAnd (\k => Grammar k t e a)

public export %inline
andSame : {0 x : _} -> Grammar (x && x) t e a -> Grammar x t e a
andSame = andSame (\k => Grammar k t e a)

public export %inline
andTrue : {0 x : _} -> Grammar (x && True) t e a -> Grammar x t e a
andTrue = andTrue (\k => Grammar k t e a)

public export %inline
andFalse : {0 x : _} -> Grammar (x && False) t e a -> Grammar False t e a
andFalse = andFalse (\k => Grammar k t e a)

--------------------------------------------------------------------------------
--          Simple Grammars
--------------------------------------------------------------------------------

||| Tries to convert the head of the list of tokens.
||| Fails with appropriate errors if the list is empty or the conversion
||| fails.
public export
terminal : (t -> Maybe a) -> Grammar True t e a
terminal f (B v b :: xs) = case f v of
    Just r  => Succ0 r xs
    Nothing => unexpected (B v b)
terminal _ []            = eoi

||| Like `terminal` but fails with a custom error if the conversion fails.
public export
terminalE : (t -> Either e a) -> Grammar True t e a
terminalE f (B v b :: xs) = case f v of
    Right r  => Succ0 r xs
    Left err => custom b err
terminalE _ []            = eoi

||| Tries to drop the given token from the head of the list of tokens.
||| Fails with appropriate errors if the list is empty or the token
||| at the head does not match.
public export
exact : Eq t => t -> Grammar True t e ()
exact v (x::xs) = if v == x.val then Succ0 () xs else expected x.bounds v
exact v []      = expected NoBounds v

||| Look at the next token without consuming any input.
public export
peek : Grammar False t e t
peek (x::xs) = Succ0 x.val (x::xs)
peek []      = eoi

||| Check whether the next token satisfies a predicate. Does not consume.
public export
nextIs : (t -> Bool) -> Grammar False t e t
nextIs f (x::xs) = if f x.val then Succ0 x.val (x :: xs) else unexpected x
nextIs f []      = eoi

||| Check whether the next token equals the given value. Does not consume.
public export
nextEquals : Eq t => t -> Grammar False t e t
nextEquals v (x::xs) =
  if v == x.val then Succ0 x.val (x::xs) else expected x.bounds v
nextEquals v []      = expected NoBounds v

--------------------------------------------------------------------------------
--          Testing Parsers
--------------------------------------------------------------------------------

||| Utility for testing a parses and the error messages it produces
||| at the REPL.
export
testParse :
     {auto _ : Show a}
  -> {auto _ : Interpolation e}
  -> (Origin -> String -> Either (FileContext,e) a)
  -> String
  -> IO ()
testParse f s = case f Virtual s of
  Right res     => putStrLn "Success: \{show res}"
  Left (fc,err) => putStrLn $ printParseError s fc err
