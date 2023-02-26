||| This module provides utilities for writing parsers by hand (without
||| using the combinators from module `Text.Parse.Core`).
|||
||| Typically, you get the best performance by using direct pattern matches
||| and explicit recursion. However, for those cases where performance is
||| not the main issue, this module provides some combinators for
||| certain reoccuring patterns.
|||
||| It is strongly recommended to use a lexer and probably one or two
||| cleanup passes over the sequence of generated tokens, as this can
||| typically simpliy the parsers.
|||
||| Example parsers can be found in sub-packages `parser-json` and
||| `parser-toml`.
module Text.Parse.Manual

import public Data.Bool.Rewrite
import public Data.List.Shift
import public Data.List.Suffix
import public Data.List.Suffix.Result
import public Data.List.Suffix.Result0

import public Text.Bounds
import public Text.FC
import public Text.ParseError

import public Text.Lex.Manual
import public Text.Lex.Shift

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
exact x (B y b :: xs) = if x == y then Succ0 () xs else expected b x
exact x []            = expected NoBounds x

-- --------------------------------------------------------------------------------
-- --          Parentheses
-- --------------------------------------------------------------------------------
-- 
-- ||| Wrapps the given grammar between an opening and closing token.
-- public export
-- between : Eq t => (o,c : t) -> Grammar b t e a -> Grammar True t e a
-- between o c f ts =
--   let Succ0 _ r1   := exact o | Fail0 err => Fail0 err
--       Succ0 res r2 := f r1    | Fail0 err => Fail0 err
--       Succ0 _ r3   := exact c | Fail0 err => Fail0 err
--    in Succ0 res r2 @{strict [T r3, F 

