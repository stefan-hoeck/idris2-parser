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

%hide Prelude.(*>)
%hide Prelude.(<*)
%hide Prelude.(<*>)
%hide Prelude.pure

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
exact x (B y b :: xs) = if x == y then Succ0 () xs else expected b x
exact x []            = expected NoBounds x

--------------------------------------------------------------------------------
--          Applicative Syntax
--------------------------------------------------------------------------------

public export %inline
pure : a -> Grammar False t e a
pure v xs = Succ0 v xs

public export %inline
(<*>) : Grammar b1 t e (a -> b) -> Grammar b2 t e a -> Grammar (b1 || b2) t e b
(<*>) gf ga xs =
  let Succ0 f r1 @{p} := gf xs | Fail0 err => Fail0 err
      Succ0 v r2 @{q} := ga r1 | Fail0 err => Fail0 err
   in Succ0 (f v) r2 @{swapOr $ trans q p}

public export %inline
(*>) : Grammar b1 t e () -> Grammar b2 t e a -> Grammar (b1 || b2) t e a
(*>) g1 g2 xs =
  let Succ0 () r1 @{p} := g1 xs | Fail0 err => Fail0 err
      Succ0 v  r2 @{q} := g2 r1 | Fail0 err => Fail0 err
   in Succ0 v r2 @{swapOr $ trans q p}

||| Version of `(*>)` specialized for strict second grammars
public export %inline
seqt : Grammar b t e () -> Grammar True t e a -> Grammar True t e a
seqt x y = orTrue $ x *> y

public export %inline
(<*) : Grammar b1 t e a -> Grammar b2 t e () -> Grammar (b1 || b2) t e a
(<*) g1 g2 xs =
  let Succ0 v  r1 @{p} := g1 xs | Fail0 err => Fail0 err
      Succ0 () r2 @{q} := g2 r1 | Fail0 err => Fail0 err
   in Succ0 v r2 @{swapOr $ trans q p}

--------------------------------------------------------------------------------
--          Parentheses
--------------------------------------------------------------------------------

||| Drops the given token after parsing the given grammar
public export %inline
before : Eq t => Grammar b t e a -> (c : t) -> Grammar True t e a
before f c = orTrue $ f <* exact c

||| Drops the given token before parsing the given grammar
public export %inline
after : Eq t => (o : t) -> Grammar b t e a -> Grammar True t e a
after o f = exact o *> f

||| Wrapps the given grammar between an opening and closing token.
|||
||| Note: This fails with an `Unclosed` exception if the end of
|||       input is reached without closing the opening token.
public export %inline
between : Eq t => (o,c : t) -> Grammar b t e a -> Grammar True t e a
between o c f (B x b :: xs) = case o == x of
  False => expected b o
  True  =>
    let Succ0 v (B y b2 :: ys) := succT (f xs) | res => failInParen b x res
     in if c == y then Succ0 v xs else unexpected (B y b2)
between o c f [] = eoi

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

public export
optional : Grammar b t e a -> Grammar False t e (Maybe a)
optional f ts = weaken $ (Just <$> f ts) <|> Succ0 Nothing ts @{Same}

public export
manyOnto :
     (fatal : ParseError t e -> Bool)
  -> Grammar True t e a
  -> SnocList a
  -> AccGrammar False t e (List a)
manyOnto fatal f sx ts (SA r) = case f ts of
  Succ0 v ys => succF $ manyOnto fatal f (sx :< v) ys r 
  Fail0 x    => if fatal x.val then Fail0 x else Succ0 (sx <>> []) ts

||| Runs the given parser zero or more times, accumulating the
||| results in a list.
|||
||| Note: This will fail in case of a fatal error, which allows for
|||       more fine-grained control over whether a parser is successful
|||       or not.
public export %inline
manyF :
     (fatal : ParseError t e -> Bool)
  -> Grammar True t e a
  -> Grammar False t e (List a)
manyF fatal f ts = manyOnto fatal f [<] ts suffixAcc

||| Runs the given parser zero or more times, accumulating the
||| results in a list.
|||
||| Note: This will never fail, even if the given parser fails
|||       with an error that should be fatal. User `manyF` to
|||       have the ability to specify fatal errors.
public export %inline
many : Grammar True t e a -> Grammar False t e (List a)
many = manyF (const False)

||| Runs the given parser one or more times, accumulating the
||| results in a non-empty list.
|||
||| Note: This will fail in case of a fatal error, even when parsing
|||       the tail of the list, which allows for
|||       more fine-grained control over whether a parser is successful
|||       or not.
public export %inline
someF :
     (fatal : ParseError t e -> Bool)
  -> Grammar True t e a
  -> Grammar True t e (List1 a)
someF fatal f = [| f ::: manyF fatal f|]

||| Runs the given parser one or more times, accumulating the
||| results in a non-empty list.
|||
||| Note: User `manyF` for the ability to specify fatal errors.
public export %inline
some : Grammar True t e a -> Grammar True t e (List1 a)
some = someF (const False)

||| Runs the given parser one or more times, separating occurences with
||| the given separator.
|||
||| Note: This will fail in case of a fatal error, even when parsing
|||       the tail of the list, which allows for
|||       more fine-grained control over whether a parser is successful
|||       or not.
|||
|||       Consider using `sepByExact1` for better error behavior,
|||       if the separator consists of a single, constant token.
public export %inline
sepByF1 :
     (fatal : ParseError t e -> Bool)
  -> (sep : Grammar b t e ())
  -> Grammar True t e a
  -> Grammar True t e (List1 a)
sepByF1 fatal sep f = [| f ::: manyF fatal (seqt sep f)|]

||| Like `sepBy1` but with better error behavior:
||| If the separator was recognized, this fails instead of
||| aborting with a partial list.
public export %inline
sepByExact1 :
     Eq t
  => Eq e
  => (sep : t)
  -> Grammar True t e a
  -> Grammar True t e (List1 a)
sepByExact1 sep = sepByF1 (/= Expected sep) (exact sep)
