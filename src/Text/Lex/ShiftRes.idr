module Text.Lex.ShiftRes

import Data.Nat
import Text.Lex.SuffixRes
import public Data.List.Shift

%default total

--------------------------------------------------------------------------------
--          ShiftRes
--------------------------------------------------------------------------------

||| Result of running a lexer once: The lexer either stops, when
||| it can no longer consume any characters, or it shifts some characters
||| from the head of the list of remaining characters to the tail of the
||| snoclist or already recognised characters.
|||
||| @ strict : `True` if we can proof that the lexer recognised at least
|||            one character
||| @ st     : the initial snoclist of already recognised characters
||| @ ts     : the initial list of remaining characters
public export
data ShiftRes :
     (strict : Bool)
  -> (st     : SnocList t)
  -> (ts     : List t)
  -> Type where

  Stop : ShiftRes s st ts

  Succ :
       {0 st    : SnocList t}
    -> {0 ts    : List t}
    -> {pre     : SnocList t}
    -> (post    : List t)
    -> {auto sh : Shift b pre post st ts}
    -> ShiftRes b st ts

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export
swapOr : {0 x,y : _} -> ShiftRes (x || y) st ts -> ShiftRes (y || x) st ts
swapOr = swapOr (\k => ShiftRes k st ts)

public export %inline
orSame : {0 x : _} -> ShiftRes (x || x) st ts -> ShiftRes x st ts
orSame = orSame (\k => ShiftRes k st ts)

public export %inline
orTrue : {0 x : _} -> ShiftRes (x || True) st ts -> ShiftRes True st ts
orTrue = orTrue (\k => ShiftRes k st ts)

public export %inline
orFalse : {0 x : _} -> ShiftRes (x || False) st ts -> ShiftRes x st ts
orFalse = orFalse (\k => ShiftRes k st ts)

public export %inline
swapAnd : {0 x,y : _} -> ShiftRes (x && y) st ts -> ShiftRes (y && x) st ts
swapAnd = swapAnd (\k => ShiftRes k st ts)

public export %inline
andSame : {0 x : _} -> ShiftRes (x && x) st ts -> ShiftRes x st ts
andSame = andSame (\k => ShiftRes k st ts)

public export %inline
andTrue : {0 x : _} -> ShiftRes (x && True) st ts -> ShiftRes x st ts
andTrue = andTrue (\k => ShiftRes k st ts)

public export %inline
andFalse : {0 x : _} -> ShiftRes (x && False) st ts -> ShiftRes False st ts
andFalse = andFalse (\k => ShiftRes k st ts)

public export %inline
weaken : {0 x : _} -> ShiftRes x st ts -> ShiftRes False st ts
weaken (Succ xs @{p}) = Succ xs @{weaken p}
weaken Stop = Stop

public export %inline
weakens : {0 x : _} -> ShiftRes True st ts -> ShiftRes x st ts
weakens (Succ xs @{p}) = Succ xs @{weakens p}
weakens Stop = Stop

public export %inline
and1 : {0 x : _} -> ShiftRes x st ts -> ShiftRes (x && y) st ts
and1 (Succ xs @{p}) = Succ xs @{and1 p}
and1 Stop = Stop

public export %inline
and2 : {0 x : _} -> ShiftRes x st ts -> ShiftRes (y && x) st ts
and2 r = swapAnd $ and1 r

public export %inline
trans : ShiftRes b1 sx xs -> Shift b2 sx xs sy ys -> ShiftRes (b1 || b2) sy ys
trans (Succ ts @{p}) q = Succ ts @{p ~> q}
trans Stop           _ = Stop

||| Operator alias for `trans`.
public export %inline
(~>) : ShiftRes b1 sx xs -> Shift b2 sx xs sy ys -> ShiftRes (b1 || b2) sy ys
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) : Shift b1 sx xs sy ys -> ShiftRes b2 sx xs -> ShiftRes (b1 || b2) sy ys
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) : ShiftRes b1 sx xs -> Shift b2 sx xs sy ys -> ShiftRes False sy ys
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Shift` dominates.
public export %inline
(~~>) : ShiftRes b1 sx xs -> Shift True sx xs sy ys -> ShiftRes b1 sy ys
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Shift` dominates.
public export %inline
(<~~) : Shift b1 sx xs sy ys -> ShiftRes True sx xs -> ShiftRes b1 sy ys
(<~~) x y = weakens $ y ~> x

public export
suffix : (SnocList t -> a) -> ShiftRes {t} b st ts -> SuffixRes b t ts a
suffix f Stop                    = Fail
suffix f (Succ {pre} post @{sh}) = Succ (f pre) post @{suffix sh}

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) : ShiftRes b1 sx xs -> Lazy (ShiftRes b2 sx xs) -> ShiftRes (b1 && b2) sx xs
Succ post @{q} <|> _ = Succ post @{and1 q}
Stop           <|> q = and2 q

--------------------------------------------------------------------------------
--          Shifters
--------------------------------------------------------------------------------

||| A `Shifter` is a function that moves items from the head of a list
||| to the tail of a snoclist.
|||
||| A lexer is just a fancy wrapper around a `Shifter`, and *running* a
||| lexer (via function `run`) leads to the underlying `Shifter`
||| (see `Text.Lex.Core`).
public export
0 Shifter : (b : Bool) -> Type -> Type
Shifter b t = (st : SnocList t) -> (ts : List t) -> ShiftRes b st ts

||| Shifter that recognises the empty String
public export
eoi : Shifter False t
eoi _ [] = Succ []
eoi _ _  = Stop

||| Shifter that always fails
public export
stop : Shifter True t
stop _ _ = Stop

public export
0 AutoShift : Bool -> Type -> Type
AutoShift s a =
     {0 b     : Bool}
  -> {0 giro  : SnocList a}
  -> {0 orig  : List a}
  -> {pre     : SnocList a}
  -> (post    : List a)
  -> {auto sh : Shift b pre post giro orig}
  -> ShiftRes (s || b) giro orig

||| A shifter that doesn't move anything.
public export
same : AutoShift False a
same post = Succ post

||| A shifter that moves exactly one value
public export
tail : AutoShift True a
tail (x :: xs) = Succ xs
tail []        = Stop

||| A shifter that moves exactly one value, if
||| it fulfills the given predicate.
public export
one : (t -> Bool) -> AutoShift True t
one f (x :: xs) = if f x then Succ xs else Stop
one _ []        = Stop

||| A shifter that moves items while the given predicate returns
||| `True`
public export
takeWhile : (a -> Bool) -> AutoShift False a
takeWhile f (x :: xs) = if f x then takeWhile f xs else Succ (x::xs)
takeWhile f []        = Succ []

||| A strict version of `takeWhile`, which moves at least one item.
public export
takeWhile1 : (a -> Bool) -> AutoShift True a
takeWhile1 f (x :: xs) = if f x then takeWhile f xs else Stop
takeWhile1 f []        = Stop

||| A shifter that moves items while the give predicate returns
||| `False`
public export
takeUntil : (t -> Bool) -> AutoShift False t
takeUntil f (x :: xs) = if f x then Succ (x::xs) else takeUntil f xs
takeUntil f []        = Succ []

||| A strict version of `takeUntil`, which moves at least one item.
public export
takeUntil1 : (t -> Bool) -> AutoShift True t
takeUntil1 f (x :: xs) = if f x then Stop else takeUntil f xs
takeUntil1 f []        = Stop

||| A shifter that moves digits.
public export
digits : AutoShift False Char
digits (x :: xs) = if isDigit x then digits xs else Succ(x::xs)
digits []        = Succ []

||| A strict version of `digits`.
public export
digits1 : AutoShift True Char
digits1 (x :: xs) = if isDigit x then digits xs else Stop
digits1 []        = Stop

||| A shifter that takes moves an integer prefix
public export
int : AutoShift True Char
int ('-' :: xs) = digits1 {b} xs
int xs          = digits1 {b} xs

||| Like `int` but also allows an optional leading `'+'` character.
public export
intPlus : AutoShift True Char
intPlus ('+' :: xs) = digits1 {b} xs
intPlus xs          = int {b} xs

dot,rest,digs,exp : AutoShift False Char
exp ('e' :: xs) = weakens $ intPlus {b} xs
exp ('E' :: xs) = weakens $ intPlus {b} xs
exp xs          = Succ xs

dot (x :: xs) = if isDigit x then dot xs else exp (x::xs)
dot []        = Succ []

rest ('.' :: x :: xs) = if isDigit x then dot xs else Stop
rest xs               = exp xs

digs (x :: xs) = if isDigit x then digs xs else rest (x::xs)
digs []        = Succ []

digs0 : AutoShift True Char
digs0 ('0' :: xs) = rest xs
digs0 (x :: xs)   = if isDigit x then digs xs else Stop
digs0 []          = Stop

||| A shifter for recognizing JSON numbers
public export
number : AutoShift True Char
number ('-' :: xs) = digs0 {b} xs
number xs          = digs0 {b} xs

public export
take : (n : Nat) -> AutoShift (isSucc n) a
take (S k) (x::xs) = orTrue $ take k xs
take 0     xs      = Succ xs
take (S k) []      = Stop

public export
exact : Eq t => List t -> AutoShift True t
exact (v :: []) (x :: xs) = if v == x then Succ xs else Stop
exact (v :: vs) (x :: xs) = if v == x then exact {b} vs xs else Stop
exact _         _         = Stop

str : AutoShift True Char
str ('"'       :: xs) = Succ xs
str ('\\' :: x :: xs) = str {b} xs
str (x         :: xs) = str {b} xs
str []                = Stop

public export
string : AutoShift True Char
string ('"' :: xs) = str {b} xs
string _           = Stop
