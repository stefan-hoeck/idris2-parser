module Text.Lex.Shift

import Data.List
import Data.Nat
import public Text.Lex.Manual
import public Data.List.Shift

%default total

--------------------------------------------------------------------------------
--          ShiftRes
--------------------------------------------------------------------------------

||| Result of running a lexer once: The lexer either stops, when
||| it can no longer consume any characters, or it shifts some characters
||| from the head of the list of remaining characters to the tail of the
||| snoclist of already recognised characters.
|||
||| @ st     : the initial snoclist of already recognised characters
||| @ ts     : the initial list of remaining characters
public export
data ShiftRes :
     (b : Bool)
  -> (t : Type)
  -> (st : SnocList t)
  -> (ts : List t)
  -> Type where
  Succ :
       {0 t     : Type}
    -> {0 b     : Bool}
    -> {0 st    : SnocList t}
    -> {0 ts    : List t}
    -> {pre     : SnocList t}
    -> (post    : List t)
    -> {auto sh : Shift b t pre post st ts}
    -> ShiftRes b t st ts

  Stop :
       {0 t   : Type}
    -> {0 b     : Bool}
    -> {0 st,se,ee  : SnocList t}
    -> {ts,errStart : List t}
    -> (start : Shift False t se errStart st ts)
    -> (0 errEnd : List t)
    -> {auto end : Shift False t ee errEnd se errStart}
    -> StopReason
    -> ShiftRes b t st ts

public export %inline
suffix : (SnocList t -> a) -> ShiftRes True t [<] ts -> SuffixRes t ts a
suffix f (Succ {pre} post @{sh}) = Succ (f pre) post @{suffix sh} 
suffix f (Stop s e x @{sh})      = Fail (suffix s) e x @{suffix sh}

--------------------------------------------------------------------------------
--         Conversions
--------------------------------------------------------------------------------

public export
swapOr : {0 x,y : _} -> ShiftRes (x || y) t st ts -> ShiftRes (y || x) t st ts
swapOr = swapOr (\k => ShiftRes k t st ts)

public export %inline
orSame : {0 x : _} -> ShiftRes (x || x) t st ts -> ShiftRes x t st ts
orSame = orSame (\k => ShiftRes k t st ts)

public export %inline
orTrue : {0 x : _} -> ShiftRes (x || True) t st ts -> ShiftRes True t st ts
orTrue = orTrue (\k => ShiftRes k t st ts)

public export %inline
orFalse : {0 x : _} -> ShiftRes (x || False) t st ts -> ShiftRes x t st ts
orFalse = orFalse (\k => ShiftRes k t st ts)

public export %inline
swapAnd : {0 x,y : _} -> ShiftRes (x && y) t st ts -> ShiftRes (y && x) t st ts
swapAnd = swapAnd (\k => ShiftRes k t st ts)

public export %inline
andSame : {0 x : _} -> ShiftRes (x && x) t st ts -> ShiftRes x t st ts
andSame = andSame (\k => ShiftRes k t st ts)

public export %inline
andTrue : {0 x : _} -> ShiftRes (x && True) t st ts -> ShiftRes x t st ts
andTrue = andTrue (\k => ShiftRes k t st ts)

public export %inline
andFalse : {0 x : _} -> ShiftRes (x && False) t st ts -> ShiftRes False t st ts
andFalse = andFalse (\k => ShiftRes k t st ts)

public export
weaken : {0 x : _} -> ShiftRes x t st ts -> ShiftRes False t st ts
weaken (Succ xs @{p}) = Succ xs @{weaken p}
weaken (Stop s e r) = Stop s e r

public export
weakens : {0 x : _} -> ShiftRes True t st ts -> ShiftRes x t st ts
weakens (Succ xs @{p}) = Succ xs @{weakens p}
weakens (Stop s e r) = Stop s e r

public export
and1 : {0 x : _} -> ShiftRes x t st ts -> ShiftRes (x && y) t st ts
and1 (Succ xs @{p})= Succ xs @{and1 p}
and1 (Stop s e r)  = Stop s e r

public export %inline
and2 : {0 x : _} -> ShiftRes x t st ts -> ShiftRes (y && x) t st ts
and2 r = swapAnd $ and1 r

public export %inline
trans : {ys : _} -> ShiftRes b1 t sx xs -> Shift b2 t sx xs sy ys -> ShiftRes (b1 || b2) t sy ys
trans (Succ ts @{p})    q = Succ ts @{p ~> q}
trans (Stop x y z @{p}) q = Stop (x ~?> q) y z

||| Operator alias for `trans`.
public export %inline
(~>) : {ys : _} -> ShiftRes b1 t sx xs -> Shift b2 t sx xs sy ys -> ShiftRes (b1 || b2) t sy ys
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) : {ys : _} -> Shift b1 t sx xs sy ys -> ShiftRes b2 t sx xs -> ShiftRes (b1 || b2) t sy ys
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) : {ys : _} -> ShiftRes b1 t sx xs -> Shift b2 t sx xs sy ys -> ShiftRes False t sy ys
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Shift` dominates.
public export %inline
(~~>) : {ys : _} -> ShiftRes b1 t sx xs -> Shift True t sx xs sy ys -> ShiftRes b1 t sy ys
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Shift` dominates.
public export %inline
(<~~) : {ys : _} -> Shift b1 t sx xs sy ys -> ShiftRes True t sx xs -> ShiftRes b1 t sy ys
(<~~) x y = weakens $ y ~> x

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) :
     ShiftRes b1 t sx xs
  -> Lazy (ShiftRes b2 t sx xs)
  -> ShiftRes (b1 && b2) t sx xs
s@(Succ {}) <|> _ = and1 s
_           <|> r = and2 r

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
Shifter b t = (st : SnocList t) -> (ts : List t) -> ShiftRes b t st ts

public export
0 AutoShift : Bool -> Type -> Type
AutoShift s t =
     {0 b     : Bool}
  -> {0 giro  : SnocList t}
  -> {orig    : List t}
  -> {pre     : SnocList t}
  -> (post    : List t)
  -> {auto sh : Shift b t pre post giro orig}
  -> ShiftRes (s || b) t giro orig

public export
range :
     {0 b1,b2 : Bool}
  -> {0 giro,ruc,tser : SnocList t}
  -> {orig,cur   : List t}
  -> StopReason
  -> (shiftCur   : Shift b1 t ruc cur giro orig)
  -> (0 rest     : List t)
  -> {auto sr    : Shift False t tser rest ruc cur}
  -> ShiftRes b2 t giro orig
range r sc rest = Stop (weaken sc) rest r

public export %inline
invalidEscape :
     {0 b1,b2 : Bool}
  -> {0 giro,ruc,tser : SnocList t}
  -> {orig,cur   : List t}
  -> (shiftCur   : Shift b1 t ruc cur giro orig)
  -> (0 rest     : List t)
  -> {auto sr    : Shift False t tser rest ruc cur}
  -> ShiftRes b2 t giro orig
invalidEscape = range InvalidEscape

public export %inline
unknownRange :
     {0 b1,b2 : Bool}
  -> {0 giro,ruc,tser : SnocList t}
  -> {orig,cur   : List t}
  -> (shiftCur   : Shift b1 t ruc cur giro orig)
  -> (0 rest     : List t)
  -> {auto sr    : Shift False t tser rest ruc cur}
  -> ShiftRes b2 t giro orig
unknownRange = range UnknownToken

public export
whole :
     {0 b           : Bool}
  -> {0 ruc,giro    : SnocList t}
  -> StopReason
  -> (0 cur         : List t)
  -> {orig          : List t}
  -> {auto shiftCur : Shift False t ruc cur giro orig}
  -> ShiftRes b t giro orig
whole r cur = Stop Same cur r

public export %inline
unknown :
     {0 b           : Bool}
  -> {0 ruc,giro    : SnocList t}
  -> (0 cur         : List t)
  -> {orig          : List t}
  -> {auto shiftCur : Shift False t ruc cur giro orig}
  -> ShiftRes b t giro orig
unknown = whole UnknownToken

public export
failEOI :
     {0 b1,b2 : Bool}
  -> {0 ruc,giro : SnocList t}
  -> {0 cur      : List t}
  -> {orig       : List t}
  -> (shiftCur   : Shift b1 t ruc cur giro orig)
  -> ShiftRes b2 t giro orig
failEOI sc = Stop {end = weaken sc} Same cur EOI

public export
failEmpty :
     {0 b        : Bool}
  -> {0 ruc,giro : SnocList t}
  -> {orig       : List t}
  -> {auto sh    : Shift False t ruc [] giro orig}
  -> ShiftRes b t giro orig
failEmpty = Stop sh [] EOI

--------------------------------------------------------------------------------
--          General Purpose Shifters
--------------------------------------------------------------------------------

||| Shifter that recognises the empty String
public export
eoi : Shifter False t
eoi _ []      = Succ []
eoi _ (x::xs) = whole ExpectedEOI xs

||| Shifter that always fails
public export
fail : Shifter True t
fail _ []      = failEmpty
fail _ (x::xs) = unknown xs

||| A shifter that moves exactly one value, if
||| it fulfills the given predicate.
public export
one : (t -> Bool) -> AutoShift True t
one f (x :: xs) = if f x then Succ xs else unknownRange sh xs
one _ []        = failEOI sh

||| A shifter that moves items while the given predicate returns
||| `True`
public export
takeWhile : (t -> Bool) -> AutoShift False t
takeWhile f (x :: xs) = if f x then takeWhile f xs else Succ (x::xs)
takeWhile f []        = Succ []

||| A strict version of `takeWhile`, which moves at least one item.
public export
takeWhile1 : (t -> Bool) -> AutoShift True t
takeWhile1 f (x :: xs) = if f x then takeWhile f xs else unknownRange sh xs
takeWhile1 f []        = failEOI sh

||| A shifter that moves items while the give predicate returns
||| `False`
public export
takeUntil : (t -> Bool) -> AutoShift False t
takeUntil f (x :: xs) = if f x then Succ (x::xs) else takeUntil f xs
takeUntil f []        = Succ []

||| A strict version of `takeUntil`, which moves at least one item.
public export
takeUntil1 : (t -> Bool) -> AutoShift True t
takeUntil1 f (x :: xs) = if f x then unknownRange sh xs else takeUntil f xs
takeUntil1 f []        = failEOI sh

||| A shifter that moves digits.
public export
digits : AutoShift False Char
digits (x :: xs) = if isDigit x then digits xs else Succ (x::xs)
digits []        = Succ []

||| A strict version of `digits`.
public export
digits1 : AutoShift True Char
digits1 (x :: xs) = if isDigit x then digits xs else unknownRange sh xs
digits1 []        = failEOI sh

||| A shifter that moves an integer prefix
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

rest ('.'::x::xs) = if isDigit x then dot xs else unknown xs
rest ('.'::[])    = unknown []
rest xs           = exp xs

digs (x :: xs) = if isDigit x then digs xs else rest (x::xs)
digs []        = Succ []

||| A shifter for recognizing JSON numbers
public export
number : Shifter True Char
number sc ('-' :: '0' :: xs) = rest xs
number sc ('-' :: x   :: xs) = if isDigit x then digs xs else unknown xs
number sc (x          :: xs) = if isDigit x then digs xs else unknown xs
number sc []                 = failEmpty

public export
double : Tok Char Double
double cs = suffix (cast . cast {to = String}) $ number [<] cs

public export
take : (n : Nat) -> {auto 0 p : IsSucc n} -> AutoShift True t
take (S Z)       (x::xs)   = Succ xs
take (S k@(S _)) (x :: xs) = take {b} k xs
take (S k) []              = failEOI sh

public export
tail : AutoShift True t
tail (x::xs)   = Succ xs
tail []        = failEOI sh

public export
exact : Eq t => (ts : List t) -> {auto 0 p : NonEmpty ts} -> AutoShift True t
exact (v :: vs) (x :: xs) = case v == x of
  True => case vs of
    []         => Succ xs
    ws@(_::_) => exact {b} ws xs
  False => unknown xs
exact (v :: vs) []        = failEOI sh

str : AutoShift True Char
str ('"'       :: xs) = Succ xs
str ('\\' :: x :: xs) = str {b} xs
str (x         :: xs) = str {b} xs
str []                = failEOI sh

public export
string : Shifter True Char
string sc ('"' :: xs) = str {b = True} xs
string sc (h   :: t)  = unknown t
string sc []          = failEmpty
