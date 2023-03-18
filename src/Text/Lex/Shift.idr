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
     (b  : Bool)
  -> (sc : SnocList Char)
  -> (cs : List Char)
  -> Type where
  Succ :
       {0 b     : Bool}
    -> {0 st    : SnocList Char}
    -> {0 ts    : List Char}
    -> {pre     : SnocList Char}
    -> (post    : List Char)
    -> {auto sh : Shift b Char pre post st ts}
    -> ShiftRes b st ts

  Stop :
       {0 b         : Bool}
    -> {0 st,se,ee  : SnocList Char}
    -> {ts,errStart : List Char}
    -> (start       : Shift False Char se errStart st ts)
    -> (0 errEnd    : List Char)
    -> {auto end    : Shift False Char ee errEnd se errStart}
    -> ParseError Void Void
    -> ShiftRes b st ts

public export %inline
suffix : (SnocList Char -> a) -> ShiftRes True [<] cs -> LexRes True cs e a
suffix f (Succ {pre} post @{sh}) = Succ (f pre) post @{suffix sh} 
suffix f (Stop s e x @{sh})      = Fail (suffix s) e (fromVoid x) @{suffix sh}

--------------------------------------------------------------------------------
--         Conversions
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

public export
weaken : {0 x : _} -> ShiftRes x st ts -> ShiftRes False st ts
weaken (Succ xs @{p}) = Succ xs @{weaken p}
weaken (Stop s e r) = Stop s e r

public export
weakens : {0 x : _} -> ShiftRes True st ts -> ShiftRes x st ts
weakens (Succ xs @{p}) = Succ xs @{weakens p}
weakens (Stop s e r) = Stop s e r

public export
and1 : {0 x : _} -> ShiftRes x st ts -> ShiftRes (x && y) st ts
and1 (Succ xs @{p})= Succ xs @{and1 p}
and1 (Stop s e r)  = Stop s e r

public export %inline
and2 : {0 x : _} -> ShiftRes x st ts -> ShiftRes (y && x) st ts
and2 r = swapAnd $ and1 r

public export %inline
trans :
     {ys : _}
  -> ShiftRes b1 sx xs
  -> Shift b2 Char sx xs sy ys
  -> ShiftRes (b1 || b2) sy ys
trans (Succ ts @{p})    q = Succ ts @{Shift.trans p q}
trans (Stop x y z @{p}) q = Stop (weaken $ trans x q) y z

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) :
     ShiftRes b1 sx xs
  -> Lazy (ShiftRes b2 sx xs)
  -> ShiftRes (b1 && b2) sx xs
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
0 Shifter : (b : Bool) -> Type
Shifter b = (st : SnocList Char) -> (ts : List Char) -> ShiftRes b st ts

public export
0 AutoShift : Bool -> Type
AutoShift s =
     {0 b     : Bool}
  -> {0 giro  : SnocList Char}
  -> {orig    : List Char}
  -> {pre     : SnocList Char}
  -> (post    : List Char)
  -> {auto sh : Shift b Char pre post giro orig}
  -> ShiftRes (s || b) giro orig

public export
range :
     {0 b1,b2 : Bool}
  -> {0 giro,ruc,tser : SnocList Char}
  -> {orig,cur   : List Char}
  -> (err        : ParseError Void Void)
  -> (shiftCur   : Shift b1 Char ruc cur giro orig)
  -> (0 rest     : List Char)
  -> {auto sr    : Shift False Char tser rest ruc cur}
  -> ShiftRes b2 giro orig
range r sc rest = Stop (weaken sc) rest r

public export %inline
invalidEscape :
     {0 b1,b2 : Bool}
  -> {0 giro,ruc,tser : SnocList Char}
  -> {orig,cur   : List Char}
  -> (shiftCur   : Shift b1 Char ruc cur giro orig)
  -> (0 rest     : List Char)
  -> {auto sr    : Shift False Char tser rest ruc cur}
  -> ShiftRes b2 giro orig
invalidEscape = range InvalidEscape

public export %inline
unknownRange :
     {0 b1,b2 : Bool}
  -> {0 giro,ruc,tser : SnocList Char}
  -> {orig,cur   : List Char}
  -> (shiftCur   : Shift b1 Char ruc cur giro orig)
  -> (0 rest     : List Char)
  -> {auto sr    : Shift False Char tser rest ruc cur}
  -> ShiftRes b2 giro orig
unknownRange sc ee = range (Unknown . Left . packPrefix $ suffix sr) sc ee

public export %inline
single :
     {0 b,bres      : Bool}
  -> {0 giro,ruc    : SnocList Char}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (err           : ParseError Void Void)
  -> (shiftCur      : Shift b Char ruc (c::errEnd) giro orig)
  -> ShiftRes bres giro orig
single r p = range r p errEnd

public export %inline
unknown :
     {0 b,bres      : Bool}
  -> {0 giro,ruc    : SnocList Char}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (shiftCur      : Shift b Char ruc (c::errEnd) giro orig)
  -> ShiftRes bres giro orig
unknown p = unknownRange p errEnd

public export %inline
failCharClass :
     {0 b,bres      : Bool}
  -> {0 giro,ruc    : SnocList Char}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (class         : CharClass)
  -> (shiftCur      : Shift b Char ruc (c::errEnd) giro orig)
  -> ShiftRes bres giro orig
failCharClass cc = single (ExpectedChar cc)

public export %inline
failDigit :
     {0 b,bres      : Bool}
  -> {0 giro,ruc    : SnocList Char}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (tpe           : DigitType)
  -> (shiftCur      : Shift b Char ruc (c::errEnd) giro orig)
  -> ShiftRes bres giro orig
failDigit = failCharClass . Digit

public export
eoiAt :
     {0 b1,b2 : Bool}
  -> {0 ruc,giro : SnocList Char}
  -> {orig       : List Char}
  -> (shiftCur   : Shift b1 Char ruc [] giro orig)
  -> ShiftRes b2 giro orig
eoiAt sc = range EOI sc []

--------------------------------------------------------------------------------
--          General Purpose Shifters
--------------------------------------------------------------------------------

||| Shifter that recognises the empty String
public export
eoi : Shifter False
eoi _ []      = Succ []
eoi _ (x::xs) = single ExpectedEOI Same

||| Shifter that always fails
public export
fail : Shifter True
fail _ []      = eoiAt Same
fail _ (x::xs) = unknown Same

||| A shifter that moves exactly one value, if
||| it fulfills the given predicate.
public export
one : (Char -> Bool) -> AutoShift True
one f (x :: xs) = if f x then Succ xs else unknown sh
one _ []        = eoiAt sh

||| A shifter that moves items while the given predicate returns
||| `True`
public export
takeWhile : (Char -> Bool) -> AutoShift False
takeWhile f (x :: xs) = if f x then takeWhile f xs else Succ (x::xs)
takeWhile f []        = Succ []

||| A strict version of `takeWhile`, which moves at least one item.
public export
takeWhile1 : (Char -> Bool) -> AutoShift True
takeWhile1 f (x :: xs) = if f x then takeWhile f xs else unknown sh
takeWhile1 f []        = eoiAt sh

||| A shifter that moves items while the give predicate returns
||| `False`
public export
takeUntil : (Char -> Bool) -> AutoShift False
takeUntil f (x :: xs) = if f x then Succ (x::xs) else takeUntil f xs
takeUntil f []        = Succ []

||| A strict version of `takeUntil`, which moves at least one item.
public export
takeUntil1 : (Char -> Bool) -> AutoShift True
takeUntil1 f (x :: xs) = if f x then unknown sh else takeUntil f xs
takeUntil1 f []        = eoiAt sh

||| A shifter that moves digits.
public export
digits : AutoShift False
digits (x :: xs) = if isDigit x then digits xs else Succ (x::xs)
digits []        = Succ []

||| A strict version of `digits`.
public export
digits1 : AutoShift True
digits1 (x :: xs) = if isDigit x then digits xs else failDigit Dec sh
digits1 []        = eoiAt sh

||| A shifter that moves an integer prefix
public export
int : AutoShift True
int ('-' :: xs) = digits1 {b} xs
int xs          = digits1 {b} xs

||| Like `int` but also allows an optional leading `'+'` character.
public export
intPlus : AutoShift True
intPlus ('+' :: xs) = digits1 {b} xs
intPlus xs          = int {b} xs

dot,rest,digs,exp : AutoShift False
exp ('e' :: xs) = weakens $ intPlus {b} xs
exp ('E' :: xs) = weakens $ intPlus {b} xs
exp (x   :: xs) =
  if isDigit x then unknownRange Same xs else Succ (x::xs)
exp []          = Succ []

dot (x :: xs) = if isDigit x then dot xs else exp (x::xs)
dot []        = Succ []

rest ('.'::x::xs) =
  if isDigit x then dot xs else failDigit Dec (shift sh)
rest ('.'::[])    = eoiAt (shift sh)
rest xs           = exp xs

digs (x :: xs) = if isDigit x then digs xs else rest (x::xs)
digs []        = Succ []

||| A shifter for recognizing JSON numbers
public export
number : Shifter True
number sc ('-' :: '0' :: xs) = rest xs
number sc ('-' :: x   :: xs) =
  if isDigit x then digs xs else failDigit Dec (shift Same)
number sc ('0' :: xs)        = rest xs
number sc (x          :: xs) = if isDigit x then digs xs else unknown Same
number sc []                 = eoiAt Same

public export
double : Tok True e Double
double cs = suffix (cast . cast {to = String}) $ number [<] cs

public export
take : (n : Nat) -> {auto 0 p : IsSucc n} -> AutoShift True
take (S Z)       (x::xs)   = Succ xs
take (S k@(S _)) (x :: xs) = take {b} k xs
take (S k) []              = eoiAt sh

public export
tail : AutoShift True
tail (x::xs)   = Succ xs
tail []        = eoiAt sh

public export
exact : (ts : List Char) -> {auto 0 p : NonEmpty ts} -> AutoShift True
exact (v :: vs) (x :: xs) = case v == x of
  True => case vs of
    []        => Succ xs
    ws@(_::_) => exact {b} ws xs
  False => single (Expected . Left $ show v) sh
exact (v :: vs) []        = eoiAt sh

str : AutoShift True
str ('"'       :: xs) = Succ xs
str ('\\' :: x :: xs) = str {b} xs
str (x         :: xs) = str {b} xs
str []                = eoiAt sh

public export
string : Shifter True
string sc ('"' :: xs) = str {b = True} xs
string sc (h   :: t)  = single (Expected . Left $ show '"') Same
string sc []          = eoiAt Same
