module Data.List.Shift

import Data.Bool
import Data.List
import Data.List.Suffix
import Data.Nat
import Text.Lex.Bounded

%default total

||| Witness that a pair of a snoclist and a list
||| is the result of shifting values from the head of
||| an initial list to the tail of an initial snoclist.
|||
||| This data type is a witness for what a lexer does:
||| taking a finite number of elements from the head of a
||| list and appending them to the tail of a snoclist.
|||
||| By carrying around such a proof, we guarantee that no
||| character is lost during lexing, and that the order of
||| characters does not change during lexing.
|||
||| @ strict : `True` if at least one element was shifted
||| @ sx     : the current snoclist
||| @ xs     : the current list
||| @ giro   : the initial snoclist
||| @ orig   : the initial list
public export
data Shift :
     (strict : Bool)
  -> (sx     : SnocList a)
  -> (xs     : List a)
  -> (giro   : SnocList a)
  -> (orig   : List a)
  -> Type where
  [search strict xs giro orig]

  ||| Doing nothing results in a non-strict `Shift`
  Same : Shift False sx xs sx xs

  ||| We arrive at a new result by shifting one more value.
  SH   : Shift b1 sx (h :: t) sy ys -> Shift b2 (sx :< h) t sy ys

export %inline
sh : Shift b sx (h :: t) sx xs -> Shift True (sx :< h) t sx xs
sh = SH

public export
weaken : Shift b sx xs sy ys -> Shift False sx xs sy ys
weaken Same   = Same
weaken (SH x) = SH x

public export
weakens : Shift True sx xs sy ys -> Shift b sx xs sy ys
weakens (SH x) = SH x
weakens Same impossible

public export
suffix : Shift b sx xs sy ys -> Suffix b xs ys
suffix Same   = Same
suffix (SH x) = Uncons $ suffix x

public export %inline
toNat : Shift b sx xs sy ys -> Nat
toNat s = toNat $ suffix s

public export
and1 : Shift b1 sx xs sy ys -> Shift (b1 && b2) sx xs sy ys
and1 Same   = Same
and1 (SH x) = SH x

public export
and2 : Shift b2 sx xs sy ys -> Shift (b1 && b2) sx xs sy ys
and2 s = rewrite andCommutative b1 b2 in (and1 s)

public export
trans :
     Shift b1 sx xs sb bs
  -> Shift b2 sb bs sy cy
  -> Shift (b1 || b2) sx xs sy cy
trans Same y   = y
trans (SH x) y = SH $ trans x y

%transform "shiftTransPlus" Shift.trans x y = believe_me (toNat x + toNat y)

export
swapOr : Shift (b1 || b2) sx xs sy ys -> Shift (b2 || b1) sx xs sy ys
swapOr x = replace {p = \x => Shift x sx xs sy ys} orCommFD x

export
swapAnd : Shift (b1 && b2) sx xs sy ys -> Shift (b2 && b1) sx xs sy ys
swapAnd x = replace {p = \x => Shift x sx xs sy ys} andCommFD x

--------------------------------------------------------------------------------
--          Rec
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
data Rec :
     (strict : Bool)
  -> (st     : SnocList t)
  -> (ts     : List t)
  -> Type where

  Stop : Rec s st ts

  Res :  {0 st    : SnocList t}
      -> {0 ts    : List t}
      -> {pre     : SnocList t}
      -> (post    : List t)
      -> {auto sh : Shift b pre post st ts}
      -> Rec b st ts

public export
toSuffix : (SnocList t -> a) -> Rec {t} b st ts -> SuffixRes b t ts a
toSuffix f Stop                   = Fail
toSuffix f (Res {pre} post @{sh}) = Succ (f pre) post @{suffix sh}

namespace Rec
  public export
  weaken : Rec b sx xs -> Rec False sx xs
  weaken Stop             = Stop
  weaken (Res post @{sh}) = Res post @{weaken sh}

  public export
  weakens : Rec True sx xs -> Rec b sx xs
  weakens Stop             = Stop
  weakens (Res post @{sh}) = Res post @{weakens sh}

  export
  swapOr : Rec (b1 || b2) sx xs -> Rec (b2 || b1) sx xs
  swapOr x = replace {p = \x => Rec x sx xs} orCommFD x

  export
  swapAnd : Rec (b1 && b2) sx xs -> Rec (b2 && b1) sx xs
  swapAnd x = replace {p = \x => Rec x sx xs} andCommFD x

public export
(~>) : Rec s1 sx xs -> (p : Shift s2 sx xs sb bs) -> Rec (s1 || s2) sb bs
Res post @{q} ~> p = Res post @{trans q p}
Stop          ~> p = Stop

public export
(~?>) : Rec s1 sx xs -> (p : Shift s2 sx xs sb bs) -> Rec False sb bs
r ~?> p = weaken (r ~> p)

public export
(<|>) : Rec b1 sx xs -> Lazy (Rec b2 sx xs) -> Rec (b1 && b2) sx xs
Res post @{q} <|> _             = Res post @{and1 q}
Stop          <|> Res post @{q} = Res post @{and2 q}
Stop          <|> Stop          = Stop
 
--------------------------------------------------------------------------------
--          Shifters
--------------------------------------------------------------------------------

||| A `Shifter` is a function that moves items from the head of a list
||| to the tail of a snoclist.
|||
||| A lexer is just a fancy wrapper around a `Shifter`, and *running* a
||| lexer (via function `run`) leads to the underlying `Shifter`.
public export
0 Shifter : (b : Bool) -> Type -> Type
Shifter b t = (st : SnocList t) -> (ts : List t) -> Rec b st ts

||| Shifter that recognises the empty String
public export
eoi : Shifter False t
eoi _ [] = Res []
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
  -> Rec (s || b) giro orig

||| A shifter that doesn't move anything.
public export
same : AutoShift False a
same post = Res post

||| A shifter that moves exactly one value
public export
tail : AutoShift True a
tail (x :: xs) = Res xs
tail []        = Stop

||| A shifter that moves exactly one value, if
||| it fulfills the given predicate.
public export
one : (t -> Bool) -> AutoShift True t
one f (x :: xs) = if f x then Res xs else Stop
one _ []        = Stop

||| A shifter that moves items while the given predicate returns
||| `True`
public export
takeWhile : (a -> Bool) -> AutoShift False a
takeWhile f (x :: xs) = if f x then takeWhile f xs else Res (x::xs)
takeWhile f []        = Res []

||| A strict version of `takeWhile`, which moves at least one item.
public export
takeWhile1 : (a -> Bool) -> AutoShift True a
takeWhile1 f (x :: xs) = if f x then takeWhile f xs else Stop
takeWhile1 f []        = Stop

||| A shifter that moves items while the give predicate returns
||| `False`
public export
takeUntil : (t -> Bool) -> AutoShift False t
takeUntil f (x :: xs) = if f x then Res (x::xs) else takeUntil f xs
takeUntil f []        = Res []

||| A strict version of `takeUntil`, which moves at least one item.
public export
takeUntil1 : (t -> Bool) -> AutoShift True t
takeUntil1 f (x :: xs) = if f x then Stop else takeUntil f xs
takeUntil1 f []        = Stop

||| A shifter that moves digits.
public export
digits : AutoShift False Char
digits (x :: xs) = if isDigit x then digits xs else Res(x::xs)
digits []        = Res []

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
exp xs          = Res xs

dot (x :: xs) = if isDigit x then dot xs else exp (x::xs)
dot []        = Res []

rest ('.' :: x :: xs) = if isDigit x then dot xs else Stop
rest xs               = exp xs

digs (x :: xs) = if isDigit x then digs xs else rest (x::xs)
digs []        = Res []

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
take (S k) (x::xs) = rewrite sym (orTrueTrue _) in take k xs
take 0     xs      = Res xs
take (S k) []      = Stop

public export
exact : Eq t => List t -> AutoShift True t
exact (v :: []) (x :: xs) = if v == x then Res xs else Stop
exact (v :: vs) (x :: xs) = if v == x then exact {b} vs xs else Stop
exact _         _         = Stop

str : AutoShift True Char
str ('"'       :: xs) = Res xs
str ('\\' :: x :: xs) = str {b} xs
str (x         :: xs) = str {b} xs
str []                = Stop

public export
string : AutoShift True Char
string ('"' :: xs) = str {b} xs
string _           = Stop
